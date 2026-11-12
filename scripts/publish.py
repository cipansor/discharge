#!/usr/bin/env python3
"""Check, and optionally run, the publishing sequence for this repository.

`cargo publish` resolves a `path` dependency against the registry, so `verif`
cannot be packaged until `verif-arithmetic` is on crates.io. Publishing in the
wrong order fails in one of two ways, depending on whether the dependency has
ever been published:

    no matching package named `verif-arithmetic` found

on a first release, and, once an older version is on the registry,

    failed to select a version for the requirement `verif-arithmetic = "^0.1.0"`
    candidate versions found which didn't match: 0.1.0

which reads like a broken manifest but is only the order. Both are detected and
reported as waiting on a dependency. This script derives the order from the
manifests themselves, so it cannot go stale the way a hand-written list does.

By default it only checks: `cargo publish --dry-run` for every crate, in order,
stopping at nothing, reporting which are ready and which are waiting on a
dependency. It uploads nothing. Pass --publish to upload for real; that path
stops at the first failure, because a published version cannot be overwritten and
there is no point continuing past a broken crate.

Usage:
    python3 scripts/publish.py                     # check every crate
    python3 scripts/publish.py --strict            # check, and fail if any is blocked
    python3 scripts/publish.py --crate verif       # check one crate
    python3 scripts/publish.py --tag verif-v0.1.0  # the crate a release tag names
    python3 scripts/publish.py --publish           # upload, in order, stop on error
    python3 scripts/publish.py --publish --yes     # same, no confirmation prompt

Releases are per crate, because the crates version independently: a tag is
`<crate>-v<version>` and publishes exactly that crate. There is deliberately no
bare `v<version>` tag - one tag cannot describe both crates here, which may sit
at different versions. `crates_from_tag` refuses it.

Exit code is 0 when nothing is wrong: a crate waiting on an unpublished
dependency is the expected pre-publish state, not an error. Pass --strict to make
it one, which is the check to run after publishing a dependency.
"""

import argparse
import re
import subprocess
import sys
import time
import tomllib
import urllib.error
import urllib.request
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# Every crate that is published, with the directory it lives in. The parent crate
# is at the repository root; the sibling is a subdirectory. `tools/mir-oracle` is
# deliberately absent: it links `rustc_private`, is an excluded workspace member,
# and is never published.
CRATES = {
    "verif": ROOT,
    "verif-arithmetic": ROOT / "verif-arithmetic",
}

# A release tag names one crate and one version: `verif-v0.1.0`.
TAG_PATTERN = re.compile(r"^(?P<crate>[A-Za-z0-9_-]+)-v(?P<version>[0-9][^/]*)$")

# A bare version tag: `v` immediately followed by a digit. Matched as a prefix so
# that `v0.1.0` is refused while `verif-v0.1.0` (which also starts with `v`) is
# not. See `crates_from_tag`.
BARE_VERSION = re.compile(r"^v[0-9]")


class ReleaseError(Exception):
    """A request that cannot be carried out: a bad tag, or an unknown crate."""


def crates_from_tag(tag: str) -> tuple[str, str]:
    """Return (crate, version) named by a `<crate>-v<version>` release tag.

    A bare `v<version>` tag is refused rather than interpreted. It would be
    ambiguous - it cannot say which crate it means, and treating it as "both of
    them" is exactly the behaviour that publishes a crate nobody asked for.
    Failing loudly is the only safe reading.

    "Bare" is matched as `v` immediately followed by a digit, not as a leading
    `v`: a crate in this repository is named `verif`, so `verif-v0.1.0` starts
    with `v` and is a perfectly good tag. The digit is what makes `v0.1.0` a
    version and `verif-...` a crate name.
    """
    if BARE_VERSION.match(tag):
        raise ReleaseError(
            f"`{tag}` is a bare version tag, which this repository does not use. "
            "The crates version independently, so a release is named per crate: "
            "`<crate>-v<version>`, for example `verif-v0.1.0`."
        )
    match = TAG_PATTERN.match(tag)
    if not match:
        raise ReleaseError(
            f"`{tag}` is not a release tag. Name the crate and the version: "
            "`<crate>-v<version>`, for example `verif-v0.1.0`."
        )
    return match.group("crate"), match.group("version")


# "no matching package named `verif-arithmetic` found"
MISSING_DEP = re.compile(r"no matching package named `([^`]+)` found")

# The same "not published yet" condition from the other side: the dependency
# exists on crates.io at an older version, so cargo fails to select a version
# instead of failing to find the package. This is the shape a release takes from
# the second release onward.
UNRESOLVED_DEP = re.compile(
    r"failed to select a version for the requirement `([A-Za-z0-9_-]+)"
)

# crates.io rate limits how many NEW crates an account may publish in a short
# window, and a second run of the same version is refused outright. Cargo
# surfaces both as a plain non-zero exit, so they are detected here.
RATE_LIMITED = re.compile(r"429|too many requests|rate limit", re.IGNORECASE)
RETRY_AFTER = re.compile(
    r"try again after (\w{3}, \d{2} \w{3} \d{4} \d{2}:\d{2}:\d{2} GMT)"
)
ALREADY_PUBLISHED = re.compile(r"already exists on crates\.io")
RATE_LIMIT_FALLBACK = 70  # seconds, used only when the 429 carries no timestamp


def rate_limit_wait(output: str) -> float:
    """Seconds to wait before retrying a rate-limited upload.

    Reads the retry time out of the 429 when it is there, because the new-crate
    window is minutes long and a fixed short backoff cannot clear it.
    """
    match = RETRY_AFTER.search(output)
    if not match:
        return float(RATE_LIMIT_FALLBACK)
    try:
        when = datetime.strptime(match.group(1), "%a, %d %b %Y %H:%M:%S GMT")
    except ValueError:
        return float(RATE_LIMIT_FALLBACK)
    return max(65.0, when.replace(tzinfo=timezone.utc).timestamp() - time.time() + 5)


def load_manifests() -> tuple[dict[str, dict], dict[str, list[str]]]:
    """Return (name -> manifest, name -> its in-repo dependencies)."""
    manifests: dict[str, dict] = {}
    for name, directory in CRATES.items():
        parsed = tomllib.loads((directory / "Cargo.toml").read_text())
        if parsed["package"]["name"] != name:
            raise ReleaseError(
                f"{directory}/Cargo.toml names {parsed['package']['name']!r}, "
                f"expected {name!r}"
            )
        manifests[name] = parsed

    deps: dict[str, list[str]] = {}
    for name, parsed in manifests.items():
        deps[name] = [
            dep for dep in parsed.get("dependencies", {}) if dep in CRATES
        ]
    return manifests, deps


def version_of(manifest: dict) -> str:
    """The version a manifest declares."""
    return manifest["package"]["version"]


def topo_order(crates: list[str], deps: dict[str, list[str]]) -> list[str]:
    """Order crates so every crate follows the ones it depends on."""
    within = set(crates)
    ordered: list[str] = []
    placed: set[str] = set()
    while len(ordered) < len(crates):
        progressed = False
        for crate in crates:
            if crate in placed:
                continue
            if all(dep in placed for dep in deps[crate] if dep in within):
                ordered.append(crate)
                placed.add(crate)
                progressed = True
        if not progressed:
            raise SystemExit(f"dependency cycle among: {sorted(set(crates) - placed)}")
    return ordered


def dirty_by_crate(crates: list[str]) -> dict[str, list[str]]:
    """Attribute each dirty file to the crate whose directory contains it."""
    result = subprocess.run(
        ["git", "status", "--porcelain"], cwd=ROOT, capture_output=True, text=True
    )
    blocked: dict[str, list[str]] = {}
    for line in result.stdout.splitlines():
        if not line.strip():
            continue
        path = line[3:].strip().strip('"')
        for crate in crates:
            directory = CRATES[crate]
            prefix = "" if directory == ROOT else f"{directory.relative_to(ROOT)}/"
            if prefix and path.startswith(prefix):
                blocked.setdefault(crate, []).append(path)
    return blocked


def notes_for(tag: str) -> str:
    """Release notes for the crate a tag names, from the commits that touched it.

    Scoped to one crate's files, so a release for one crate does not list the
    other's commits. The parent crate owns the repository root, so its pathspec is
    "everything except the sibling and the tools" rather than a directory; the
    sibling owns exactly its own directory. A plain list of directories would put
    every sibling commit into the parent's notes.

    The range starts at this crate's previous tag, so the notes cover what changed
    since the last release of *this* crate, not since the last release of any.
    """
    crate, version = crates_from_tag(tag)

    if CRATES[crate] == ROOT:
        paths = [".", ":(exclude)verif-arithmetic", ":(exclude)tools"]
    else:
        paths = [str(CRATES[crate].relative_to(ROOT))]

    previous = subprocess.run(
        ["git", "tag", "--list", f"{crate}-v*", "--sort=-v:refname"],
        cwd=ROOT, capture_output=True, text=True, check=True,
    ).stdout.split()
    previous = [t for t in previous if t != tag]
    rev = f"{previous[0]}..HEAD" if previous else "HEAD"

    log = subprocess.run(
        ["git", "log", "--no-merges", "--format=- %s", rev, "--", *paths],
        cwd=ROOT, capture_output=True, text=True, check=True,
    ).stdout.strip()

    header = f"# {crate} {version}\n\n## Changes\n\n"
    return header + (log if log else "- (no commits touched this crate)") + "\n"


def verify_checkout(tag: str) -> tuple[bool, str]:
    """Check that HEAD is the commit the tag points at.

    A manual dispatch can select any ref in the Actions UI, and the tag input only
    controls what is *named*: if the selected branch happens to carry the same
    version, the manifest check passes and the branch's contents are published
    under the tag, while the GitHub release is created against the tag's commit.
    Two commits, one release, and the registry holds the one nobody tagged.

    The version check cannot catch that, because both commits declare the same
    version. Comparing the commit can.
    """
    head = subprocess.run(
        ["git", "rev-parse", "HEAD"], cwd=ROOT, capture_output=True, text=True
    )
    if head.returncode != 0:
        return False, "cannot read HEAD"
    tagged = subprocess.run(
        ["git", "rev-list", "-n", "1", tag], cwd=ROOT, capture_output=True, text=True
    )
    if tagged.returncode != 0:
        return False, f"tag `{tag}` does not exist in this checkout"
    if head.stdout.strip() != tagged.stdout.strip():
        return False, (
            f"HEAD is {head.stdout.strip()[:12]} but `{tag}` is "
            f"{tagged.stdout.strip()[:12]}; check out the tag, not a branch"
        )
    return True, tagged.stdout.strip()[:12]


def confirm_index(crate: str, version: str, timeout: float, interval: float) -> tuple[bool, str]:
    """Wait, briefly, for a published version to appear in the crates.io index.

    A successful upload and an API-visible version are separate events: the index
    is updated asynchronously, so an immediate request can 404 for a few seconds
    after `cargo publish` returned success. Treating that first 404 as a failure
    aborts a workflow whose crate *is* published -- leaving the release half-done,
    with the upload done and the GitHub release never created.

    So a 404 is retried, not fatal. A network error is retried too. Any other HTTP
    error is not: a 403 or a 400 will not become a 200 by waiting, and retrying it
    only delays the report.
    """
    url = f"https://crates.io/api/v1/crates/{crate}/{version}"
    deadline = time.time() + timeout
    attempt = 0
    while True:
        attempt += 1
        try:
            code = urllib.request.urlopen(url, timeout=30).status
        except urllib.error.HTTPError as error:
            code = error.code
        except (urllib.error.URLError, OSError) as error:
            code = None
            detail = str(error)

        if code == 200:
            return True, f"HTTP 200 after {attempt} request(s)"
        if code is not None and code != 404 and code < 500:
            return False, f"HTTP {code} is not a temporary condition"

        if time.time() >= deadline:
            seen = f"HTTP {code}" if code is not None else f"no response ({detail})"
            return False, f"still not in the index after {timeout:.0f}s ({seen})"

        time.sleep(interval)


def run_publish(crate: str, dry_run: bool) -> tuple[str, str]:
    """Return (verdict, detail).

    Verdict is 'ready', 'blocked' (a dependency is unpublished) or 'failed'.
    """
    command = ["cargo", "publish", "-p", crate]
    if dry_run:
        command.append("--dry-run")
    result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True)
    output = result.stdout + result.stderr

    if result.returncode == 0:
        return "ready", ""

    # A dependency inside this repository that is not on the registry yet is the
    # expected pre-publish state, not a broken crate. Only a name that really is
    # a crate here counts; a version conflict on a third-party crate is a failure.
    for pattern in (MISSING_DEP, UNRESOLVED_DEP):
        match = pattern.search(output)
        if match and match.group(1) in CRATES:
            return "blocked", match.group(1)

    if RATE_LIMITED.search(output):
        return "rate-limited", ""
    if ALREADY_PUBLISHED.search(output):
        return "published", ""

    if "not yet committed into git" in output or "--allow-dirty" in output:
        paths = [
            line.strip()
            for line in output.splitlines()
            if line.strip().startswith("crates/")
            or line.strip().startswith("src/")
            or line.strip().endswith(".rs")
            or line.strip().endswith(".md")
            or line.strip().endswith(".toml")
        ]
        return "dirty", paths[0] if paths else "uncommitted files"

    detail = ""
    for line in output.splitlines():
        if line.strip().startswith("error") or line.strip().startswith("Caused by"):
            detail = line.strip()
            break
    return "failed", detail or output.strip().splitlines()[-1] if output.strip() else ""


def check_one(crate: str, dirty: dict[str, list[str]], order_index: int) -> tuple[str, str]:
    verdict, detail = run_publish(crate, dry_run=True)
    if verdict == "ready" and crate in dirty:
        files = dirty[crate]
        return "dirty", f"{len(files)} uncommitted file(s), e.g. {files[0]}"
    return verdict, detail


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--publish", action="store_true", help="upload for real")
    parser.add_argument("--yes", action="store_true", help="skip the confirmation")
    parser.add_argument("--strict", action="store_true", help="fail if any crate is blocked")
    parser.add_argument("--crate", help="check only this crate")
    parser.add_argument("--tag", help="release the crate this tag names")
    parser.add_argument(
        "--check-tag",
        action="store_true",
        help="validate --tag and exit without packaging anything",
    )
    parser.add_argument(
        "--verify-checkout",
        action="store_true",
        help="assert HEAD is the commit --tag points at, then exit",
    )
    parser.add_argument(
        "--notes",
        action="store_true",
        help="print the release notes for --tag on stdout, then exit",
    )
    parser.add_argument(
        "--confirm-index",
        action="store_true",
        help="wait for --tag's version to appear in the crates.io index, then exit",
    )
    parser.add_argument(
        "--index-timeout",
        type=float,
        default=300.0,
        help="seconds to wait for the index (default 300)",
    )
    parser.add_argument(
        "--index-interval",
        type=float,
        default=10.0,
        help="seconds between index requests (default 10)",
    )
    args = parser.parse_args(argv)

    try:
        manifests, deps = load_manifests()
        crates = list(CRATES)

        if args.tag:
            crate, tag_version = crates_from_tag(args.tag)
            if crate not in CRATES:
                raise ReleaseError(
                    f"`{args.tag}` names `{crate}`, which is not a crate here. "
                    f"Known: {', '.join(sorted(CRATES))}"
                )
            declared = version_of(manifests[crate])
            if declared != tag_version:
                raise ReleaseError(
                    f"`{args.tag}` says {crate} is {tag_version}, but its manifest "
                    f"says {declared}. Update the manifest, or move the tag."
                )
            crates = [crate]
        elif args.crate:
            if args.crate not in CRATES:
                raise ReleaseError(
                    f"`{args.crate}` is not a crate here. "
                    f"Known: {', '.join(sorted(CRATES))}"
                )
            crates = [args.crate]
    except ReleaseError as error:
        print(f"error: {error}", file=sys.stderr)
        return 1

    if args.check_tag:
        if not args.tag:
            print("error: --check-tag needs --tag", file=sys.stderr)
            return 1
        crate, version = crates_from_tag(args.tag)
        print(f"tag {args.tag} names {crate} {version}, which matches its manifest")
        return 0

    # The three release subcommands. Each is a separate mode rather than a flag on
    # the check run, because the workflow needs to run them at different points --
    # the checkout check before anything is installed, the notes before the
    # upload, the index confirmation after it -- and a mode that does one thing is
    # the one that can be tested on its own.
    if args.verify_checkout or args.notes or args.confirm_index:
        if not args.tag:
            print(
                "error: --verify-checkout, --notes and --confirm-index need --tag",
                file=sys.stderr,
            )
            return 1
        try:
            crate, version = crates_from_tag(args.tag)
        except ReleaseError as error:
            print(f"error: {error}", file=sys.stderr)
            return 1

        if args.verify_checkout:
            ok, detail = verify_checkout(args.tag)
            if not ok:
                print(f"error: {detail}", file=sys.stderr)
                return 1
            print(f"checkout: HEAD is `{args.tag}` at {detail}")
            return 0

        if args.notes:
            sys.stdout.write(notes_for(args.tag))
            return 0

        ok, detail = confirm_index(
            crate, version, args.index_timeout, args.index_interval
        )
        print(f"{crate} {version}: {detail}")
        if not ok:
            print(
                f"error: {crate} {version} did not appear in the crates.io index",
                file=sys.stderr,
            )
            return 1
        return 0

    order = topo_order(list(CRATES), deps)
    selected = [c for c in order if c in crates]
    dirty = dirty_by_crate(list(CRATES))

    mode = "publish" if args.publish else "check"
    print(f"publish {mode}: {', '.join(selected)} (in dependency order)\n")

    if args.publish and not args.yes:
        print("About to upload, which cannot be undone:")
        for crate in selected:
            print(f"  {crate} {version_of(manifests[crate])}")
        answer = input("Type 'yes' to continue: ").strip()
        if answer != "yes":
            print("aborted")
            return 1

    blocked = 0
    failed = 0
    for index, crate in enumerate(selected, 1):
        version = version_of(manifests[crate])
        if args.publish:
            verdict, detail = run_publish(crate, dry_run=False)
            while verdict == "rate-limited":
                wait = rate_limit_wait(detail)
                print(f"{index}. {crate} {version}: rate limited; waiting {wait:.0f}s")
                time.sleep(wait)
                verdict, detail = run_publish(crate, dry_run=False)
        else:
            verdict, detail = check_one(crate, dirty, index)

        if verdict == "ready":
            print(f"{index}. {crate} {version}: ready")
        elif verdict == "published":
            print(f"{index}. {crate} {version}: already on crates.io, skipped")
        elif verdict == "blocked":
            print(f"{index}. {crate} {version}: blocked, waiting on `{detail}`")
            blocked += 1
            if args.publish:
                print("   stopping: a published version cannot be overwritten")
                return 1
        elif verdict == "dirty":
            print(f"{index}. {crate} {version}: uncommitted files ({detail})")
            failed += 1
            if args.publish:
                return 1
        else:
            print(f"{index}. {crate} {version}: FAILED: {detail}")
            failed += 1
            if args.publish:
                return 1

    print()
    if blocked:
        print(f"{blocked} crate(s) blocked on an unpublished dependency.")
        if args.strict:
            return 1
    if failed:
        print(f"{failed} crate(s) failed.")
        return 1
    if not blocked:
        print("all selected crates are ready to publish.")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
