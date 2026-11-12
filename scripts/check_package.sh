#!/bin/sh
# Packaging hygiene: the things a `.crate` needs that no compiler checks.
#
# A crate can build, test and lint perfectly and still be a bad citizen on
# crates.io: a manifest missing `readme` renders no README on the crate page, a
# directory with no `LICENSE` ships a `.crate` that cannot be redistributed
# legally, a stray `target/` bloats the download, and a project credited in the
# code but absent from `NOTICE` is an attribution bug. None of those fail a
# build. This script is the check, and it is hermetic: it reads manifests and
# the file list, and runs no compiler, so it is cheap enough to run on every
# pull request.
#
# Usage: sh scripts/check_package.sh
set -u

root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$root" || exit 1

fail=0
note() { printf '   %s\n' "$1"; }
bad() { printf 'FAIL %s\n' "$1" >&2; fail=1; }

python3 - "$root" <<'PY' || fail=1
import re
import sys
import tomllib
from pathlib import Path

root = Path(sys.argv[1])

# Every crate that is meant to be published, with the directory it lives in.
CRATES = {
    "verif": root,
    "verif-arithmetic": root / "verif-arithmetic",
}

# A crates.io listing without these is a listing a user cannot evaluate. The
# first four are what cargo itself warns about; `rust-version` and `readme` are
# the two the reference crates in this organisation always set.
REQUIRED = [
    "description",
    "license",
    "repository",
    "keywords",
    "categories",
    "rust-version",
    "readme",
]

# The files a `.crate` should carry so a recipient can use and redistribute it.
NEEDED_FILES = ["LICENSE", "README.md", "NOTICE"]

problems = []

for name, directory in CRATES.items():
    manifest = directory / "Cargo.toml"
    if not manifest.is_file():
        problems.append(f"{name}: no Cargo.toml at {manifest}")
        continue
    parsed = tomllib.loads(manifest.read_text())
    package = parsed.get("package", {})

    if package.get("name") != name:
        problems.append(
            f"{name}: manifest names {package.get('name')!r}, expected {name!r}"
        )

    for field in REQUIRED:
        if not package.get(field):
            problems.append(f"{name}: Cargo.toml has no `{field}`")

    for filename in NEEDED_FILES:
        if not (directory / filename).is_file():
            problems.append(
                f"{name}: {filename} is missing from {directory}; "
                f"the published .crate would not carry it"
            )

    # `documentation` should point at docs.rs for this crate, not at the repo:
    # the field exists to tell a reader where the API docs are.
    documentation = package.get("documentation", "")
    if documentation and documentation != f"https://docs.rs/{name}":
        problems.append(
            f"{name}: documentation is {documentation!r}, expected "
            f"'https://docs.rs/{name}'"
        )

    # docs.rs builds with default features unless told otherwise. A crate whose
    # default build leaves a feature out would publish docs missing that whole
    # surface -- for `verif` that is the `std`-only MIR frontend. A crate with
    # nothing but the default has no flag to set, and adding a no-op one would
    # be exactly the "flag with no reader" this repository argues against, so
    # the requirement is only for a crate that has a non-default feature.
    features = parsed.get("features", {})
    default = set(features.get("default", []))
    extra = {f for f in features if f != "default"} - default
    has_docs_rs = "rs" in parsed.get("package", {}).get("metadata", {}).get("docs", {})
    if extra and not has_docs_rs:
        problems.append(
            f"{name}: has non-default feature(s) {sorted(extra)} but no "
            f"[package.metadata.docs.rs]; docs.rs would build only the default "
            f"features and omit them"
        )


# The attribution rule: a third-party project named in a crate's source must be
# named in that crate's NOTICE. The list is small and fixed on purpose -- a
# project that appears here is one the crate's own documentation compares itself
# to or runs as an oracle, and each is a name a reader should be able to look up.
#
# The check is per crate, not global: a project named only in `verif`'s source is
# `verif`'s to attribute, and requiring the sibling to name it too would make the
# rule noisier than the thing it protects.
ATTRIBUTED = {
    "SPARK": "SPARK",
    "gnatprove": "SPARK",
    "AdaCore": "SPARK",
    "Z3": "Z3",
    "Kani": "Kani",
    "Verus": "Verus",
    "Prusti": "Prusti",
    "MIRAI": "MIRAI",
    "Lean": "Lean",
    "Coq": "Coq",
    "CBMC": "CBMC",
    "Ferrocene": "Ferrocene",
    "rustc_public": "rustc_public",
}

per_crate_sources = {
    "verif": [root / "src"],
    "verif-arithmetic": [root / "verif-arithmetic" / "src"],
}

attributed_total = 0
for name, sources in per_crate_sources.items():
    seen = set()
    for source in sources:
        for path in source.rglob("*.rs"):
            text = path.read_text(errors="replace")
            for needle, key in ATTRIBUTED.items():
                if re.search(rf"\b{re.escape(needle)}\b", text):
                    seen.add(key)
    attributed_total += len(seen)

    notice = CRATES[name] / "NOTICE"
    if not notice.is_file():
        continue
    text = notice.read_text()
    for key in sorted(seen):
        if key not in text:
            problems.append(
                f"{notice.relative_to(root)}: {key!r} is named in {name}'s source "
                f"but not attributed in this NOTICE"
            )

if problems:
    for problem in problems:
        print(f"  {problem}", file=sys.stderr)
    print(
        f"\n{len(problems)} packaging problem(s). These do not fail a build, "
        "which is why this check exists.",
        file=sys.stderr,
    )
    raise SystemExit(1)

print(f"package: {len(CRATES)} manifest(s) complete, "
      f"LICENSE/README/NOTICE present, attribution covers {attributed_total} project(s)")
PY

# No compiled artifact may be tracked. Gate 16 of scripts/gate.sh checks this
# too, but this script is the one a contributor runs on its own, and the check is
# two lines. `.gitignore` cannot help a file that is already tracked.
if command -v git >/dev/null 2>&1 && git rev-parse --is-inside-work-tree >/dev/null 2>&1; then
  artifacts=$(git ls-files | grep -E '(^|/)(target/|\.sweep/)|\.rlib$|\.rmeta$|\.d$|\.o$|\.bc$|__pycache__' || true)
  if [ -n "$artifacts" ]; then
    printf '%s\n' "$artifacts" >&2
    bad "build artifacts are tracked"
  fi
fi

if [ "$fail" -eq 0 ]; then
  echo "package: ok"
fi
exit "$fail"
