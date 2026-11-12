#!/usr/bin/env python3
"""Fail if a GitHub Action is referenced by a mutable ref instead of a commit.

The cipansor organisation requires every action to be pinned to a full-length
commit SHA. A tag or branch such as `@v4` is mutable: whoever controls the
upstream repository can move it, and the next workflow run then executes code
that nobody reviewed. That is the whole class of supply-chain attack this
prevents, and it is invisible in review because `@v4` reads as a version.

Accepted forms:

    uses: actions/checkout@11d5960a326750d5838078e36cf38b85af677262 # v4
    uses: ./local/action
    uses: docker://alpine@sha256:<64 hex>

The trailing `# v4` comment is the point: the SHA is unreadable, so the tag is
kept beside it for humans. The comment is not what is checked.

Usage: python3 scripts/check_actions_pinned.py [workflow ...]
With no arguments it scans .github/workflows and .github/actions.
"""

import re
import sys
from pathlib import Path

# `- uses: value` at the start of a line, capturing the value up to a comment.
USES = re.compile(r"^\s*(?:-\s*)?uses:\s*(?P<value>[^#\s]+)")

SHA = re.compile(r"^[0-9a-f]{40}$")
DOCKER_DIGEST = re.compile(r"^docker://.+\@sha256:[0-9a-f]{64}$")


def check_line(value: str) -> str | None:
    """Return an error message, or None when the reference is acceptably pinned."""
    if value.startswith("./"):
        return None  # a local action; there is no remote ref to pin
    if value.startswith("docker://"):
        if DOCKER_DIGEST.match(value):
            return None
        return f"{value!r} is not pinned by digest (expected docker://image@sha256:<64 hex>)"
    if "@" not in value:
        return f"{value!r} has no ref at all; pin it to a full-length commit SHA"
    repo, ref = value.rsplit("@", 1)
    if SHA.match(ref):
        return None
    return (
        f"{value!r} uses the mutable ref {ref!r}; pin it to the full-length "
        f"commit SHA that {ref} resolves to, keeping {ref} in a trailing comment"
    )


def files(root: Path, given: list[str]) -> list[Path]:
    if given:
        return [Path(p) for p in given]
    found = sorted(root.glob(".github/workflows/*.y*ml"))
    found += sorted(root.glob(".github/actions/*/action.y*ml"))
    return found


def main(argv: list[str]) -> int:
    root = Path(__file__).resolve().parent.parent
    targets = files(root, argv)
    if not targets:
        print("actions: no workflow files found", file=sys.stderr)
        return 0

    failures = []
    for path in targets:
        for number, line in enumerate(path.read_text().splitlines(), 1):
            m = USES.match(line)
            if not m:
                continue
            error = check_line(m.group("value"))
            if error:
                failures.append((path, number, error))

    for path, number, error in failures:
        try:
            shown = path.relative_to(root)
        except ValueError:
            shown = path
        print(f"{shown}:{number}: {error}", file=sys.stderr)

    if failures:
        print(
            f"\n{len(failures)} action reference(s) are not pinned to a commit SHA. "
            "The cipansor org rejects unpinned actions at workflow start.",
            file=sys.stderr,
        )
        return 1

    print(f"actions: {len(targets)} file(s) checked, every action pinned to a commit SHA")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
