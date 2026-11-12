#!/usr/bin/env python3
"""Fail if a README link points at a heading or a file that does not exist.

`README.md` is the crate's page on crates.io, and it is the only document with a
hand-written table of contents. A heading gets renamed, the entry in the contents
list keeps pointing at the old anchor, and nothing notices: Markdown has no link
checker, `cargo doc` never sees the README, and a dead anchor renders as ordinary
text rather than an error. The same is true of a relative link such as
`[CONTRIBUTING.md](CONTRIBUTING.md)` once the file moves.

So the anchors are checked the way the rest of this repository checks its claims:
by a script, not by remembering to look. Only *internal* targets are resolved --
an `http(s)://` link is left alone, because a network check would fail for
reasons that have nothing to do with this repository and a CI job that reaches
out to the internet is a job that fails when the internet is slow.

The GitHub anchor rule is reproduced rather than approximated: lowercase the
heading, drop every character that is not a letter, a digit, a space, an
underscore or a hyphen, then turn each space into a hyphen. Duplicate headings
get `-1`, `-2`, ... suffixes in document order, which is what GitHub does.

Usage: python3 scripts/check_doc_links.py [markdown ...]
With no arguments it checks `README.md` at the repository root.
"""

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# An inline link: the target is everything up to the closing paren. A target may
# carry a title (`](path "Title")`), which is not part of the path.
LINK = re.compile(r"\]\(([^)\s]+)(?:\s+\"[^\"]*\")?\)")
HEADING = re.compile(r"^(#{1,6})\s+(.*?)\s*$")
FENCE = re.compile(r"^\s*(```|~~~)")


def anchor_of(heading: str) -> str:
    """The GitHub anchor for a heading, before duplicate disambiguation."""
    text = heading.lower()
    text = re.sub(r"[^a-z0-9 _-]", "", text)
    return text.strip().replace(" ", "-")


def anchors(text: str) -> set[str]:
    """Every anchor a reader can reach in this document."""
    seen: dict[str, int] = {}
    out: set[str] = set()
    in_fence = False
    for line in text.splitlines():
        # A `#` inside a fenced block is code, not a heading.
        if FENCE.match(line):
            in_fence = not in_fence
            continue
        if in_fence:
            continue
        m = HEADING.match(line)
        if not m:
            continue
        base = anchor_of(m.group(2))
        n = seen.get(base, 0)
        seen[base] = n + 1
        out.add(base if n == 0 else f"{base}-{n}")
    return out


def check(path: Path) -> list[str]:
    text = path.read_text(encoding="utf-8")
    have = anchors(text)
    errors: list[str] = []

    in_fence = False
    for lineno, line in enumerate(text.splitlines(), 1):
        if FENCE.match(line):
            in_fence = not in_fence
            continue
        if in_fence:
            continue
        for target in LINK.findall(line):
            if target.startswith("#"):
                frag = target[1:]
                if frag and frag not in have:
                    errors.append(
                        f"{path}:{lineno}: no heading matches anchor '#{frag}'"
                    )
            elif "://" in target or target.startswith(("mailto:", "tel:")):
                continue  # an external link; not this repository's to resolve
            else:
                rel = target.split("#", 1)[0]
                if rel and not (path.parent / rel).exists():
                    errors.append(
                        f"{path}:{lineno}: link target '{rel}' does not exist"
                    )
    return errors


def main(argv: list[str]) -> int:
    paths = [Path(a) for a in argv[1:]] or [ROOT / "README.md"]
    problems: list[str] = []
    for p in paths:
        if not p.exists():
            problems.append(f"{p}: file to check does not exist")
            continue
        problems.extend(check(p))
    if problems:
        print("check_doc_links: broken links", file=sys.stderr)
        for e in problems:
            print(f"  {e}", file=sys.stderr)
        return 1
    total = ", ".join(str(p) for p in paths)
    print(f"documentation links resolve ({total})")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
