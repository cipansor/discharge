#!/usr/bin/env python3
"""Fail if a documentation link points at a heading or a file that does not exist.

`README.md` is the crate's page on crates.io, and it is the only document with a
hand-written table of contents. A heading gets renamed, the entry in the contents
list keeps pointing at the old anchor, and nothing notices: Markdown has no link
checker, `cargo doc` never sees the README, and a dead anchor renders as ordinary
text rather than an error. The same is true of a relative link such as
`[CONTRIBUTING.md](CONTRIBUTING.md)` once the file moves.

A fragment is resolved in the document that owns it, which is not always this
one: `[Ground rules](CONTRIBUTING.md#where-a-rule-lives)` names a heading in
`CONTRIBUTING.md`, and checking only that the file exists would accept the link
after that heading was renamed. Non-Markdown targets have no headings, so for
those the existence check is the whole check.

So the anchors are checked the way the rest of this repository checks its claims:
by a script, not by remembering to look. Only *internal* targets are resolved --
an `http(s)://` link is left alone, because a network check would fail for
reasons that have nothing to do with this repository and a CI job that reaches
out to the internet is a job that fails when the internet is slow. Fenced code
blocks and inline code spans are skipped for the same reason: a link inside one
is an example, and it renders as code rather than as something to click.

The GitHub anchor rule is reproduced rather than approximated: lowercase the
heading, drop every character that is not a letter, a digit, a space, an
underscore or a hyphen, then turn each space into a hyphen. Duplicate headings
get `-1`, `-2`, ... suffixes in document order, which is what GitHub does.

Usage: python3 scripts/check_doc_links.py [markdown ...]
With no arguments it checks every top-level `*.md`, README first.
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


# Markdown targets are parsed for their headings; anything else (a `.rs`, a
# `.toml`) has no anchors to resolve, so only its existence can be checked.
MARKDOWN = (".md", ".markdown")


def strip_inline_code(line: str) -> str:
    """Drop `` `...` `` spans from a line.

    A link inside an inline code span is an *example*, not a link -- it renders as
    code, so there is nothing for a reader to click and nothing to resolve. This
    matters here rather than in theory: the notes in `AGENTS.md` about this very
    checker quote a broken link, and without this they would fail the check they
    describe.
    """
    out: list[str] = []
    i, n = 0, len(line)
    while i < n:
        if line[i] != "`":
            out.append(line[i])
            i += 1
            continue
        j = i
        while j < n and line[j] == "`":
            j += 1
        run = j - i
        # A code span closes with a run of exactly the same length, so ``a`b`` is
        # one span and does not end at the inner backtick.
        close = line.find("`" * run, j)
        if close == -1:
            out.append(line[i:j])  # an unmatched run is literal text
            i = j
        else:
            i = close + run
    return "".join(out)


def check(path: Path) -> list[str]:
    text = path.read_text(encoding="utf-8")
    have = anchors(text)
    # A fragment on a relative link names a heading in the *target* file, so the
    # target's anchors are needed too. Cache them: the same file is often linked
    # several times, and re-reading it per link would make this quadratic.
    cache: dict[Path, set[str]] = {path.resolve(): have}
    errors: list[str] = []

    def target_anchors(p: Path) -> set[str]:
        key = p.resolve()
        if key not in cache:
            try:
                cache[key] = anchors(p.read_text(encoding="utf-8"))
            except (OSError, UnicodeDecodeError):
                cache[key] = set()
        return cache[key]

    in_fence = False
    for lineno, line in enumerate(text.splitlines(), 1):
        if FENCE.match(line):
            in_fence = not in_fence
            continue
        if in_fence:
            continue
        for target in LINK.findall(strip_inline_code(line)):
            if "://" in target or target.startswith(("mailto:", "tel:")):
                continue  # an external link; not this repository's to resolve

            file_part, _, frag = target.partition("#")

            if not file_part:
                # A same-document link: the fragment names a heading here.
                if frag and frag not in have:
                    errors.append(
                        f"{path}:{lineno}: no heading matches anchor '#{frag}'"
                    )
                continue

            target_file = path.parent / file_part
            if not target_file.exists():
                errors.append(
                    f"{path}:{lineno}: link target '{file_part}' does not exist"
                )
                continue

            # The file exists, but the fragment is a claim about the *target's*
            # headings, and dropping it here is how a renamed heading in another
            # document goes unnoticed: the link still resolves as a file, so it
            # renders as a link that lands on the top of the page instead of the
            # section it names.
            if frag and target_file.suffix.lower() in MARKDOWN:
                if frag not in target_anchors(target_file):
                    errors.append(
                        f"{path}:{lineno}: no heading matches anchor '#{frag}' "
                        f"in {file_part}"
                    )
    return errors


def default_paths() -> list[Path]:
    """Every top-level Markdown document, README first.

    Discovered rather than listed so that a document added later is checked
    without anyone remembering to add it to the gate.
    """
    docs = sorted(p for p in ROOT.glob("*.md") if p.is_file())
    readme = ROOT / "README.md"
    return [readme] + [p for p in docs if p != readme]


def main(argv: list[str]) -> int:
    paths = [Path(a) for a in argv[1:]] or default_paths()
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
