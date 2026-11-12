# Contributing

Thank you for helping. This crate is maintained by Yayasan Pesantren Cipansor
and contributors, and contributions of every size are welcome: a new obligation
in the proof suite, one more differential case, a documentation fix, or a bug
report.

## Ground rules

The crate's whole point is that its safety claims are checkable, so a change is
expected to keep them checkable:

- **No dependency beyond the standard library**, ever, in the default build. The
  crate is `no_std` and links `core` and nothing else. `scripts/gate.sh` step 5
  fails the moment a registry or git dependency appears in the tree. A test
  oracle (z3, Kani, Verus, Lean, Coq) is a *subprocess*, never a dependency.
- **`no_std` by default.** `std` is a feature and adds only the host-side tools
  (the MIR frontend, the file-backed helpers). The engine that ships to a
  microcontroller must build for `thumbv7em-none-eabihf`; gate 4 checks it.
- **`unsafe` is confined and justified.** The two `unsafe` blocks that exist are
  in the `no_std` arena (`src/smt.rs`) and the CNF/solver pair (`src/sat.rs`),
  each guarded by the crate's own single-threaded discipline. Every block needs
  a `// SAFETY:` comment, and gate 17 pins the count so a new one cannot slip in
  unnoticed. New `unsafe` needs a reason that the safe alternatives cannot meet.
- **A proof must not outrun reality.** If you add a decision procedure or a
  shortcut, add the differential test that would catch it disagreeing with the
  thing it is supposed to model. The oracles in `tests/` and `examples/` exist
  for exactly this; a proof with no independent check is a claim, not evidence.
- **Fail closed.** An input the engine cannot handle must answer `Unknown` or
  refuse, never guess `Valid`. See the honesty tests in `tests/wp.rs`.
- **Typed results, not strings.** Verdicts are enums (`Verdict`, `Search`,
  `Outcome`) with `Display`, never a stringly-typed answer.
- **Documented public API.** The crate denies `missing_docs`, and gate 15
  builds the docs with `-D warnings`, so an intra-doc link to a renamed item is
  a build failure rather than a dead link on docs.rs.
- **A README example that runs.** `README.md` is the crate's front page on
  crates.io and its first doctest; keep the flagship example compiling.

## Before you open a pull request

Run the same gates CI runs. One script, eighteen checks:

```sh
sh scripts/gate.sh
```

It must print `ALL GATES GREEN`. The gates are: clippy on both feature sets,
the test suite with a count that fails on failure, the Ferrocene qualified build
(skipped when absent), the `no_std` bare-metal build, the zero-dependency check,
the z3/Kani/Verus/`rustc_public`/Lean/Coq differential oracles, the comparison
fixtures, the MSRV build on the declared floor, the documentation build, the
build-artifact check, the pinned-`unsafe` check, and the build-time zero-cost
check. A gate that *skips* says so; it is not the same as a gate that passed, and
the output keeps the two apart.

Two checks are worth running as well, because they cover things no compiler can:

```sh
python3 scripts/check_actions_pinned.py
sh scripts/check_package.sh
```

The first fails if a GitHub Action is referenced by a mutable tag instead of a
commit SHA. The second is the packaging hygiene check: it verifies that each
crate's manifest is complete enough to publish (description, license, keywords,
categories, `rust-version`, `readme`), that each crate directory carries the
`LICENSE`/`README.md`/`NOTICE` a `.crate` should ship, that no compiled artifact
is tracked, and that every third-party project named in the code is also named in
`NOTICE`.

If you use a language or library feature newer than the declared minimum
(`rust-version` in `Cargo.toml`, currently 1.85), raise that field in the same
change. Edition 2024 is what fixes the floor at 1.85. Gate 14 compiles both
crates against the declared floor, so a stale floor fails there rather than
shipping as a false promise.

## What makes a good contribution

### A new proof or obligation

State the obligation in the crate that can decide it. A property over an 8- or
16-bit domain belongs in `verif-arithmetic`, where the proof is an exhaustive
enumeration that needs nothing but `core`. A property that needs symbolic
reasoning over a wider domain belongs in `verif`'s `smt` engine. When both can
state it, state it in both: `tests/oracle.rs` cross-checks the enumeration
against the symbolic engine, and the disagreement is the interesting event.

### Tests

Test the real code path. Do not reach for a mock unless there is no other way,
and say why in a comment when you do. Prefer a case transcribed from an
authority, a standard, or an independent implementation over one that restates
your own code.

For a claim that a proof is *sound*, hand-picked cases are not enough on their
own. The differential harnesses (`tests/differential.rs`,
`tests/modular_differential.rs`, `tests/op_differential.rs`) generate cases and
compare the engine's answer against execution; add to them rather than writing a
second curated table.

### Documentation

If you change behaviour, update `README.md`. It is the crate's documentation on
crates.io, and it is compiled, so a documented example that no longer works
fails the build.

## Versioning and releases

The two crates version independently, in their own `Cargo.toml`. A release is
named per crate, `<crate>-v<version>`, and publishes exactly that crate — there
is no bare `v<version>` tag, because one tag cannot say which crate it means.
`scripts/publish.py` derives the publish order from the manifests and dry-runs
each crate; `verif` depends on `verif-arithmetic`, so the sibling must be on
crates.io before the parent can be packaged.

Below 1.0 the level follows Cargo's compatibility rule, which is not the same as
above it, because `^0.1.0` accepts `0.1.1` but not `0.2.0`:

| Level | `0.1.0` becomes | When |
| --- | --- | --- |
| `patch` | `0.1.1` | A compatible fix |
| `minor` | `0.2.0` | New functionality, or any breaking change below 1.0 |
| `major` | `1.0.0` | A deliberate move to a stable API |

Adding a public function is a **minor** bump. Maintainers tag and publish; a
contributor does not need a crates.io token.

## Reporting a bug

Open an issue with the input that triggers it, what you expected, and what
happened. A false `Valid` is a **soundness bug** — see [`SECURITY.md`](SECURITY.md)
and report it privately rather than in a public issue.

## License

By contributing you agree that your contribution is licensed under the Apache
License, Version 2.0 ([`LICENSE`](LICENSE)). There is no contributor licence
agreement to sign. Add yourself to the contributors list in the pull request if
you would like to be credited.
