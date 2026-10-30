# Ferrocene: the qualified toolchain, as an oracle

Ferrocene is the qualified Rust toolchain — ISO 26262 ASIL D, IEC 61508 SIL 3,
EN 50128, IEC 62304. It is the one compiler whose word carries weight for a
safety-critical claim, which is why this repository checks its own `no_std`
builds with it.

It is an **oracle, not a dependency**. Ferrocene is invoked as a subprocess,
exactly like Kani, Verus, Lean, Coq and z3, and adds nothing to the dependency
tree; the zero-external-dependency gate in `scripts/gate.sh` holds whether or not
Ferrocene is present.

## What it checks, and what it does not

The crate's README says plainly that it has no qualification evidence of its own.
That is still true after this runs. What this checks is the half that *can* be
checked:

- the qualified compiler accepts the same sources, unchanged, and
- it produces the same artifact shape for the target this repository ships to
  (`thumbv7em-none-eabihf`), which is a target Ferrocene itself qualifies.

The three builds are the parent crate without `std`, the arithmetic sibling, and
`examples/bare_metal.rs`. The example is the one that matters most: it is
`#![no_std]` and it calls the decision procedure, so compiling it for
`thumbv7em-none-eabihf` is what shows the *prover* — the BDD blasting and the SAT
fallback, not just the types around them — is code the qualified compiler accepts
for the target.

It does **not** check that the verification the crate performs is sound, and it
does not confer qualification on the crate. A qualified *compiler* is not a
qualified *verifier*; `discharge`'s engine is not in Ferrocene's qualification
scope, and no amount of building with Ferrocene changes that.

## Why it skips by default

Ferrocene is commercial: a subscription plus a customer-portal token, and its
release archives "require authentication through the customer portal, and don't
allow programmatic access" (Ferrocene User Manual 3.2.1). A public CI job cannot
install it, so the gate reports and skips when it is absent — the same convention
`tools/mir-oracle/run.sh` and the Kani, Verus, Lean and Coq gates use. A skipped
oracle is not evidence, and the gate says so rather than passing in silence.

## Running it

With CriticalUp installed and authenticated:

```sh
criticalup auth set          # paste a customer-portal token
sh tools/ferrocene/run.sh    # resolves the toolchain from criticalup.toml
```

Or point it at an already-installed toolchain:

```sh
FERROCENE_RUSTC=/opt/ferrocene/bin/rustc sh tools/ferrocene/run.sh
```

The script exits `0` when both crates build, `1` on a real build failure, and `2`
when no toolchain was found. `scripts/gate.sh` treats `2` as "report and skip" and
anything else as a failure, so a broken toolchain can never be mistaken for an
absent one.

## In CI

The `ferrocene` job in `.github/workflows/ci.yml` runs this when a
`FERROCENE_TOKEN` secret is configured, and reports and skips otherwise — the
same shape as the Kani and Verus jobs. Nothing about the crate's build changes
when the secret is absent.
