# Security Policy

## Reporting a vulnerability

Report vulnerabilities through **GitHub's private vulnerability reporting** on
this repository:

<https://github.com/cipansor/discharge/security/advisories/new>

That form is private: only the maintainers see the report until an advisory is
published, and it gives us a place to discuss a fix and request a CVE in one
thread. Please do not open a public issue for a suspected vulnerability.

Include, as far as you can:

- the affected version or commit,
- the smallest input that shows the problem,
- what you expected and what happened,
- and, for a soundness bug, the obligation you believe was discharged wrongly.

## Scope

The interesting class of vulnerability in a verifier is not a crash. It is a
**soundness bug**: an input for which `prove` returns `Valid` (or an obligation
is reported discharged) when the property does not actually hold. A verifier
that lies is worse than one that crashes, because a crash is visible and a false
`Valid` is not — it produces a false assurance in exactly the safety-critical
code this crate is aimed at. Reports of this kind are the most valuable and are
treated as the highest severity.

In scope:

- **Soundness of the engine.** A `Verdict::Valid`, a `Certificate`, or a
  discharged obligation that is not backed by the formula it claims to be about.
  This includes the bit-blaster disagreeing with Rust's own wrapping arithmetic,
  the two engines (`smt` and `sat`/`bitblast`) disagreeing on the same term
  graph, and a counterexample that does not replay against the compiled function.
- **The `unsafe` code.** There are three `unsafe` blocks in `src/`. The
  `static mut CTX` in the `no_std` build (`src/smt.rs`) is a single global
  guarded by the crate's own discipline rather than by the compiler; a way to
  reach it that breaks that discipline — in particular from more than one thread
  on bare metal — is in scope.
- **The MIR frontend.** `discharge::mir` shells out to `rustc --emit=mir` and
  parses the textual dump. A crafted or merely unusual input that makes the
  parser accept something it should refuse (rather than failing closed) is in
  scope.
- **The exported query.** `smtscript` writes SMT-LIB2 that an external solver
  will read. A formula whose export does not mean what the engine proved is in
  scope.

Out of scope:

- A reported `Unknown`, `Incomplete`, or a refusal. Those are the engine
  declining to answer, which is the intended behaviour at the scaling wall and
  at the frontend's modelling limits.
- A wrong answer from an oracle (z3, Kani, Verus) that disagrees with a correct
  engine answer. The oracles are test-only and are not dependencies.
- Anything that requires a modified build of the crate or of `rustc`.
- Denial of service that needs an unbounded input the caller supplies anyway
  (the obligation cap and the SAT conflict budget are the documented defences,
  and they answer `Unknown` rather than hanging).

## What this crate does not protect against

Stated plainly, so a report is not spent on a non-goal:

- **It is a verifier, not a sandbox.** It reasons about code you give it; it
  does not contain code you run.
- **The frontend is a development tool.** `discharge::mir` is `std`-only and
  shells out to `rustc`. It is not part of the artifact that ships to a
  microcontroller. The embedded engine is.
- **Zero dependencies is a security property, and it is checked in CI.** The
  crate links nothing but `core` (and `std` for the host tools), so there is no
  third-party supply chain inside the verified artifact. The gate that enforces
  this is `scripts/gate.sh` step 4.

## Supported versions

The crate is pre-1.0 and has no published release yet. Fixes land on `main`, and
a report is answered against the tip of `main`. Once releases exist, this section
will name the versions that receive fixes.
