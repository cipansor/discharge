//! A MIR frontend: verify the Rust you actually wrote.
//!
//! Every other frontend in this crate reasons about a *model* — a symbolic
//! expression you write by hand next to the function it is supposed to describe.
//! That is a real gap: the model and the code can drift, and only a human eye
//! closes it. This module closes it mechanically instead. It reads the **MIR**
//! that `rustc` itself lowers your function to, symbolically executes it, and
//! discharges the resulting obligations with the same engine (`smt`) that the
//! rest of the crate uses.
//!
//! The pipeline has three stages, and they are separable on purpose:
//!
//! ```text
//!   rustc --emit=mir          src/mir/parse.rs        src/mir/exec.rs
//!   ─────────────────► MIR text ─────────► MirFn ─────────► obligations ──► Verdict
//!                    (parse)              (IR)          (symbolic execution)
//! ```
//!
//! * `parse` turns the textual MIR dump into an IR.
//! * `exec` walks that IR path by path, building one obligation per path.
//! * [`spec`] reads the `requires:` / `ensures:` doc comments from the *source*,
//!   because MIR carries neither attributes nor doc comments. The contract names
//!   the function; the MIR supplies the meaning. Neither can be fooled by the
//!   other. Doc comments rather than attributes because an unknown attribute
//!   needs a proc-macro to consume it, and a proc-macro is a dependency.
//!
//! The IR and the executor are crate-internal on purpose: they are an
//! implementation of a frontend, not a thing to build on. What is public is
//! [`verify`], which answers "is this file's code safe" in terms of outcomes
//! rather than IR nodes, plus [`spec`] for callers that want the contracts on
//! their own.
//!
//! # What is checked
//!
//! Four families of obligation, all on the real MIR:
//!
//! 1. **Panic freedom.** Every `assert` rustc emits — overflow on `+`, division
//!    by zero, shift past the width, index out of bounds — is a reachable
//!    failure if the negated condition is satisfiable under the path condition.
//!    A violation comes back as a counterexample, not as a vague failure.
//! 2. **Postcondition.** At each `return`, `requires ∧ path ⇒ ensures`.
//! 3. **Loop invariant.** An `invariant:` clause is proved by induction: it must
//!    hold on entry to the loop head, and one iteration must leave it true. A
//!    loop with an invariant is *not* unwound, which is what lets a loop with a
//!    symbolic trip count be decided rather than cut off. The head havocs the
//!    locals the loop can write before assuming the invariant, so the exit edge
//!    carries `invariant ∧ ¬guard` over every state the loop can leave — see
//!    `exec::Cut`, and the section in `AGENTS.md` on why omitting that havoc
//!    proves false postconditions.
//! 4. **Reachability.** An `unreachable` that is reachable, and a `requires`
//!    that no input can satisfy, are both reported rather than silently passed.
//!
//! # Bounded, and honest about it
//!
//! This is a *bounded* model checker, like Kani. A loop with no declared
//! invariant is unwound to a bound (`exec::DEFAULT_UNWIND`); a path that needs
//! more is reported `Unknown`, never `Valid`. Calls into the same dump are
//! inlined to a depth
//! (`exec::DEFAULT_INLINE_DEPTH`). A call to something the frontend does not
//! model — an unknown intrinsic, a trait method, anything outside this dump —
//! makes the *path* unknown rather than assuming a convenient result. An
//! unmodelled call is not evidence, in either direction.
//!
//! Arithmetic is modelled exactly where the engine allows. Overflow, underflow
//! and division by zero are predicates, not approximations: a widened product is
//! compared against the width, and division goes through an exact restoring
//! divider. Where a shape is past what the engine can decide — a widened product
//! wider than 16 bits, a shift by a symbolic amount — no predicate is produced
//! and the path is reported unmodelled. Declining is the intended answer there; a
//! weaker predicate would be worse than either, because it could make an
//! overflowing function look panic-free.
//!
//! # Why `std`
//!
//! This module is `std`-only, and that is a deliberate split rather than a
//! retreat from the crate's `no_std` claim. A MIR frontend is host-side tooling:
//! it shells out to `rustc` and it manipulates variable-length data (functions,
//! blocks, paths). The *decision procedure* it calls is still the same
//! allocator-free, `no_std` engine. Nothing about the core changed; only the
//! front door is a host program.

pub(crate) mod exec;
pub(crate) mod intrinsics;
pub(crate) mod parse;
pub mod shape;
pub mod spec;
pub mod verify;
