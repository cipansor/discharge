//! A bounded symbolic memory, and the frame condition that comes with it.
//!
//! The logic in [`crate::smt`] is bit-vectors and booleans. That is enough for
//! arithmetic and control flow, but not for *memory*: you cannot state "this
//! array element is unchanged" with bit-vectors alone. This module adds the one
//! theory that matters most for safety-critical code — a memory with `select`
//! and `store` — and it does so without touching the decision procedure.
//!
//! # How a memory is represented
//!
//! A [`Mem`] of `2^addr_width` cells, each `elem_width` bits, is a slice of
//! ordinary symbolic words: one variable per cell. Reading at a *concrete*
//! address is a slice index. Reading at a *symbolic* address is an ite chain:
//!
//! ```text
//! read(m, a) = ite(a == 0, m[0], ite(a == 1, m[1], ... m[n-1]))
//! ```
//!
//! Because the address has exactly `addr_width` bits, every address value matches
//! exactly one cell and the chain is exact — there is no "default" cell and no
//! aliasing.
//!
//! # Writing is substitution, not mutation
//!
//! There is no mutable store. `store(m, a, v)` is expressed as a *simultaneous*
//! update of every cell:
//!
//! ```text
//! m'[k] = ite(a == k, v, m[k])        for every k
//! ```
//!
//! [`Mem::store_binds`] produces exactly that list of `(cell, expression)` pairs.
//! Because [`crate::smt::substitute`] applies bindings simultaneously and
//! bottom-up, the update is a genuine parallel assignment: every `m[k]` on the
//! right is the *old* value. That is the same mechanism
//! [`crate::wp::Stmt::Assign`] uses, which is why a memory write slots into
//! weakest-precondition generation with no new machinery — see
//! [`crate::wp::Stmt::AssignMany`].
//!
//! # What this buys you
//!
//! The frame condition — the obligation that a write to one address leaves other
//! addresses alone — becomes a theorem rather than a proof obligation you have to
//! remember:
//!
//! ```text
//! read(store(m, a, v), b) == ite(a == b, v, read(m, b))
//! ```
//!
//! [`Mem::frame_lemma`] states it, and `tests/mem.rs` proves it with the engine
//! *and* checks it against concrete evaluation, because a lemma that is only
//! proved by the same code that uses it is weak evidence.
//!
//! # Bounds are structural, and that is the point
//!
//! An address is an `addr_width`-bit word, so it cannot name a cell outside the
//! memory: out-of-range access is *unrepresentable*, not merely proved absent.
//! A bounds check is therefore not an obligation here. The cost is that a
//! genuinely out-of-range access is impossible to model, so you must size the
//! memory to the largest address the real code can produce — and if that is not
//! known, this module is the wrong tool.
//!
//! # Honest limits
//!
//! * Symbolic reads cost `2^addr_width` ites, and the BDD that decides a query
//!   over them grows with the address space. Keep `addr_width` small (up to about
//!   6, i.e. 64 cells) unless you have measured otherwise.
//! * Two memories are compared *cellwise*. There is no extensional equality
//!   axiom beyond that, and no aliasing between two different memories.
//! * Nested `store` chains are handled by substitution, so the number of terms
//!   grows with the number of writes along the path being verified.

use crate::smt::{self, Pred, Var};

/// The largest memory this module models, as a number of cells.
///
/// A symbolic read is an ite chain of this length and the decision procedure sees
/// the whole chain, so the cap is what keeps a query tractable. Raise it only
/// with measurements in hand.
pub const MAX_CELLS: usize = 64;

/// The address width that [`MAX_CELLS`] corresponds to.
pub const MAX_ADDR_WIDTH: u8 = 6;

/// A symbolic memory of `2^addr_width` cells, each `elem_width` bits.
///
/// The cell variables are supplied by the caller, so a memory costs nothing to
/// create and needs no allocator. [`declare`] fills a buffer with fresh ones.
#[derive(Debug, Clone, Copy)]
pub struct Mem<'a> {
    cells: &'a [Var],
    elem_width: u8,
}

/// Declare the cells of a memory: `2^addr_width` fresh variables of
/// `elem_width` bits each, written into `out`.
///
/// Returns the number of cells, which is the slice length to hand to
/// [`Mem::new`]. Panics if `out` is too small, because a short buffer would
/// silently produce a memory with the wrong address space.
pub fn declare(addr_width: u8, elem_width: u8, out: &mut [Var]) -> usize {
    assert!(
        (1..=MAX_ADDR_WIDTH).contains(&addr_width),
        "addr_width must be 1..={} ({} cells)",
        MAX_ADDR_WIDTH,
        MAX_CELLS
    );
    assert!((1..=64).contains(&elem_width), "elem_width must be 1..=64");
    let n = 1usize << addr_width;
    assert!(
        out.len() >= n,
        "buffer of {} cells is too small for {} addresses",
        out.len(),
        n
    );
    for slot in out[..n].iter_mut() {
        *slot = smt::var(elem_width);
    }
    n
}

impl<'a> Mem<'a> {
    /// Wrap a cell slice as a memory.
    ///
    /// The length must be a power of two, because the address space is the full
    /// range of an `addr_width`-bit word.
    pub fn new(cells: &'a [Var], elem_width: u8) -> Mem<'a> {
        assert!(!cells.is_empty(), "a memory needs at least one cell");
        assert!(
            cells.len().is_power_of_two(),
            "cell count {} is not a power of two, so no address width matches it",
            cells.len()
        );
        assert!(
            cells.len() <= MAX_CELLS,
            "cell count {} exceeds the {}-cell cap; see MAX_CELLS",
            cells.len(),
            MAX_CELLS
        );
        assert!((1..=64).contains(&elem_width), "elem_width must be 1..=64");
        for c in cells {
            assert_eq!(
                smt::bits(*c),
                elem_width,
                "cell width does not match the declared element width"
            );
        }
        Mem { cells, elem_width }
    }

    /// Number of address bits.
    pub fn addr_width(&self) -> u8 {
        self.cells.len().trailing_zeros() as u8
    }

    /// Width of each cell, in bits.
    pub fn elem_width(&self) -> u8 {
        self.elem_width
    }

    /// Number of cells.
    pub fn len(&self) -> usize {
        self.cells.len()
    }

    /// Whether the memory has no cells. Always false for a valid memory; present
    /// so the type does not trip the usual lint.
    pub fn is_empty(&self) -> bool {
        self.cells.is_empty()
    }

    /// The cell variables, in address order.
    pub fn cells(&self) -> &'a [Var] {
        self.cells
    }

    /// The largest address this memory can hold, as a number.
    pub fn addr_max(&self) -> u64 {
        (self.cells.len() - 1) as u64
    }

    /// Read at a concrete address. A slice index, with the bounds check the
    /// compiler can see through.
    pub fn read_const(&self, addr: usize) -> Var {
        assert!(
            addr < self.cells.len(),
            "address {} is outside a memory of {} cells",
            addr,
            self.cells.len()
        );
        self.cells[addr]
    }

    /// Read at a symbolic address.
    ///
    /// Panics if `addr` is not exactly `addr_width` bits: a narrower address
    /// could not name every cell, and a wider one could name values that are not
    /// cells, which would silently alias onto the last one.
    pub fn read(&self, addr: Var) -> Var {
        self.check_addr(addr, "read");
        // Fold from the top down so the chain is built inside-out and the
        // innermost cell is the last one, which is the highest address.
        let mut val = self.cells[self.cells.len() - 1];
        for k in (0..self.cells.len() - 1).rev() {
            val = smt::ite(smt::eq_const(addr, k as u64), self.cells[k], val);
        }
        val
    }

    /// The simultaneous cell updates that implement `store(m, addr, val)`.
    ///
    /// Fills `out` with `(m[k], ite(addr == k, val, m[k]))` for every `k` and
    /// returns the number of pairs written. Apply the result with
    /// [`crate::smt::substitute`] or [`crate::wp::Stmt::AssignMany`]; because
    /// substitution is simultaneous, each `m[k]` on the right-hand side is read in
    /// the *old* state, so the whole memory updates at once.
    ///
    /// Panics if `out` is too short, rather than leaving some cells un-updated,
    /// which would silently drop part of the write.
    pub fn store_binds(&self, addr: Var, val: Var, out: &mut [(Var, Var)]) -> usize {
        self.check_addr(addr, "store");
        assert_eq!(
            smt::bits(val),
            self.elem_width,
            "stored value must be {} bits",
            self.elem_width
        );
        let n = self.cells.len();
        assert!(
            out.len() >= n,
            "buffer of {} bindings is too small for {} cells",
            out.len(),
            n
        );
        for (k, slot) in out[..n].iter_mut().enumerate() {
            let hit = smt::eq_const(addr, k as u64);
            *slot = (self.cells[k], smt::ite(hit, val, self.cells[k]));
        }
        n
    }

    /// The memory after `store(addr, val)`, applied to the predicate `p`.
    ///
    /// This is the weakest-precondition rule for a write: every cell in `p` is
    /// replaced by its value after the store. It is the memory analogue of
    /// [`crate::wp::Stmt::Assign`], and it exists so callers do not have to build
    /// the binding array themselves.
    pub fn store_wp(&self, addr: Var, val: Var, p: Pred) -> Pred {
        let mut binds = [(addr, val); MAX_CELLS];
        let n = self.store_binds(addr, val, &mut binds);
        smt::substitute(p, &binds[..n])
    }

    /// `read(store(m, addr, val), at) == ite(addr == at, val, read(m, at))`.
    ///
    /// The frame condition: a write to `addr` is visible at `at` exactly when the
    /// two addresses coincide, and otherwise the old value survives.
    ///
    /// The left-hand side is *derived* by pushing the store's bindings through
    /// [`crate::smt::substitute_word`], not restated. That matters: a lemma that
    /// merely quotes one of the definitions it is about proves nothing about the
    /// other. Here the two sides come from independently written code — the ite
    /// chain in [`Mem::read`] and the binding list in [`Mem::store_binds`] — so
    /// the equality is a real claim.
    pub fn frame_lemma(&self, addr: Var, val: Var, at: Var) -> Pred {
        self.check_addr(addr, "frame_lemma");
        self.check_addr(at, "frame_lemma");
        let mut binds = [(addr, val); MAX_CELLS];
        let n = self.store_binds(addr, val, &mut binds);
        let read_after = smt::substitute_word(self.read(at), &binds[..n]);
        let expected = smt::ite(smt::eq(addr, at), val, self.read(at));
        smt::eq(read_after, expected)
    }

    /// `read(m, a) == read(m, b)` for the same memory, i.e. addresses that agree
    /// produce the same value. Useful as a sanity lemma and as a rewrite rule.
    pub fn read_congruent(&self, a: Var, b: Var) -> Pred {
        smt::implies(smt::eq(a, b), smt::eq(self.read(a), self.read(b)))
    }

    /// Reject an address that cannot name a cell of this memory.
    fn check_addr(&self, addr: Var, who: &str) {
        assert_eq!(
            smt::bits(addr),
            self.addr_width(),
            "{}: address must be {} bits for a memory of {} cells",
            who,
            self.addr_width(),
            self.cells.len()
        );
    }

    /// Two memories have the same contents.
    ///
    /// This is cellwise equality. There is no separate array-extensionality
    /// axiom, which is exactly right for a bounded memory whose cells are all
    /// visible.
    pub fn equals(&self, other: &Mem<'_>) -> Pred {
        assert_eq!(
            self.cells.len(),
            other.cells.len(),
            "memories of different sizes are never equal"
        );
        let mut acc = smt::truth(true);
        for k in 0..self.cells.len() {
            acc = smt::and(acc, smt::eq(self.cells[k], other.cells[k]));
        }
        acc
    }

    /// The cells where the two memories differ, as a disjunction. The negation of
    /// [`Mem::equals`], stated positively so it reads as "these addresses were
    /// disturbed".
    pub fn differs(&self, other: &Mem<'_>) -> Pred {
        assert_eq!(self.cells.len(), other.cells.len());
        let mut acc = smt::truth(false);
        for k in 0..self.cells.len() {
            acc = smt::or(acc, smt::not(smt::eq(self.cells[k], other.cells[k])));
        }
        acc
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::smt::Verdict;

    #[test]
    fn a_concrete_read_is_a_slice_index() {
        smt::with_fresh(|| {
            let mut buf = [smt::var(8); 4];
            let n = declare(2, 8, &mut buf);
            assert_eq!(n, 4);
            let m = Mem::new(&buf[..n], 8);
            assert_eq!(m.addr_width(), 2);
            assert_eq!(m.len(), 4);
            assert_eq!(m.addr_max(), 3);
            // The cell variables are distinct.
            assert_ne!(m.read_const(0), m.read_const(1));
        });
    }

    #[test]
    fn a_symbolic_read_is_exact_at_every_address() {
        smt::with_fresh(|| {
            let mut buf = [smt::var(8); 4];
            let n = declare(2, 8, &mut buf);
            let m = Mem::new(&buf[..n], 8);
            let a = smt::var(2);

            // At a pinned address, the symbolic read must equal that cell.
            for k in 0..4u64 {
                let v = smt::prove_implies(
                    smt::eq_const(a, k),
                    smt::eq(m.read(a), m.read_const(k as usize)),
                );
                assert_eq!(v, Verdict::Valid, "read disagrees at address {}", k);
            }
        });
    }

    #[test]
    fn the_frame_lemma_holds() {
        smt::with_fresh(|| {
            let mut buf = [smt::var(8); 4];
            let n = declare(2, 8, &mut buf);
            let m = Mem::new(&buf[..n], 8);
            let a = smt::var(2);
            let b = smt::var(2);
            let v = smt::var(8);

            assert_eq!(smt::prove(m.frame_lemma(a, v, b)), Verdict::Valid);
            assert_eq!(smt::prove(m.read_congruent(a, b)), Verdict::Valid);
        });
    }

    #[test]
    fn a_symbolic_read_agrees_with_concrete_evaluation() {
        smt::with_fresh(|| {
            let mut buf = [smt::var(8); 4];
            let n = declare(2, 8, &mut buf);
            let m = Mem::new(&buf[..n], 8);
            let a = smt::var(2);
            let read = m.read(a);

            // Pin every cell and the address, then check the read against the
            // model the engine finds. This is the differential test: the symbolic
            // ite chain has to behave like an array lookup on real numbers.
            let cells = [0u64, 37, 74, 111];
            let mut pre = smt::eq_const(a, 2);
            for (k, value) in cells.iter().enumerate() {
                pre = smt::and(pre, smt::eq_const(m.read_const(k), *value));
            }
            let v = smt::prove_implies(pre, smt::eq_const(read, cells[2]));
            assert_eq!(v, Verdict::Valid, "symbolic read disagrees with a lookup");
        });
    }

    #[test]
    fn a_store_then_read_returns_the_stored_value() {
        smt::with_fresh(|| {
            let mut buf = [smt::var(8); 4];
            let n = declare(2, 8, &mut buf);
            let m = Mem::new(&buf[..n], 8);
            let a = smt::var(2);
            let v = smt::var(8);
            // Reading back at the same address gives the value just written.
            let after = m.store_wp(a, v, smt::eq(m.read(a), v));
            assert_eq!(smt::prove(after), Verdict::Valid);
        });
    }

    #[test]
    fn a_store_leaves_other_cells_alone() {
        smt::with_fresh(|| {
            let mut buf = [smt::var(8); 4];
            let n = declare(2, 8, &mut buf);
            let m = Mem::new(&buf[..n], 8);
            let a = smt::var(2);
            let v = smt::var(8);

            // Stated the way it matters: pin the address away from cell 3, and
            // the old contents of cell 3 survive the write.
            let p = m.store_wp(a, v, smt::eq(m.read_const(3), smt::word(9, 8)));
            let q = smt::implies(
                smt::and(
                    smt::not(smt::eq_const(a, 3)),
                    smt::eq_const(m.read_const(3), 9),
                ),
                p,
            );
            assert_eq!(smt::prove(q), Verdict::Valid);
        });
    }

    #[test]
    fn oversized_memories_are_rejected() {
        let r = std::panic::catch_unwind(|| {
            smt::with_fresh(|| {
                let mut buf = [smt::var(8); MAX_CELLS * 2];
                let _ = declare(MAX_ADDR_WIDTH + 1, 8, &mut buf);
            });
        });
        assert!(r.is_err(), "the cell cap must be enforced at declaration");
    }

    #[test]
    fn store_binds_produces_one_pair_per_cell() {
        smt::with_fresh(|| {
            let mut buf = [smt::var(8); 4];
            let n = declare(2, 8, &mut buf);
            let m = Mem::new(&buf[..n], 8);
            let a = smt::var(2);
            let v = smt::var(8);
            let mut binds = [(a, v); 8];
            let written = m.store_binds(a, v, &mut binds);
            assert_eq!(written, 4);
            // The left-hand sides are the cells, in address order.
            for (k, (target, _)) in binds.iter().enumerate().take(4) {
                assert_eq!(*target, m.read_const(k));
            }
        });
    }

    #[test]
    fn out_of_range_constants_are_rejected() {
        let r = std::panic::catch_unwind(|| {
            smt::with_fresh(|| {
                let mut buf = [smt::var(8); 4];
                let n = declare(2, 8, &mut buf);
                let m = Mem::new(&buf[..n], 8);
                let _ = m.read_const(4);
            });
        });
        assert!(r.is_err(), "reading past the end must not silently succeed");
    }

    #[test]
    fn a_mismatched_address_width_is_rejected() {
        let r = std::panic::catch_unwind(|| {
            smt::with_fresh(|| {
                let mut buf = [smt::var(8); 4];
                let n = declare(2, 8, &mut buf);
                let m = Mem::new(&buf[..n], 8);
                let wide = smt::var(8); // 8-bit address for a 4-cell memory
                let _ = m.read(wide);
            });
        });
        assert!(
            r.is_err(),
            "a wider address could alias onto the last cell; it must be rejected"
        );
    }
}
