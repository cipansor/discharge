//! Read contracts out of the *source*, because MIR does not carry attributes.
//!
//! # Why doc comments, not attributes
//!
//! The obvious syntax would be `#[requires(x < 10)]`, and it is what SPARK's
//! `Pre` looks like. It cannot be used here, for a reason worth stating: an
//! attribute that is not a built-in has to be expanded by a proc macro, and a
//! proc macro is a *crate dependency*. This crate's central claim is that it
//! has none — `cargo tree` must print exactly one line — and giving that up to
//! get nicer syntax would trade the property that makes the tool usable in a
//! bare-metal build for a cosmetic one.
//!
//! So contracts are written as doc comments, which are real Rust syntax, always
//! compile, and need nothing at all:
//!
//! ```
//! /// # Contract
//! /// requires: b != 0
//! /// ensures: ret * b <= a
//! fn div(a: u32, b: u32) -> u32 { a / b }
//! ```
//!
//! The scanner looks for lines beginning `requires:` or `ensures:` inside a doc
//! comment and attaches them to the next `fn`. `//!` inner docs are skipped, so
//! the contract parser does not mistake its own documentation for a contract —
//! a bug this file had until the scanner was made to ignore `//!`.
//!
//! This is the one place the frontend looks at source text rather than at the
//! compiler's own IR, and the split is deliberate. Attributes are erased long
//! before MIR is printed, so a contract cannot ride along with the body. Reading
//! it from source instead keeps the two halves independent: the *body* comes
//! from `rustc`, and the *claim* comes from the file you wrote. Neither can
//! quietly rewrite the other, and a contract that names a function the MIR dump
//! does not contain is reported rather than ignored.
//!
//! # The expression language
//!
//! Deliberately small, and small enough to be obviously sound. A contract is a
//! comparison between two arithmetic expressions over the argument names, the
//! return value (`ret`), and integer literals:
//!
//! ```text
//!   #[requires(a < 1000)]
//!   #[requires(b != 0)]
//!   #[ensures(ret <= a + b)]
//!   #[requires(a <= 100 && b <= 100)]
//!   #[ensures((ret - a) <= 50)]
//! ```
//!
//! Operators: `+ - * & | ^`, comparisons `== != < <= > >=`, and `&& || !`.
//! Anything outside that — a function call, a cast, an array index, a method —
//! is *refused*, and a refused contract means the function is not verified at
//! all. Refusing is the only safe response: a contract the frontend cannot read
//! exactly is a contract it cannot check, and silently dropping it would report
//! success for an unchecked property.

use std::collections::{BTreeMap, BTreeSet};

use crate::mir::parse::{Ty, USIZE_WIDTH};
use crate::smt::{self, Pred, Var};

/// How long an array may be before a symbolic subscript is refused.
///
/// `a[i]` is modelled as an ite chain over the array's whole domain, so the cost
/// is linear in the length. A bound keeps a very large array from turning a
/// contract into a term the solver cannot handle; past it the subscript is
/// refused rather than silently approximated.
pub const MAX_INDEX_CHAIN: u64 = 64;

/// A contract attached to a function.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct FnContract {
    /// Raw text of each `#[requires(...)]`, in source order.
    pub requires: Vec<String>,
    /// Raw text of each `#[ensures(...)]`, in source order.
    pub ensures: Vec<String>,
    /// Raw text of each loop `invariant:`, in source order.
    ///
    /// A loop invariant is not inferred. `wp` already made that call for its own
    /// frontend (`Stmt::While::invariant` is not optional), and for the same
    /// reason: the invariant is the induction hypothesis, and guessing it means
    /// guessing the proof. A loop with no invariant is unwound and reported
    /// incomplete, which is what happened here before this field existed.
    ///
    /// The text is not tied to a loop in the source. A function with one loop has
    /// one invariant; a function with several loops and several `invariant:`
    /// lines is refused rather than guessed at, because attaching the wrong
    /// invariant to the wrong loop would be unsound.
    pub invariants: Vec<String>,
    /// Line number of the `fn` item, for diagnostics.
    pub line: usize,
}

/// Every function's contract, keyed by function name.
#[derive(Clone, Debug, Default)]
pub struct Specs {
    /// Contracts keyed by function name. A function with no entry has no
    /// contract, which means "check panic freedom on every input" rather than
    /// "skip it".
    pub by_fn: BTreeMap<String, FnContract>,
    /// Struct layouts read from the same source, keyed by struct name.
    ///
    /// A contract that names a field (`c.lo`) needs two things the MIR dump does
    /// not carry: which *index* that name is (declaration order), and the field's
    /// width and signedness. The dump prints `_1: &Config` and nothing about
    /// `Config`, so the layout has to come from the source — the same place the
    /// contract text itself comes from, which keeps the two consistent by
    /// construction. A struct with no entry here has no readable fields, and a
    /// contract naming one is refused rather than guessed.
    pub structs: BTreeMap<String, StructDef>,
}

/// A struct's fields, in declaration order.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct StructDef {
    /// `(name, type)` for each field. The index in this vector *is* the MIR field
    /// index, because a struct without `repr(transparent)`/reordering has its
    /// fields in declaration order and rustc prints `.0` for the first one.
    pub fields: Vec<(String, Ty)>,
}

impl StructDef {
    /// The field index for `name`, or `None` if the struct has no such field.
    pub fn index_of(&self, name: &str) -> Option<u32> {
        self.fields.iter().position(|(n, _)| n == name).map(|i| i as u32)
    }
}

impl Specs {
    /// The contract attached to `name`, if the source declared one.
    pub fn get(&self, name: &str) -> Option<&FnContract> {
        self.by_fn.get(name)
    }
}

/// Extract contracts from Rust source text.
///
/// The scanner is line-oriented and deliberately shallow: it collects
/// `requires:` / `ensures:` lines from doc comments and attaches them to the
/// next `fn` item. It fails closed — a contract it cannot parse becomes a
/// [`SpecError`] at evaluation time, which causes the function to be *skipped*
/// rather than verified against a contract that was silently dropped.
///
/// Only `///` (outer) doc comments are read. `//!` (inner) comments are ignored
/// so that module documentation describing the syntax is not read as a contract
/// for the next function in the file.
pub fn extract(source: &str) -> Specs {
    let mut specs = Specs::default();
    let mut pending = FnContract::default();
    let mut in_block_comment = false;

    // Struct layouts, read in the same pass. The MIR dump names a struct
    // (`_1: &Config`) but never prints its fields, so a contract like
    // `c.lo <= c.hi` has no way to learn that `lo` is field 0 of width 8 unless
    // the layout is read here.
    let mut cur_struct: Option<(String, StructDef)> = None;

    for (lineno, raw_line) in source.lines().enumerate() {
        let line = raw_line.trim();
        if in_block_comment {
            if line.contains("*/") {
                in_block_comment = false;
            }
            continue;
        }
        if line.starts_with("/*") {
            if !line.contains("*/") {
                in_block_comment = true;
            }
            continue;
        }
        // Inside a struct body: read fields until the closing brace.
        if cur_struct.is_some() {
            if line.starts_with('}') {
                let (name, def) = cur_struct.take().unwrap();
                specs.structs.insert(name, def);
                continue;
            }
            if let Some((fname, fty)) = struct_field(line) {
                if let Some((_, def)) = cur_struct.as_mut() {
                    def.fields.push((fname, Ty::parse(&fty)));
                }
            }
            continue;
        }
        if let Some(name) = struct_head(line) {
            cur_struct = Some((name, StructDef::default()));
            continue;
        }
        // Inner doc comments (`//!`) and ordinary comments are not contracts.
        if line.starts_with("//!") || line.starts_with("//") && !line.starts_with("///") {
            continue;
        }
        if let Some(rest) = line.strip_prefix("///") {
            let t = rest.trim();
            if let Some(r) = t.strip_prefix("requires:") {
                pending.requires.push(r.trim().to_string());
            } else if let Some(r) = t.strip_prefix("ensures:") {
                pending.ensures.push(r.trim().to_string());
            } else if let Some(r) = t.strip_prefix("invariant:") {
                pending.invariants.push(r.trim().to_string());
            }
            continue;
        }
        // A function item: attach whatever is pending and start fresh. A
        // function with no contract is not recorded, so the set of entries is
        // exactly "the functions that carry a claim" rather than "every function
        // in the file".
        if let Some(name) = fn_name(line) {
            if !pending.requires.is_empty()
                || !pending.ensures.is_empty()
                || !pending.invariants.is_empty()
            {
                pending.line = lineno + 1;
                specs.by_fn.insert(name, std::mem::take(&mut pending));
            }
            pending = FnContract::default();
            continue;
        }
        // Any other non-comment, non-blank line ends a doc block without a
        // function, so pending contracts are dropped rather than carried over to
        // an unrelated function further down the file.
        if !line.is_empty() && !line.starts_with('#') {
            pending = FnContract::default();
        }
    }
    specs
}

/// Pull the function name out of a `pub fn name(...)` / `fn name(...)` line.
fn fn_name(line: &str) -> Option<String> {
    let t = line.trim_start_matches("pub(crate) ").trim_start_matches("pub ").trim();
    let rest = t.strip_prefix("const ").unwrap_or(t).trim();
    let rest = rest.strip_prefix("async ").unwrap_or(rest).trim();
    let rest = rest.strip_prefix("unsafe ").unwrap_or(rest).trim();
    let rest = rest.strip_prefix("extern \"C\" ").unwrap_or(rest).trim();
    let rest = rest.strip_prefix("fn ")?;
    let name: String = rest
        .chars()
        .take_while(|c| c.is_alphanumeric() || *c == '_')
        .collect();
    if name.is_empty() {
        None
    } else {
        Some(name)
    }
}

// ---------------------------------------------------------------------------
// Contract expression evaluation
// ---------------------------------------------------------------------------

/// Why a contract could not be turned into a predicate.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpecError {
    /// The contract text that could not be read.
    pub text: String,
    /// Why it could not be read.
    pub reason: String,
}

impl SpecError {
    /// Re-point the error at the *source* contract text.
    ///
    /// The parser reads the text *after* the field rewrite, so its errors quote
    /// mangled names (`a__chain`, `c__f0`) that appear nowhere in the source.
    /// Reporting those to the user is a diagnosability bug, not just a cosmetic
    /// one: the name in the message cannot be searched for. The reason is kept as
    /// is -- it is about the rewritten form -- and only the quoted text is the
    /// source's.
    fn about(self, text: &str) -> Self {
        Self { text: text.to_string(), reason: self.reason }
    }
}

impl std::fmt::Display for SpecError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "cannot read contract `{}`: {}", self.text, self.reason)
    }
}

/// The fields a contract may name, resolved to symbolic variables.
///
/// A contract writes `c.lo`, but the expression language knows only flat
/// identifiers. Rather than grow the grammar with a projection operator, each
/// readable field is *rewritten* to a mangled identifier (`c.lo` → `c__f0`) and
/// bound to a variable of the field's own width and signedness. The grammar stays
/// a comparison of arithmetic expressions over names, and the projection is a
/// binding decision made before parsing — one place, not one per operator.
///
/// The rewrite is textual and runs on the whole contract, so it must not fire
/// inside a longer identifier: `xs.len()` is handled separately (a length is a
/// property of the argument, not a field), and `myc.lo` must not match `c.lo`.
/// The scanner is therefore token-aware rather than a `replace`.
#[derive(Clone, Debug, Default)]
pub struct FieldEnv {
    /// Mangled name → the variable standing for that field.
    pub vars: BTreeMap<String, Var>,
    /// Which mangled names are signed, for comparison signedness.
    pub signed: BTreeSet<String>,
    /// `arg.field` → mangled name, so the rewrite can be driven by what actually
    /// exists rather than by a pattern.
    pub paths: BTreeMap<String, String>,
    /// The argument names known to be aggregates. Used only to *diagnose*: a
    /// contract naming `c.lo` where `c` is a struct but `lo` is not a field gets
    /// "unknown field `lo`" rather than a parser error about the `.` it cannot
    /// reduce. Both refuse; one says why.
    pub known_args: BTreeSet<String>,
    /// The first variable slot this environment may use. It is one past the
    /// highest local the function declares, so a field variable can never take an
    /// index a local already holds.
    ///
    /// A *fixed* base would be a soundness assumption about the input ("no
    /// function has 200 locals"). Two variables at one index is not a missing
    /// proof but a wrong one, so the base is derived from the function instead of
    /// assumed about it. If the fields do not fit below `MAX_VARS`, the field is
    /// refused rather than aliased.
    base: u32,
    /// How many fields have been bound, which is also the next variable slot.
    next_slot: u32,
    /// Base slot for `ret.N` bindings, so they cannot collide with argument
    /// field slots. The return value's own variable is allocated by the caller
    /// (it is a real local), so only the *projections* get slots here.
    next_ret_slot: u32,
    /// `(local, field index, variable)` for each bound field.
    ///
    /// The executor reads `_1.0` out of its own `fields` map, so the *same*
    /// variable the contract names as `c.lo` has to be seeded there under
    /// `(_1, 0)`. If the two disagreed, the contract would be about one symbolic
    /// input and the body about another, and every proof would be vacuous in the
    /// direction that matters. These seeds are how the two are made to agree by
    /// construction rather than by convention.
    pub seeds: Vec<(u32, u32, Var)>,
    /// `(local, fixed length)` for each *array* argument, so the executor can
    /// enumerate the domain a symbolic subscript needs. A slice has no entry:
    /// there is no fixed domain, so its `xs[i]` stays refused.
    pub array_lens: Vec<(u32, u64)>,
    /// `(local, length variable, element width)` for each slice or array
    /// argument.
    ///
    /// A slice has no length in its type, so the length is a symbolic input, and
    /// `xs.len()` in a contract and `PtrMetadata(_1)` in the body must name the
    /// same one. An array's length *is* in its type, so there it is the constant
    /// `N`, and the contract's `a.len()` and the body's `const N_usize` agree by
    /// being the same word. This is the indexed analogue of `seeds`.
    pub len_seeds: Vec<(u32, Var, u8)>,
    /// `(local, index, element variable)` for each slice or array element the
    /// contract names. The body's `(*_1)[0]` reads the same variable, so `xs[0]`
    /// in a contract and `xs[0]` in the body are one value, not two that look
    /// alike.
    pub elem_seeds: Vec<(u32, u64, Var)>,
    /// Indexed arguments (slices and arrays): name → (local, element width, the
    /// array's fixed length if it is one), so a contract's `xs.len()` and `xs[0]`
    /// can be bound without the IR's `Ty` in hand.
    ///
    /// The length is `Some(n)` for an array and `None` for a slice, which is what
    /// lets a contract naming `a[9]` on a `[u8; 4]` be refused as out of range
    /// rather than bound to a fresh variable for an element that does not exist.
    indexed: BTreeMap<String, (u32, u8, Option<u64>)>,
    /// `arg -> index variable` for an array argument a contract subscripts with a
    /// *symbolic* index (`a[i]`).
    ///
    /// An array has a finite domain, so a symbolic subscript can be *modelled*
    /// rather than refused: `a[i]` becomes the ite chain over `0..N`, which is
    /// exact. The index variable is a fresh input, and the chain is built by the
    /// parser from the element variables in [`elem_seeds`](Self::elem_seeds) so
    /// the contract's `a[i]` and the body's `a[i]` are the same expression.
    ///
    /// A *slice* gets no entry: its length is a symbolic input, so there is no
    /// finite domain to enumerate and `xs[i]` stays a refusal. That is the honest
    /// boundary -- an array's length is in its type, a slice's is not.
    sym_index: BTreeMap<String, Var>,
    /// `arg -> the index argument's name` for an array a contract subscripts
    /// symbolically, so the rewrite can tell `a[i]` (which has a chain) from
    /// `a[j]` (which does not) instead of rewriting both to the same chain.
    sym_index_name: BTreeMap<String, String>,
    /// `arg -> the ite chain` for an array a contract subscripts symbolically.
    ///
    /// Built once by [`bind_sym_index`](Self::bind_sym_index) from the element
    /// variables, so the rewrite can replace `a[i]` with a *name* the parser
    /// resolves, and the chain is the same term every time it is used. An array
    /// argument has no variable of its own (its type has no bit width), so
    /// without this the parser would refuse `a` as an unknown name.
    sym_chain: BTreeMap<String, Var>,
    /// Every *source* name in scope: the argument names.
    ///
    /// The bindings above are named by mangling (`a__len`, `c__f0`,
    /// `a__chain`), and those names are handed to the parser alongside the
    /// arguments. If a real argument happens to be called `a__chain`, the
    /// generated binding would shadow it: `eval_requires` extends the argument
    /// names with the generated ones, so the later insert wins and a contract
    /// naming that argument silently reads the array's chain instead. That is a
    /// false proof, not a parse error. Every generated name is therefore checked
    /// against this set before it is inserted, and the binding is refused rather
    /// than allowed to shadow an argument.
    declared: BTreeSet<String>,
}

impl FieldEnv {
    /// Whether `name` may be introduced as a generated binding.
    ///
    /// It may not when a *source* name already holds it: the generated binding is
    /// inserted after the arguments when a contract is parsed, so a collision
    /// would let the generated value shadow the argument and a contract naming
    /// that argument would be checked against the wrong input.
    fn name_is_free(&self, name: &str) -> bool {
        !self.declared.contains(name)
    }

    /// Bind a field of an argument to a variable.
    ///
    /// The slot is handed out sequentially, not derived from a hash of the path.
    /// A hash can collide, and two fields sharing a variable is not a missing
    /// proof but a *wrong* one — `c.lo <= c.hi` would become `x <= x`. A counter
    /// cannot collide, so there is nothing to argue about.
    pub fn bind(&mut self, local: u32, arg: &str, field: &str, index: u32, ty: &Ty) -> Option<()> {
        self.bind_bits(local, arg, field, index, ty.width()?, ty.is_signed())
    }

    /// Record that `name` is an aggregate argument, so a contract naming a field
    /// it does not have gets a message about the field rather than about the dot.
    pub fn declare_arg(&mut self, name: &str) {
        self.known_args.insert(name.to_string());
        self.declared.insert(name.to_string());
    }

    /// [`bind`] by width and signedness, for callers outside the crate that
    /// cannot name the IR's `Ty`.
    ///
    /// This is the primitive; `bind` is the typed wrapper. Keeping the IR
    /// internal is deliberate (see the module docs), so the public entry point
    /// takes a width rather than a `Ty` and does not leak the parse tree.
    pub fn bind_bits(
        &mut self,
        local: u32,
        arg: &str,
        field: &str,
        index: u32,
        w: u8,
        signed: bool,
    ) -> Option<()> {
        if !(1..=64).contains(&w) {
            return None;
        }
        // A field is a distinct symbolic input from the argument's own variable.
        // `var_named` keys on the *local index*, so a field needs an index no
        // local of this function can use; the base is past the range rustc prints
        // for these corpora and `var_named` refuses anything at or above
        // `MAX_VARS`, which keeps a very large field count a refusal rather than
        // an alias.
        let slot = self.base + self.next_slot;
        if slot as usize >= crate::smt::MAX_VARS {
            return None;
        }
        let mangled = format!("{arg}__f{index}");
        if !self.name_is_free(&mangled) {
            return None;
        }
        self.next_slot += 1;
        let v = smt::var_named(slot, w);
        self.vars.insert(mangled.clone(), v);
        self.seeds.push((local, index, v));
        if signed {
            self.signed.insert(mangled.clone());
        }
        self.paths.insert(format!("{arg}.{field}"), mangled);
        self.known_args.insert(arg.to_string());
        Some(())
    }
}


impl FieldEnv {
    /// Bind `ret.N` to a variable, for a postcondition that names a component of
    /// a tuple return.
    ///
    /// Unlike an argument field, the variable here is not fresh: it is whatever
    /// the executor holds for element `N` of the return place, so the contract's
    /// `ret.0` and the body's `_0.0` are the same value. `slot` is only used by
    /// the up-front parse probe, which needs *some* variable of the right width
    /// and does not care which.
    pub fn bind_ret(&mut self, index: u32, ty: &Ty, v: Var) -> Option<()> {
        // The component's own type decides. A `&T` component is *not* read
        // through to its referent here, because the executor seeds a scalar `&T`
        // argument as `Unknown` (`Ty::width` is `None` for `Ref`), so a `ret.1`
        // of type `&u8` has no value to bind. Reading through would make the probe
        // accept a component the run then cannot resolve -- the probe exists to
        // refuse exactly what the run would refuse, so it must refuse here too.
        ty.width()?;
        let mangled = format!("ret__f{index}");
        self.vars.insert(mangled.clone(), v);
        if ty.is_signed() {
            self.signed.insert(mangled.clone());
        }
        self.paths.insert(format!("ret.{index}"), mangled);
        Some(())
    }

    /// A fresh variable for the `index`-th return projection, for the parse probe.
    ///
    /// Only called for a component a contract actually *names* (see
    /// [`named_ret_components`]). Binding every declared component instead made a
    /// `(u8, &u8)` return unprobeable -- component 1 is a reference with no
    /// bit-vector width -- so the whole function was skipped for a component no
    /// contract asked about, even when the contract only mentioned `ret.0`.
    pub fn probe_ret_slot(&mut self, index: u32, ty: &Ty) -> Option<Var> {
        let w = ty.width()?;
        // Past the field slots, so a return component and an argument field never
        // share an index.
        let slot = self.base + self.next_slot + self.next_ret_slot;
        if slot as usize >= crate::smt::MAX_VARS {
            return None;
        }
        self.next_ret_slot += 1;
        let v = smt::var_named(slot, w);
        self.bind_ret(index, ty, v)?;
        Some(v)
    }

    /// Bind a slice argument's length to a fresh symbolic variable.
    ///
    /// `xs.len()` has no constant value — the length is whatever the caller
    /// passed — so it is an input, exactly like the elements. The same variable
    /// is handed to the executor as a `len_seed`, which is what makes the
    /// contract's `xs.len()` and the body's `PtrMetadata(_1)` one value.
    pub fn bind_indexed_len(&mut self, local: u32, arg: &str, elem_w: u8) -> Option<Var> {
        if !(1..=64).contains(&elem_w) {
            return None;
        }
        let len_name = format!("{arg}__len");
        if !self.name_is_free(&len_name) {
            return None;
        }
        let slot = self.base + self.next_slot;
        if slot as usize >= crate::smt::MAX_VARS {
            return None;
        }
        self.next_slot += 1;
        let v = smt::var_named(slot, USIZE_WIDTH);
        self.vars.insert(len_name, v);
        self.paths.insert(format!("{arg}.len()"), format!("{arg}__len"));
        self.indexed.insert(arg.to_string(), (local, elem_w, None));
        self.len_seeds.push((local, v, elem_w));
        self.known_args.insert(arg.to_string());
        Some(v)
    }

    /// Bind an array argument's length to its *constant*, `N`.
    ///
    /// Unlike a slice, an array's length is part of its type, so `a.len()` is the
    /// constant `N` and not an input: there is nothing for the caller to choose.
    /// Binding it to a fresh variable would be the unsound direction — it would
    /// admit lengths the type excludes, so a contract proved at length 4 would
    /// claim to hold at any length.
    pub fn bind_array_len(&mut self, local: u32, arg: &str, elem_w: u8, n: u64) -> Option<()> {
        if !(1..=64).contains(&elem_w) {
            return None;
        }
        let len_name = format!("{arg}__len");
        if !self.name_is_free(&len_name) {
            return None;
        }
        let v = smt::word(n, USIZE_WIDTH);
        self.vars.insert(len_name, v);
        self.paths.insert(format!("{arg}.len()"), format!("{arg}__len"));
        self.indexed.insert(arg.to_string(), (local, elem_w, Some(n)));
        self.len_seeds.push((local, v, elem_w));
        self.array_lens.push((local, n));
        self.known_args.insert(arg.to_string());
        Some(())
    }

    /// Bind one element of a slice or array argument to a fresh symbolic variable.
    ///
    /// `xs[k]` is a distinct input per index — two indices are two variables, so
    /// `xs[0] == xs[1]` is not provable — and the same index twice is the same
    /// variable. The element width is the *referent* width (`u8` for `[u8; 4]`),
    /// not the length's.
    ///
    /// An array index past its length is refused rather than bound: the element
    /// does not exist, so a contract naming it is about nothing, and a fresh
    /// variable there would make a meaningless precondition look like a real one.
    fn bind_indexed_elem(&mut self, arg: &str, index: u64) -> Option<Var> {
        let (local, elem_w, fixed_len) = *self.indexed.get(arg)?;
        if !(1..=64).contains(&elem_w) {
            return None;
        }
        if let Some(n) = fixed_len {
            if index >= n {
                return None;
            }
        }
        // Already bound (the same index twice in one contract): reuse it, so
        // `xs[0] <= xs[0]` is `x <= x` rather than two unrelated inputs.
        let mangled = format!("{arg}__e{index}");
        if let Some(v) = self.vars.get(&mangled) {
            return Some(*v);
        }
        if !self.name_is_free(&mangled) {
            return None;
        }
        let slot = self.base + self.next_slot;
        if slot as usize >= crate::smt::MAX_VARS {
            return None;
        }
        self.next_slot += 1;
        let v = smt::var_named(slot, elem_w);
        self.vars.insert(mangled.clone(), v);
        self.paths.insert(format!("{arg}[{index}]"), mangled);
        self.elem_seeds.push((local, index, v));
        Some(v)
    }

    /// Bind a symbolic array index: the index variable, and every element of the
    /// array, so the parser can build the ite chain from bindings that already
    /// exist.
    ///
    /// The index is a fresh input (whatever the caller passed) and the elements
    /// are the same ones a literal `a[k]` would bind, so `a[i]` and `a[0]` share
    /// their element variables and the two cannot disagree. The *range* is not
    /// checked here: the parser records `i < N` alongside the chain, and the
    /// contract is refused unless the precondition implies it. Enumerating
    /// `0..N` is why this only applies to an array -- a slice's length is a
    /// symbolic input, so there is nothing to enumerate.
    ///
    /// Every element is bound up front rather than on first use because the
    /// postcondition is evaluated in a closure that cannot hold a `&mut`, and
    /// because the executor is handed the same element variables as seeds: an
    /// element the contract did not bind would be created fresh by the body and
    /// the two `a[i]` would then be different values that look alike.
    pub fn bind_sym_index(
        &mut self,
        arg: &str,
        elem_w: u8,
        n: u64,
        index_name: &str,
        index: Var,
    ) -> Option<Var> {
        if !(1..=64).contains(&elem_w) {
            return None;
        }
        if n > MAX_INDEX_CHAIN {
            return None;
        }
        if let Some(v) = self.sym_index.get(arg) {
            // The same array subscripted by two different symbolic indices has no
            // single chain to rewrite to. Refusing keeps the second subscript a
            // refusal rather than silently reusing the first chain.
            return if *v == index { Some(*v) } else { None };
        }
        // The elements first, so the chain has all of them to build from.
        let mut elems = Vec::with_capacity(n as usize);
        for k in 0..n {
            elems.push(self.bind_indexed_elem(arg, k)?);
        }
        let v = index;
        self.sym_index.insert(arg.to_string(), v);
        self.sym_index_name.insert(arg.to_string(), index_name.to_string());
        // `ite(i == 0, e0, ite(i == 1, e1, ... ite(i == N-1, e_{N-1}, 0)))`.
        // The fall-through is unreachable: every use of the chain is guarded by
        // `i < N` (conjoined by `eval_*`, or assumed from the body's own bounds
        // assert), so the value chosen for `i >= N` is never observed.
        let mut chain = smt::word(0, elem_w);
        for k in (0..n).rev() {
            chain = smt::ite(smt::eq_const(v, k), elems[k as usize], chain);
        }
        self.sym_chain.insert(arg.to_string(), chain);
        // The rewrite replaces `a[i]` with this name, and the parser resolves it
        // from `vars`, so the chain has to be reachable by name.
        let chain_name = format!("{arg}__chain");
        if !self.name_is_free(&chain_name) {
            return None;
        }
        self.vars.insert(chain_name.clone(), chain);
        self.paths.insert(chain_name.clone(), chain_name);
        Some(v)
    }

    /// `(index variable, length)` for every array a contract subscripts
    /// symbolically, so the caller can require that the precondition establishes
    /// each index is in range.
    ///
    /// The ite chain has a fall-through for `i >= N` (it has to return
    /// *something*), so the chain is only an honest model of `a[i]` where `i < N`.
    /// Rather than refuse the subscript, the caller proves the precondition
    /// implies the bound; if it does not, the contract is refused. Conjoining the
    /// bound into the precondition instead would be unsound, because it would
    /// quietly strengthen what the source asked to be checked.
    pub fn index_guards(&self) -> Vec<(Var, u64)> {
        self.sym_index
            .iter()
            .filter_map(|(arg, v)| {
                let (_, _, n) = self.indexed.get(arg)?;
                Some((*v, (*n)?))
            })
            .collect()
    }

    /// Bind every indexed element a contract text names, so the rewrite has a
    /// binding for each and the run needs no mutable access to the environment.
    ///
    /// Scanning the text up front rather than binding on demand keeps
    /// `eval_requires` / `eval_ensures` taking `&FieldEnv`: the postcondition is
    /// evaluated inside an `Fn` closure the executor calls on every returning
    /// path, and that closure cannot hold a `&mut`. It also means an element the
    /// body reads but the contract does not is bound by the *executor* (through
    /// `index_elem`), and the two agree because both key on the same index.
    pub fn bind_index_refs(&mut self, text: &str, args: &BTreeMap<String, Var>) {
        let chars: Vec<char> = text.chars().collect();
        let mut i = 0;
        while i < chars.len() {
            if chars[i].is_alphabetic() || chars[i] == '_' {
                let start = i;
                while i < chars.len() && (chars[i].is_alphanumeric() || chars[i] == '_') {
                    i += 1;
                }
                let ident: String = chars[start..i].iter().collect();
                if chars.get(i) == Some(&'[') {
                    let mut j = i + 1;
                    let digits: String = chars[j..].iter().take_while(|c| c.is_ascii_digit()).collect();
                    j += digits.len();
                    if !digits.is_empty() && chars.get(j) == Some(&']') {
                        if let Ok(k) = digits.parse::<u64>() {
                            self.bind_indexed_elem(&ident, k);
                        }
                        i = j + 1;
                        continue;
                    }
                    // Not a literal index: a symbolic subscript of an *array*,
                    // `a[i]`. Only an array has a finite domain to enumerate; a
                    // slice's length is a symbolic input, so `xs[i]` is left
                    // unbound and the parser refuses it. Binding here (rather
                    // than in the parser) keeps the element variables in
                    // `elem_seeds`, so the executor is handed the same ones.
                    // Anything that is not a name the contract may use is left
                    // unbound and refused by the parser -- a refusal, not a
                    // wrong value.
                    let close = chars[j..].iter().position(|c| *c == ']').map(|p| p + j);
                    if let Some(close) = close {
                        let inner: String = chars[i + 1..close].iter().collect();
                        // The index has to be a name the contract may use -- an
                        // argument. A compound index (`a[i + 1]`) is left unbound
                        // and refused by the parser rather than mis-modelled.
                        if let Some(&index) = args.get(&inner) {
                            if let Some((_, elem_w, Some(n))) = self.indexed.get(&ident).copied()
                            {
                                self.bind_sym_index(&ident, elem_w, n, &inner, index);
                            }
                        }
                        i = close + 1;
                        continue;
                    }
                }
                continue;
            }
            i += 1;
        }
    }
}

/// Rewrite `arg.field` to its mangled binding, token-aware.
///
/// Only whole `ident.ident` runs that match a *bound* path are replaced, so an
/// unrelated `x.y` is left for the parser to refuse as an unknown name rather
/// than silently becoming something else.
/// The `ret.N` components the given contract texts name.
///
/// The up-front parse probe uses this to bind only what a contract can mention.
/// Binding *every* declared component of the return type makes a `(u8, &u8)`
/// return unprobeable: component 1 is a reference with no bit-vector width, so
/// the probe refuses and the function is `Skipped` -- for a component the
/// contract never named. `(u8, &u8)` and `(bool, &T)` returns are ordinary, so
/// that skip silently loses the proof.
///
/// Only `ret.N` is matched, not `result.N`: the rewrite that gives a component
/// its binding emits `ret.N`, so `result.N` was never resolvable and is left to
/// the parser to refuse rather than half-supported here.
pub fn named_ret_components(texts: &[String]) -> BTreeSet<u32> {
    let mut out = BTreeSet::new();
    for text in texts {
        let chars: Vec<char> = text.chars().collect();
        let mut i = 0;
        while i < chars.len() {
            if chars[i].is_alphabetic() || chars[i] == '_' {
                let start = i;
                while i < chars.len() && (chars[i].is_alphanumeric() || chars[i] == '_') {
                    i += 1;
                }
                let ident: String = chars[start..i].iter().collect();
                if ident == "ret" && chars.get(i) == Some(&'.') {
                    let j = i + 1;
                    let digits: String =
                        chars[j..].iter().take_while(|c| c.is_ascii_digit()).collect();
                    if !digits.is_empty() {
                        if let Ok(k) = digits.parse::<u32>() {
                            out.insert(k);
                        }
                    }
                }
                continue;
            }
            i += 1;
        }
    }
    out
}

fn rewrite_fields(text: &str, fields: &FieldEnv) -> Result<String, SpecError> {
    if fields.paths.is_empty() && fields.known_args.is_empty() {
        return Ok(text.to_string());
    }
    let chars: Vec<char> = text.chars().collect();
    let mut out = String::with_capacity(text.len());
    let mut i = 0;
    while i < chars.len() {
        let c = chars[i];
        if c.is_alphabetic() || c == '_' {
            let start = i;
            while i < chars.len() && (chars[i].is_alphanumeric() || chars[i] == '_') {
                i += 1;
            }
            let ident: String = chars[start..i].iter().collect();
            // A field access: `ident.ident`, where the tail is alphanumeric.
            if chars.get(i) == Some(&'.') {
                let dot = i;
                let mut j = i + 1;
                while j < chars.len() && (chars[j].is_alphanumeric() || chars[j] == '_') {
                    j += 1;
                }
                let field: String = chars[dot + 1..j].iter().collect();
                // `xs.len()` — the slice length. The parens are required, so a
                // bare `xs.len` (a field named `len`) is not silently accepted.
                let is_call = chars.get(j) == Some(&'(');
                if field == "len" && is_call {
                    let close = j + 1;
                    if chars.get(close) == Some(&')') {
                        if let Some(mangled) = fields.paths.get(&format!("{ident}.len()")) {
                            out.push_str(mangled);
                            i = close + 1;
                            continue;
                        }
                        if fields.known_args.contains(&ident) {
                            return Err(SpecError {
                                text: text.to_string(),
                                reason: format!(
                                    "`{ident}` is not a slice or array, so `len()` has no meaning here"
                                ),
                            });
                        }
                    }
                }
                let key = format!("{ident}.{field}");
                if !is_call && !field.is_empty() {
                    if let Some(mangled) = fields.paths.get(&key) {
                        out.push_str(mangled);
                        i = j;
                        continue;
                    }
                    // A field of a known aggregate that has no binding: the struct
                    // has no such field, or its layout was not readable. Refuse
                    // with a message that names the field, rather than letting the
                    // `.` reach the parser and produce "expected a comparison
                    // operator" — the same refusal, a diagnosable one.
                    if fields.known_args.contains(&ident) {
                        return Err(SpecError {
                            text: text.to_string(),
                            reason: format!("unknown field `{field}` of `{ident}`"),
                        });
                    }
                }
            }
            // `xs[k]` — a slice element. Only a literal index is rewritten; a
            // symbolic subscript has no binding to rewrite to and is left for the
            // parser to refuse, which is the same answer for a slice as for an
            // array.
            if chars.get(i) == Some(&'[') {
                let mut j = i + 1;
                let digits: String = chars[j..].iter().take_while(|c| c.is_ascii_digit()).collect();
                j += digits.len();
                if !digits.is_empty() && chars.get(j) == Some(&']') {
                    if let Some(mangled) = fields.paths.get(&format!("{ident}[{digits}]")) {
                        out.push_str(mangled);
                        i = j + 1;
                        continue;
                    }
                }
                // `a[i]` on an array: replace the whole subscript with the ite
                // chain bound for `a`. The chain is an exact function of `i`, so
                // this is a definitional rewrite, not an approximation. The index
                // itself is left in place: the range guard (`i < N`) is conjoined
                // by the caller, which is what makes the chain's fall-through
                // unreachable.
                if let Some(close) = chars[j..].iter().position(|c| *c == ']').map(|p| p + j) {
                    let inner: String = chars[i + 1..close].iter().collect();
                    // The chain bound for `ident` is only `ident[inner]` when
                    // `inner` is the very index that chain was built from. A
                    // different index (`a[j]` where the chain is `a[i]`) has no
                    // chain, so it is left for the parser to refuse rather than
                    // rewritten to the wrong subscript.
                    let is_bound_index =
                        fields.sym_index_name.get(&ident).map(|n| n == &inner).unwrap_or(false);
                    if is_bound_index {
                        if let Some(mangled) = fields.paths.get(&format!("{ident}__chain")) {
                            out.push_str(mangled);
                            i = close + 1;
                            continue;
                        }
                    }
                }
            }
            out.push_str(&ident);
            continue;
        }
        out.push(c);
        i += 1;
    }
    Ok(out)
}

/// Turn a `requires` contract into a predicate over the named arguments.
pub fn eval_requires(
    text: &str,
    args: &BTreeMap<String, Var>,
    signed: &BTreeSet<String>,
    fields: &FieldEnv,
) -> Result<Pred, SpecError> {
    let orig = text;
    let text = rewrite_fields(text, fields)?;
    let mut names = args.clone();
    names.extend(fields.vars.iter().map(|(k, v)| (k.clone(), *v)));
    let mut sgn = signed.clone();
    sgn.extend(fields.signed.iter().cloned());
    let mut p = Parser::new(&text, &names, None, &sgn, false);
    let pred = p.parse_or().map_err(|e| e.about(orig))?;
    p.expect_end().map_err(|e| e.about(orig))?;
    Ok(pred)
}

/// The refusal when a bare `ret` names an aggregate return, which has no single
/// word. The contract has to name a component instead.
pub const RET_IS_AGGREGATE: &str =
    "the return type is an aggregate, so `ret` has no single value; name a component such as `ret.0`";

/// The refusal when a bare `ret` names a scalar return whose value the run does
/// not know on this path -- an unmodelled read, or a deref with no backing.
///
/// It is a *different* problem from an aggregate return, and saying "the return
/// type is an aggregate" here would be false: the return type is a plain `u8`,
/// and the reader would go looking for a tuple that does not exist.
pub const RET_IS_UNKNOWN: &str = "the return value is not known on this path";

/// Turn an `ensures` contract into a predicate over the arguments and `ret`.
pub fn eval_ensures(
    text: &str,
    args: &BTreeMap<String, Var>,
    ret: Option<Var>,
    ret_absent: &'static str,
    signed: &BTreeSet<String>,
    ret_signed: bool,
    fields: &FieldEnv,
) -> Result<Pred, SpecError> {
    let orig = text;
    let text = rewrite_fields(text, fields)?;
    let mut names = args.clone();
    names.extend(fields.vars.iter().map(|(k, v)| (k.clone(), *v)));
    let mut sgn = signed.clone();
    sgn.extend(fields.signed.iter().cloned());
    let mut p = Parser::new(&text, &names, ret, &sgn, ret_signed);
    p.ret_absent = ret_absent;
    let pred = p.parse_or().map_err(|e| e.about(orig))?;
    p.expect_end().map_err(|e| e.about(orig))?;
    Ok(pred)
}

/// Turn a loop `invariant:` into a predicate over the function's locals.
///
/// `names` maps a source-level name to the variable standing for that local at
/// the loop head. It is the same expression language as `requires` / `ensures`,
/// but the identifiers resolve against locals (`s`, `i`) rather than only
/// parameters, because a loop invariant is usually about the accumulator.
///
/// A name that resolves to nothing is an error rather than a fresh variable:
/// a typo in an invariant must not become an unconstrained unknown that makes
/// the induction hypothesis vacuous.
pub fn eval_invariant(
    text: &str,
    names: &BTreeMap<String, Var>,
    signed: &BTreeSet<String>,
) -> Result<Pred, SpecError> {
    let mut p = Parser::new(text, names, None, signed, false);
    let pred = p.parse_or()?;
    p.expect_end()?;
    Ok(pred)
}

struct Parser<'a> {
    toks: Vec<Tok>,
    pos: usize,
    args: &'a BTreeMap<String, Var>,
    ret: Option<Var>,
    text: String,
    /// Which argument names have a *signed* type. A contract's `<` is the
    /// signed or the unsigned comparison depending on the operand, and the
    /// unsigned one calls `-1` the largest value, so reading it off the type is
    /// the difference between a contract that says what it means and one that
    /// silently says something else.
    signed: &'a BTreeSet<String>,
    /// Whether `ret` is signed.
    ret_signed: bool,
    /// What to say when `ret` has no value to name. It is supplied by the
    /// caller because only the caller knows *why*: outside an `ensures` the name
    /// is meaningless, an aggregate return has no single word, and a scalar
    /// return can be unbound because the value is not known on this path. These
    /// are three different problems and the message must not describe the wrong
    /// one -- a scalar return reported as an aggregate sends the reader looking
    /// for a tuple that is not there.
    ret_absent: &'static str,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Tok {
    Ident(String),
    Num(u64),
    Op(String),
}

fn tokenize(s: &str) -> Vec<Tok> {
    let mut out = Vec::new();
    let b: Vec<char> = s.chars().collect();
    let mut i = 0;
    while i < b.len() {
        let c = b[i];
        if c.is_whitespace() {
            i += 1;
            continue;
        }
        if c.is_ascii_digit() {
            let mut n = String::new();
            while i < b.len() && (b[i].is_ascii_digit() || b[i] == '_') {
                if b[i] != '_' {
                    n.push(b[i]);
                }
                i += 1;
            }
            // Skip a type suffix (`100u32`) so the literal stays a number.
            while i < b.len() && (b[i].is_alphanumeric()) {
                i += 1;
            }
            out.push(Tok::Num(n.parse().unwrap_or(0)));
            continue;
        }
        if c.is_alphabetic() || c == '_' {
            let mut n = String::new();
            while i < b.len() && (b[i].is_alphanumeric() || b[i] == '_') {
                n.push(b[i]);
                i += 1;
            }
            out.push(Tok::Ident(n));
            continue;
        }
        let two: String = b[i..(i + 2).min(b.len())].iter().collect();
        if ["==", "!=", "<=", ">=", "&&", "||"].contains(&two.as_str()) {
            out.push(Tok::Op(two));
            i += 2;
            continue;
        }
        out.push(Tok::Op(c.to_string()));
        i += 1;
    }
    out
}

impl<'a> Parser<'a> {
    fn new(
        s: &str,
        args: &'a BTreeMap<String, Var>,
        ret: Option<Var>,
        signed: &'a BTreeSet<String>,
        ret_signed: bool,
    ) -> Parser<'a> {
        Parser {
            toks: tokenize(s),
            pos: 0,
            args,
            ret,
            text: s.to_string(),
            signed,
            ret_signed,
            ret_absent: "`ret` is only meaningful in `ensures`",
        }
    }

    /// Whether the variable named `name` is signed, for choosing the comparison.
    fn is_signed_name(&self, name: &str) -> bool {
        if name == "ret" || name == "result" {
            return self.ret_signed;
        }
        self.signed.contains(name)
    }

    fn peek(&self) -> Option<&Tok> {
        self.toks.get(self.pos)
    }

    fn err(&self, reason: impl Into<String>) -> SpecError {
        SpecError { text: self.text.clone(), reason: reason.into() }
    }

    fn eat_op(&mut self, op: &str) -> bool {
        if let Some(Tok::Op(o)) = self.peek() {
            if o == op {
                self.pos += 1;
                return true;
            }
        }
        false
    }

    /// Whether the `(` at the cursor opens a parenthesized *predicate* rather
    /// than arithmetic. Scans to the matching `)` and looks for a comparator or
    /// a boolean operator *anywhere inside* that group. Only a lookahead --
    /// nothing is consumed.
    ///
    /// The scan must not stop at depth one. `((a == 0))` is a predicate wearing a
    /// redundant pair of parentheses, and its comparator sits at depth two; a
    /// depth-one test misses it, the group is then read as arithmetic, the `==`
    /// cannot be consumed, and the whole contract fails to parse. A contract that
    /// fails to parse is a function that never gets verified, so the extra pair
    /// would quietly drop the obligation.
    ///
    /// Looking deeper is safe because the scan stops at the matching close: for
    /// `(a + b) == c` the scan returns at the `)` after `b` and never sees the
    /// `==`, so the group stays arithmetic.
    fn paren_is_predicate(&self) -> bool {
        let mut depth = 0usize;
        for t in &self.toks[self.pos..] {
            match t {
                Tok::Op(o) if o == "(" => depth += 1,
                Tok::Op(o) if o == ")" => {
                    depth -= 1;
                    if depth == 0 {
                        return false;
                    }
                }
                Tok::Op(o)
                    if matches!(o.as_str(), "==" | "!=" | "<=" | ">=" | "<" | ">" | "&&" | "||") =>
                {
                    return true
                }
                Tok::Ident(n) if n == "true" || n == "false" => return true,
                _ => {}
            }
        }
        false
    }

    fn expect_end(&self) -> Result<(), SpecError> {
        if self.pos == self.toks.len() {
            Ok(())
        } else {
            Err(self.err(format!("trailing tokens from token {}", self.pos)))
        }
    }

    fn parse_or(&mut self) -> Result<Pred, SpecError> {
        let mut left = self.parse_and()?;
        while self.eat_op("||") {
            let right = self.parse_and()?;
            left = smt::or(left, right);
        }
        Ok(left)
    }

    fn parse_and(&mut self) -> Result<Pred, SpecError> {
        let mut left = self.parse_cmp()?;
        while self.eat_op("&&") {
            let right = self.parse_cmp()?;
            left = smt::and(left, right);
        }
        Ok(left)
    }

    /// The value of a term that has no free variable, if it is constant.
    ///
    /// `Op::Const` is the common case, but a literal is not always a single node:
    /// `-10` is `0 - 10`, and `1 + 1` is an `Add`. Evaluating the term catches
    /// those too, so a negative or folded literal is resized like any other
    /// rather than treated as an opaque non-constant.
    fn const_value(&self, v: Var) -> Option<u64> {
        smt::evaluate(v, |_| None)
    }

    /// Resize a constant operand to `wide` bits, refusing one that does not fit.
    ///
    /// Widening is exact: zero-extend unsigned, sign-extend signed. Narrowing is
    /// where a contract can be wrong rather than merely imprecise -- `a <= 300`
    /// for a `u8` would become `a <= 44` if the value were truncated -- so a
    /// value that does not fit is an error and the function is skipped, not a
    /// weaker proof.
    fn resize_const(&self, v: Var, wide: u8, signed: bool) -> Result<Var, SpecError> {
        let w = smt::bits(v);
        let val = self.const_value(v).expect("resize_const is only called on a constant");
        if wide >= w {
            return Ok(if signed && wide > w { smt::sign_extend(v, wide) } else { smt::word(val, wide) });
        }
        let fits = if signed {
            // Interpret the value as a signed `w`-bit number, then test it against
            // the signed `wide`-bit range. `i128` keeps `1 << 63` in range.
            let sval = if w >= 64 {
                val as i64 as i128
            } else if val & (1u64 << (w - 1)) != 0 {
                val as i128 - (1i128 << w)
            } else {
                val as i128
            };
            let lo = -(1i128 << (wide - 1));
            let hi = (1i128 << (wide - 1)) - 1;
            sval >= lo && sval <= hi
        } else {
            val < (1u64 << wide)
        };
        if !fits {
            return Err(self.err(format!(
                "literal {val} does not fit the operand's {wide}-bit width"
            )));
        }
        // Truncate rather than rebuild from `val`. A negative literal is the bit
        // pattern `2^w - 10` at its *source* width, so `word(val, wide)` would be
        // handed a value that does not fit `wide` and would set the engine's
        // ill-formed flag -- turning a valid contract into `Unknown`. Truncation
        // takes the low `wide` bits, which is the same bit pattern the value
        // denotes, and the `fits` check above is what keeps it from being silent.
        Ok(smt::truncate(v, wide))
    }

    /// Make two operands agree in width, by resizing the *constant* one.
    ///
    /// A contract literal is written without a type, so its width has to come
    /// from the operand it meets. Sizing it from the widest name in scope instead
    /// makes `ret <= 255` a 64-bit comparison whenever a slice or array length (a
    /// `usize`) is also in scope, and an 8-bit `ret` against a 64-bit constant is
    /// ill-formed -- which the engine reports as `Unknown` for *every* obligation
    /// in the run, not just that one. So the width is decided here, per use.
    ///
    /// Only a constant is resized: a non-constant operand's width is a property
    /// of its type, and changing it would change what the term means. Two
    /// non-constant operands of different widths cannot arise from Rust that
    /// compiles, so that is refused rather than coerced.
    fn align_widths(&self, a: Var, b: Var, signed: bool) -> Result<(Var, Var), SpecError> {
        let (wa, wb) = (smt::bits(a), smt::bits(b));
        if wa == wb {
            return Ok((a, b));
        }
        match (self.const_value(a), self.const_value(b)) {
            (Some(_), None) => Ok((self.resize_const(a, wb, signed)?, b)),
            (None, Some(_)) => Ok((a, self.resize_const(b, wa, signed)?)),
            (Some(_), Some(_)) => {
                if wa > wb {
                    Ok((self.resize_const(a, wb, signed)?, b))
                } else {
                    Ok((a, self.resize_const(b, wa, signed)?))
                }
            }
            (None, None) => {
                Err(self.err("comparison between operands of different widths"))
            }
        }
    }

    fn parse_cmp(&mut self) -> Result<Pred, SpecError> {
        // `true` / `false` as whole predicates, so a contract can say
        // `requires: true` when the function really has no precondition.
        if let Some(Tok::Ident(n)) = self.peek() {
            if n == "true" || n == "false" {
                let v = n == "true";
                self.pos += 1;
                return Ok(smt::truth(v));
            }
        }
        if self.eat_op("!") {
            let inner = self.parse_cmp()?;
            return Ok(smt::not(inner));
        }
        // A parenthesized *predicate*, as in `!(a == MIN && b == -1)`. Which
        // meaning a `(` has is decided by a lookahead to its matching `)`: if a
        // comparator appears at that level it is a predicate, otherwise it is
        // arithmetic and `parse_expr` below handles it.
        if matches!(self.peek(), Some(Tok::Op(o)) if o == "(") && self.paren_is_predicate() {
            self.pos += 1;
            let inner = self.parse_or()?;
            if !self.eat_op(")") {
                return Err(self.err("missing `)`"));
            }
            return Ok(inner);
        }
        let (left, ls) = self.parse_expr()?;
        for op in ["==", "!=", "<=", ">=", "<", ">"] {
            if self.eat_op(op) {
                let (right, rs) = self.parse_expr()?;
                // Both sides of a Rust comparison have the same signedness (the
                // language will not compare an `i8` with a `u8`), so either flag
                // decides it, and a literal on one side leaves the other to say.
                let signed = ls || rs;
                // A literal is written without a type, so its width comes from
                // the operand it meets. Sizing it from the widest name in scope
                // makes `ret <= 255` a 64-bit comparison whenever a slice or
                // array length is also in scope, and an 8-bit `ret` against a
                // 64-bit constant is ill-formed -- which poisons *every*
                // obligation in the run, not just this one.
                let (left, right) = self.align_widths(left, right, signed)?;
                return Ok(match op {
                    "==" => smt::eq(left, right),
                    "!=" => smt::not(smt::eq(left, right)),
                    "<=" if signed => smt::sle(left, right),
                    ">=" if signed => smt::sge(left, right),
                    "<" if signed => smt::slt(left, right),
                    ">" if signed => smt::sgt(left, right),
                    "<=" => smt::ule(left, right),
                    ">=" => smt::ule(right, left),
                    "<" => smt::ult(left, right),
                    ">" => smt::ult(right, left),
                    _ => unreachable!(),
                });
            }
        }
        Err(self.err("expected a comparison operator"))
    }

    /// An additive expression, plus whether it is *signed*.
    ///
    /// The flag is carried alongside the value because a comparison's meaning
    /// depends on it, and the grammar has no casts or type names to recover it
    /// later. An expression is signed when any name in it is, which is exact:
    /// Rust would reject a mixed-sign arithmetic expression.
    fn parse_expr(&mut self) -> Result<(Var, bool), SpecError> {
        let (mut left, mut sgn) = self.parse_term()?;
        loop {
            let op = if self.eat_op("+") {
                "+"
            } else if self.eat_op("-") {
                "-"
            } else if self.eat_op("|") {
                "|"
            } else if self.eat_op("^") {
                "^"
            } else {
                return Ok((left, sgn));
            };
            let (r, rs) = self.parse_term()?;
            // A literal operand is sized to the other one, exactly as in a
            // comparison. Without this, `ret == a + 5` with a slice length in
            // scope adds an 8-bit `a` to a 64-bit `5`, which `bin_word` reports
            // as ill-formed -- and that poisons every obligation in the run, so
            // the function is undecided for a reason unrelated to its body.
            let (l, r) = self.align_widths(left, r, sgn || rs)?;
            left = match op {
                "+" => smt::add(l, r),
                "-" => smt::sub(l, r),
                "|" => smt::bor(l, r),
                _ => smt::bxor(l, r),
            };
            sgn = sgn || rs;
        }
    }

    fn parse_term(&mut self) -> Result<(Var, bool), SpecError> {
        let (mut left, mut sgn) = self.parse_atom()?;
        loop {
            let op = if self.eat_op("*") {
                "*"
            } else if self.eat_op("&") {
                "&"
            } else {
                return Ok((left, sgn));
            };
            let (r, rs) = self.parse_atom()?;
            // Same width rule as the additive operators: a literal product or
            // mask is sized to the operand it meets.
            let (l, r) = self.align_widths(left, r, sgn || rs)?;
            left = if op == "*" { smt::mul(l, r) } else { smt::band(l, r) };
            sgn = sgn || rs;
        }
    }

    /// An atom, plus whether it is signed.
    fn parse_atom(&mut self) -> Result<(Var, bool), SpecError> {
        // A unary minus is folded into the literal or the name it precedes, so
        // `-10` and `-a` are both expressible. It is a *value* negation, not a
        // subtraction, which is what makes `a >= -10` read the way it looks.
        if self.eat_op("-") {
            let (v, s) = self.parse_atom()?;
            let w = smt::bits(v);
            return Ok((smt::sub(smt::word(0, w), v), s));
        }
        match self.peek().cloned() {
            Some(Tok::Num(n)) => {
                self.pos += 1;
                // A literal is built wide enough to *hold* its own value, and at
                // least as wide as the widest name in scope. Both halves matter:
                //
                // * Holding the value keeps the number exact, so the width
                //   decision can be made later, per use, by `align_widths`.
                //   Building it at the scope's width instead would mask `300` to
                //   `44` for a `u8` and set the engine's ill-formed flag -- the
                //   term would then decide `Unknown`, with no hint that the
                //   contract, not the body, was at fault.
                // * The scope's width keeps the common case (`a <= 5` for a `u32`)
                //   from building a needlessly wide constant.
                let need = (u64::BITS - n.leading_zeros()).max(1) as u8;
                let scope = self
                    .args
                    .values()
                    .chain(self.ret.iter())
                    .map(|v| smt::bits(*v))
                    .max()
                    .unwrap_or(64);
                let w = scope.max(need).min(64);
                Ok((smt::word(n, w), false))
            }
            Some(Tok::Ident(name)) => {
                self.pos += 1;
                if name == "ret" || name == "result" {
                    let v = self.ret.ok_or_else(|| self.err(self.ret_absent))?;
                    return Ok((v, self.ret_signed));
                }
                if name == "true" || name == "false" {
                    // A boolean literal is a one-bit word, so a `bool`-returning
                    // function can write `ensures: ret == false`. It used to be
                    // an error here, which left such contracts unreadable; the
                    // width check then refuses a literal compared against a
                    // wider operand, which is the right refusal.
                    return Ok((smt::word(u64::from(name == "true"), 1), false));
                }
                // `i16::MIN` and friends: the named bound of an integer type,
                // which is how a contract names the value it must exclude. The
                // tokenizer splits `::` into two single `:` operators, so both
                // spellings are recognized.
                let assoc = if let Some((ty, a)) = name.split_once("::") {
                    Some((ty.to_string(), a.to_string()))
                } else if matches!(self.peek(), Some(Tok::Op(o)) if o == ":") {
                    let mut it = self.toks[self.pos..].iter();
                    match (it.next(), it.next(), it.next()) {
                        (Some(Tok::Op(c1)), Some(Tok::Op(c2)), Some(Tok::Ident(a)))
                            if c1 == ":" && c2 == ":" =>
                        {
                            let a = a.clone();
                            self.pos += 3;
                            Some((name.clone(), a))
                        }
                        _ => None,
                    }
                } else {
                    None
                };
                if let Some((ty, a)) = assoc {
                    if let Some((k, w)) = type_bound(&ty, &a) {
                        // The bound is built at the width of the type it *names*,
                        // not at the widest name in scope. `i8::MIN` is the bit
                        // pattern `0x80`, which is exactly 8 bits; widening it to
                        // a 64-bit `128` and then narrowing it back would test
                        // `128 <= i8::MAX` and refuse the constant as out of range
                        // for a signed 8-bit operand -- a refusal of a bound that
                        // is by definition in range.
                        return Ok((smt::word(k, w), ty.starts_with('i')));
                    }
                    return Err(self.err(format!("unknown constant `{ty}::{a}`")));
                }
                let v = self
                    .args
                    .get(&name)
                    .copied()
                    .ok_or_else(|| self.err(format!("unknown name `{name}` (not an argument)")))?;
                let s = self.is_signed_name(&name);
                Ok((v, s))
            }
            Some(Tok::Op(o)) if o == "(" => {
                self.pos += 1;
                // A parenthesized *arithmetic* expression is fine; only a
                // parenthesized predicate is refused, and that is caught by the
                // grammar because `parse_expr` cannot consume `&&`.
                let (v, s) = self.parse_expr()?;
                if !self.eat_op(")") {
                    return Err(self.err("missing `)`"));
                }
                Ok((v, s))
            }
            Some(t) => Err(self.err(format!("unexpected token {t:?}"))),
            None => Err(self.err("unexpected end of contract")),
        }
    }
}

/// Pull the struct name out of a `pub struct Name {` head line.
///
/// Only a *braced* struct is recognised. A tuple struct or a unit struct has no
/// named fields to project, so reading it as a struct with no fields would turn a
/// contract naming `.0` into an "unknown field" refusal rather than a "this shape
/// is not modelled" one — the same outcome, and no false layout.
fn struct_head(line: &str) -> Option<String> {
    let t = line.trim_start_matches("pub(crate) ").trim_start_matches("pub ").trim();
    let rest = t.strip_prefix("struct ")?;
    // Only a brace body on this line is a named-field struct.
    if !rest.contains('{') {
        return None;
    }
    let name = rest.split(|c: char| c == '{' || c == '<' || c.is_whitespace()).next()?;
    if name.is_empty() {
        return None;
    }
    Some(name.to_string())
}

/// Pull `(field, type)` out of one line of a struct body.
///
/// The line looks like `pub lo: u8,` or `lo: u8,`. A line that is not a
/// `name: type` pair (a nested item, a comment, an attribute) is skipped, so an
/// unexpected shape loses a field rather than inventing one — and a lost field
/// makes a contract naming it a refusal, which is the safe direction.
fn struct_field(line: &str) -> Option<(String, String)> {
    let t = line.trim();
    if t.is_empty() || t.starts_with("//") || t.starts_with('#') {
        return None;
    }
    let t = t.trim_start_matches("pub(crate) ").trim_start_matches("pub ").trim();
    let (name, ty) = t.split_once(':')?;
    let name = name.trim();
    if name.is_empty() || !name.chars().all(|c| c.is_alphanumeric() || c == '_') {
        return None;
    }
    // Strip a trailing comma and any `#[...]` attribute tail.
    let ty = ty.split(',').next().unwrap_or(ty).trim();
    if ty.is_empty() {
        return None;
    }
    Some((name.to_string(), ty.to_string()))
}

/// Bind every field of every struct-typed argument to a symbolic variable.
///
/// A struct argument has no width of its own (`Ty::Other("Config")`), so it gets
/// no variable in [`arg_vars`] and a contract that names it directly is refused.
/// Its *fields* do have widths, and those are what a contract wants to talk
/// about. Each field becomes its own symbolic input, so `c.lo` and `c.hi` are
/// independent — which is the honest model: the frontend has no way to know the
/// caller's invariant relating them, so assuming one would be unsound.
///
/// The struct's layout comes from `structs`, read from the same source as the
/// contract. A struct that is not there yields no bindings, and a contract naming
/// one of its fields is then refused by the parser as an unknown name.
pub fn field_env(
    f: &crate::mir::parse::MirFn,
    structs: &BTreeMap<String, StructDef>,
) -> FieldEnv {
    // `base` is one past the highest local the function declares. Every local is
    // seeded at its own index before any field variable is read, so starting here
    // keeps the two index spaces disjoint for any function, not just a small one.
    let mut env =
        FieldEnv { base: f.locals.keys().max().map(|m| m + 1).unwrap_or(0), ..Default::default() };
    // Every source name in scope, recorded before any binding is generated: the
    // mangled names are checked against this set, so a generated binding can
    // never shadow an argument of the same name.
    for &l in &f.arg_locals {
        env.declared.insert(f.name_of(l));
    }
    for &l in &f.arg_locals {
        let Some(ty) = f.ty_of(l) else { continue };
        // A reference to a struct is read through: `&Config` and `Config` have the
        // same fields, and the executor treats `*_1` as `_1`.
        let base = match ty {
            Ty::Ref(inner) => inner.as_ref(),
            other => other,
        };
        let arg = f.name_of(l);
        // A slice argument: `&[u8]`. Its length is a symbolic input, and its
        // elements are bound on demand (by `bind_index_refs` for the contract and
        // by the executor for the body).
        if let Ty::Slice(elem) = base {
            if let Some(w) = elem.width() {
                env.bind_indexed_len(l, &arg, w);
            }
            continue;
        }
        // An array argument: `[u8; 4]`. Its length is the constant in its type,
        // so unlike a slice there is nothing for the caller to choose; the
        // elements are still distinct inputs per index.
        if let Ty::Array(elem, n) = base {
            if let Some(w) = elem.width() {
                env.bind_array_len(l, &arg, w, *n);
            }
            continue;
        }
        let Ty::Other(name) = base else { continue };
        // Recorded whether or not a layout was found, so a contract naming a field
        // gets a message about the field even when the struct's definition was not
        // readable.
        env.declare_arg(&arg);
        let Some(def) = structs.get(name) else { continue };
        for (i, (fname, fty)) in def.fields.iter().enumerate() {
            env.bind(l, &arg, fname, i as u32, fty);
        }
    }
    env
}

/// The argument names whose declared type is signed, for comparison signedness.
pub fn signed_args(f: &crate::mir::parse::MirFn) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    for &l in &f.arg_locals {
        if f.ty_of(l).map(|t| t.is_signed()).unwrap_or(false) {
            out.insert(f.name_of(l));
        }
    }
    out
}

/// `MIN` / `MAX` for an integer type name, as a bit pattern at that type's width.
///
/// A contract says `a != i16::MIN`, and the parser has no way to look the value
/// up except here. Returning `None` for an unknown type keeps an unrecognized
/// name a refusal rather than a zero.
fn type_bound(ty: &str, assoc: &str) -> Option<(u64, u8)> {
    let signed = ty.starts_with('i');
    let unsigned = ty.starts_with('u');
    if !signed && !unsigned {
        return None;
    }
    let bits: u32 = match ty {
        "i8" | "u8" => 8,
        "i16" | "u16" => 16,
        "i32" | "u32" => 32,
        "i64" | "u64" => 64,
        "isize" | "usize" => 64,
        _ => return None,
    };
    // The value is the bit pattern at the named type's own width, which is what
    // lets `i8::MIN` be `0x80` rather than an out-of-range 64-bit `128`.
    let v = match assoc {
        "MAX" if signed => (1u64 << (bits - 1)) - 1,
        "MAX" => {
            if bits == 64 {
                u64::MAX
            } else {
                (1u64 << bits) - 1
            }
        }
        // `MIN` for a signed type is the most negative value, which as a bit
        // pattern is the top bit alone.
        "MIN" if signed => 1u64 << (bits - 1),
        "MIN" => 0,
        _ => return None,
    };
    Some((v, bits as u8))
}

/// The argument names and widths of a function, in declaration order, as they
/// appear in the MIR dump.
pub fn arg_vars(f: &crate::mir::parse::MirFn) -> BTreeMap<String, Var> {
    let mut out = BTreeMap::new();
    for &l in &f.arg_locals {
        let ty = f.ty_of(l).cloned().unwrap_or(Ty::Other("?".into()));
        if let Some(w) = ty.width() {
            out.insert(f.name_of(l), smt::var_named(l, w));
        }
    }
    out
}
