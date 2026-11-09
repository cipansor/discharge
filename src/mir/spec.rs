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

use crate::mir::parse::{split_top_level, Const, Ty, USIZE_WIDTH};
use crate::smt::{self, Pred, Var};

/// How long an array may be before a symbolic subscript is refused.
///
/// `a[i]` is modelled as an ite chain over the array's whole domain, so the cost
/// is linear in the length. A bound keeps a very large array from turning a
/// contract into a term the solver cannot handle; past it the subscript is
/// refused rather than silently approximated.
pub const MAX_INDEX_CHAIN: u64 = 64;

/// The bound a symbolic subscript's ite chain is valid under.
///
/// The chain is built by enumerating a *finite* range and selecting the element
/// whose index matches. An array's range is its type length, a constant. A
/// slice's length is a symbolic input, so its range is the length variable --
/// but the chain can only enumerate a bounded number of steps, so a slice's
/// chain is valid only where the length is within that bound.
///
/// Carrying the bound as a type rather than as a `u64` is what keeps the two
/// from being confused: a slice has no constant to put in the `u64`, and writing
/// one would be a guess about the caller.
#[derive(Clone, Copy, Debug)]
pub enum IndexBound {
    /// An array: the length is in the type, so the bound is that constant, and
    /// `i < n` is the whole obligation.
    Const(u64),
    /// A slice: the length is a symbolic input, and the chain enumerates
    /// `0..MAX_INDEX_CHAIN`, so the chain is exact only where
    /// `len <= MAX_INDEX_CHAIN`. The obligation is that *and* `i < len`.
    ///
    /// The length bound is what makes the chain exact for *every* index in the
    /// slice rather than only for the index the contract named: with
    /// `i < len <= MAX` any index the body reads is one the enumeration covers.
    /// Bounding the index alone would leave a read at some other index falling
    /// through the chain to a wrong value.
    Len(Var),
}

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
    /// Raw text of each `decreases:` clause, in source order.
    ///
    /// A recursive function needs a measure that strictly decreases at each
    /// recursive call, or the induction has no well-founded basis and assuming the
    /// callee's contract at the recursive call would assume the conclusion. The
    /// clause is what licenses that assumption: the call is sound only when the
    /// measure is smaller at the call than at entry *and* stays non-negative.
    ///
    /// It is not inferred. A guessed measure is a guessed proof, which is the same
    /// reason a loop invariant is supplied rather than synthesised. A function with
    /// no `decreases` that calls itself is refused at the call rather than assumed.
    ///
    /// More than one is refused, like more than one `invariant:`, because two
    /// measures could disagree and picking either would be guessing which proof the
    /// source asked for.
    pub decreases: Vec<String>,
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
    /// Enum layouts read from the same source, keyed by enum name.
    ///
    /// An enum argument has no width of its own, but its *tag* does, and the
    /// `switchInt` a `match` lowers to compares that tag against the variant
    /// indices. Those indices are not in the MIR dump -- it prints `_2 =
    /// discriminant(_1)` and `switchInt(move _2) -> [0: bb4, 1: bb3, 2: bb2]`,
    /// which is a number per arm and no name at all. So the same reasoning as
    /// [`Specs::structs`] applies: the layout has to come from the source, and a
    /// contract naming a variant is refused rather than guessed at when it is not
    /// there.
    pub enums: BTreeMap<String, EnumDef>,
    /// The names of `const` items declared at *module* scope (outside any `fn`
    /// body), read from the source.
    ///
    /// The MIR dump prints a crate-level `const` and a function-local one
    /// identically (`const L: u8 = const 3_u8;`), so the definition alone cannot
    /// say which it is. A crate-level item is *used* bare (`const L`) while a
    /// local one is used qualified (`const f::L`), and that use site is the usual
    /// tell -- but a crate-level item a contract names and the body never uses has
    /// no use site at all, so it would be dropped and the contract left
    /// unreadable. This set is the second tell: a name declared here is
    /// module-scoped and its bare definition must be kept. See
    /// [`crate_level_consts`] and `parse::parse_program_scoped`.
    pub crate_consts: BTreeSet<String>,
}

/// An enum's variants, in declaration order.
///
/// The *discriminant* is stored per variant, not taken from the vector position.
/// rustc numbers variants by declaration order *unless* the source gives an
/// explicit value (`B = 3`), and then a later variant's discriminant is neither
/// its position nor its predecessor's value. A reader numbering by position puts
/// a contract naming `E::C` on the wrong tag, and -- because the `match` arm
/// constants come from rustc, not from this reader -- the contract and the arm
/// then disagree about which variant a value is.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct EnumDef {
    /// `(name, payload types, discriminant)` per variant, in declaration order.
    /// A unit variant has an empty payload; a struct variant records no payload
    /// types, so a contract naming one of its fields is refused rather than bound
    /// to the wrong thing.
    pub variants: Vec<(String, Vec<Ty>, u64)>,
}

impl EnumDef {
    /// The discriminant for `name`, or `None` if the enum has no such variant.
    pub fn index_of(&self, name: &str) -> Option<u64> {
        self.variants.iter().find(|(n, _, _)| n == name).map(|(_, _, d)| *d)
    }

    /// The width that can hold every discriminant, and no more.
    ///
    /// A tag's domain is the set of discriminants, so the width is the largest
    /// one's. Taking the variant *count*'s width instead is only the same thing
    /// when the discriminants are `0..count`, which an explicit discriminant
    /// breaks: `A, B = 3, C` needs three bits for the tag `4`, not the two bits a
    /// count of three would give.
    pub fn tag_width(&self) -> u8 {
        let max = self.variants.iter().map(|(_, _, d)| *d).max().unwrap_or(0);
        (64 - max.leading_zeros()).max(1) as u8
    }

    /// The predicate that a value of this enum's tag is one of its variants.
    ///
    /// This is what the run may *assume* about a symbolic tag, and it has to be
    /// exact rather than a count. `tag < arity` is a fact about the type only when
    /// the discriminants are consecutive from zero; with `A, B = 3, C` the real
    /// tags are `0`, `3` and `4`, and `tag < 3` would exclude `4` -- excluding a
    /// value the type admits. An assumed bound that is *false* for a real input is
    /// the unsound direction: it can make a proof vacuous. The disjunction of
    /// equalities is exact for any numbering.
    pub fn tag_bound(&self, tag: Var) -> Pred {
        let mut acc: Option<Pred> = None;
        for (_, _, d) in &self.variants {
            let p = smt::eq_const(tag, *d);
            acc = Some(match acc {
                None => p,
                Some(prev) => smt::or(prev, p),
            });
        }
        acc.unwrap_or_else(|| smt::truth(false))
    }
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

    /// The contract for a function whose MIR name is `name`, resolved the way the
    /// frontend resolves the *body*: an exact match first, then a unique match on
    /// the last `::` segment.
    ///
    /// The dump names an inherent method `<impl at FILE:L:C: L:C>::f`, while the
    /// source's contract is keyed by the bare `f` (the scanner records the
    /// identifier after `fn`, and a key is therefore never itself qualified).
    /// Matching only the exact name left every method's contract unresolved, and an
    /// unresolved contract is not a refusal: `verify_function` builds its
    /// precondition and postcondition from `contract`, so a missing one means
    /// `requires: true` and *no* `ensures` -- a method with a false postcondition
    /// was reported verified with zero obligations, the body never checked at all.
    ///
    /// A tail that no key matches stays `None`; because keys are bare, a tail
    /// match is unique by construction.
    pub fn resolve(&self, name: &str) -> Option<&FnContract> {
        if let Some(c) = self.by_fn.get(name) {
            return Some(c);
        }
        let tail = name.rsplit("::").next()?;
        self.by_fn.get(tail)
    }
}

/// The names of `const` items declared at module scope -- outside any brace.
///
/// The MIR dump prints a crate-level `const` and a function-local one
/// identically, so the definition alone cannot say which it is; the use site
/// (`const L` bare vs `const f::L` qualified) is the usual tell. A crate-level
/// constant that a *contract* names but the body never uses has no use site at
/// all, so that tell is silent and the definition would be dropped, leaving the
/// contract unreadable. The source, though, says plainly whether the item is
/// inside a `fn` body: a crate-level item sits at brace depth zero.
///
/// The scan tracks brace depth over the whole file, ignoring braces inside string
/// and character literals and inside comments, and records the name of every
/// `const NAME: …` seen at depth zero. It deliberately does not try to be a Rust
/// parser: a `const` generic parameter or an associated constant inside an `impl`
/// is at depth > 0 and so is not recorded, which is the safe direction (recording
/// too much would re-open the local-leak false proof).
pub fn crate_level_consts(source: &str) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    let mut depth: i32 = 0;
    let mut in_block_comment = false;
    for raw in source.lines() {
        let mut line = raw;
        // Block comments can span lines; a brace inside one is not code.
        loop {
            if in_block_comment {
                match line.find("*/") {
                    Some(i) => {
                        in_block_comment = false;
                        line = &line[i + 2..];
                    }
                    None => line = "",
                }
            } else if let Some(i) = line.find("/*") {
                in_block_comment = true;
                line = &line[i + 2..];
            } else {
                break;
            }
        }
        // A `const NAME: …` at depth zero is a crate-level item. The name is read
        // before the braces on the line are counted, so `const L: u8 = 3;` is
        // caught while a `const` inside a `fn` body (depth > 0) is not.
        if depth == 0 {
            let t = line.trim_start();
            let t = t.strip_prefix("pub(crate) ").or_else(|| t.strip_prefix("pub ")).unwrap_or(t);
            if let Some(after) = t.strip_prefix("const ") {
                let name: String = after
                    .chars()
                    .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
                    .collect();
                let plain =
                    name.chars().next().is_some_and(|c| c.is_ascii_alphabetic() || c == '_');
                if plain && after[name.len()..].trim_start().starts_with(':') {
                    out.insert(name);
                }
            }
        }
        // Count braces outside strings, chars and line comments.
        let bytes = line.as_bytes();
        let mut i = 0;
        while i < bytes.len() {
            match bytes[i] {
                b'/' if bytes.get(i + 1) == Some(&b'/') => break,
                b'"' => {
                    i += 1;
                    while i < bytes.len() && bytes[i] != b'"' {
                        if bytes[i] == b'\\' {
                            i += 1;
                        }
                        i += 1;
                    }
                }
                b'\'' => {
                    i += 1;
                    while i < bytes.len() && bytes[i] != b'\'' {
                        if bytes[i] == b'\\' {
                            i += 1;
                        }
                        i += 1;
                    }
                }
                b'{' => depth += 1,
                b'}' => depth -= 1,
                _ => {}
            }
            i += 1;
        }
    }
    out
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
    // Which `const` items are declared at the crate root, before any brace opens.
    // The dump cannot tell a crate-level `const` from a function-local one, so a
    // contract that names a crate-level constant the body never uses would
    // otherwise lose its definition and go unreadable. See
    // [`Specs::crate_consts`].
    specs.crate_consts = crate_level_consts(source);

    // Struct layouts, read in the same pass. The MIR dump names a struct
    // (`_1: &Config`) but never prints its fields, so a contract like
    // `c.lo <= c.hi` has no way to learn that `lo` is field 0 of width 8 unless
    // the layout is read here.
    let mut cur_struct: Option<(String, StructDef)> = None;
    // Enum layouts, read in the same pass. An enum body is a list of variants
    // rather than a list of fields, so it needs its own cursor; a struct and an
    // enum cannot be open at once, so the two cursors never interleave.
    let mut cur_enum: Option<(String, EnumDef)> = None;

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
        // Inside an enum body: read variants until the closing brace.
        if cur_enum.is_some() {
            if line.starts_with('}') {
                let (name, def) = cur_enum.take().unwrap();
                specs.enums.insert(name, def);
                continue;
            }
            match enum_variant(line) {
                VariantLine::Variant { name: vname, payload, explicit } => {
                    if let Some((_, def)) = cur_enum.as_mut() {
                        push_variant(def, vname, payload, explicit);
                    }
                }
                VariantLine::NotAVariant => {}
                // An explicit discriminant this reader cannot evaluate: the whole
                // layout is refused, because dropping the variant would shift
                // every later discriminant and guessing one would put a contract
                // on the wrong tag. Removing the enum makes a contract naming any
                // of its variants a refusal, which is the safe direction.
                VariantLine::UnreadableDiscriminant => {
                    cur_enum = None;
                }
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
        if let Some(head) = struct_head(line) {
            // A doc comment above a struct documents the struct, not a function.
            // The pending contract is dropped here for the same reason the
            // catch-all below drops it: a contract must attach to the item it was
            // written above. Carrying it to the next `fn` was a false proof when
            // the leaked `requires` was satisfiable.
            pending = FnContract::default();
            match head {
                // A tuple struct carries its fields in the head, numbered by
                // position, so there is no body to cursor over.
                StructHead::Tuple { name, fields } => {
                    let mut def = StructDef::default();
                    for (fname, fty) in fields {
                        def.fields.push((fname, Ty::parse(&fty)));
                    }
                    specs.structs.insert(name, def);
                }
                StructHead::Named { name, closed_inline } => {
                    // A one-line body is complete already; opening a cursor would run
                    // past the closing brace and consume every following line -- contracts
                    // and functions included -- as fields, so the functions would silently
                    // disappear from the spec table. Read the fields out of the head line
                    // instead, exactly as the enum path reads an `Inline` body.
                    if closed_inline {
                        let t =
                            line.trim_start_matches("pub(crate) ").trim_start_matches("pub ").trim();
                        let mut def = StructDef::default();
                        if let Some(open) = t.find('{') {
                            if let Some(close) = t[open + 1..].rfind('}') {
                                for f in split_top_level(&t[open + 1..open + 1 + close], ',') {
                                    if let Some((fname, fty)) = struct_field(&f) {
                                        def.fields.push((fname, Ty::parse(&fty)));
                                    }
                                }
                            }
                        }
                        specs.structs.insert(name, def);
                    } else {
                        cur_struct = Some((name, StructDef::default()));
                    }
                }
            }
            continue;
        }
        if let Some((name, head)) = enum_head(line) {
            // Same as the struct head: a doc comment above an enum is the enum's,
            // not a function's, so the pending contract is dropped rather than
            // carried to the next `fn`.
            pending = FnContract::default();
            match head {
                // A one-line body is complete already; it needs no cursor.
                EnumHead::Inline(variants) => {
                    specs.enums.insert(name, EnumDef { variants });
                }
                EnumHead::MultiLine => cur_enum = Some((name, EnumDef::default())),
                // The body was refused *and* closed on this line. Opening a
                // cursor here would run past the brace and consume every
                // following line -- contracts included -- as enum contents, so
                // the layout is dropped and the cursor stays shut.
                EnumHead::Refused => {}
            }
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
            } else if let Some(r) = t.strip_prefix("decreases:") {
                pending.decreases.push(r.trim().to_string());
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
                || !pending.decreases.is_empty()
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

/// An array-typed field a contract may subscript: `o.a` in `o.a[0]`. The chain is the MIR
/// projection from the argument's base local to the array, so the executor can key the
/// element by the same path the body's write lands on.
#[derive(Clone, Debug)]
pub struct PathElem {
    /// The argument name, used to build the element's mangled variable name.
    pub arg: String,
    /// The local the argument is bound to.
    pub local: u32,
    /// The field chain from the local to the array (`[0]` for the first field).
    pub chain: Vec<u32>,
    /// The element width in bits.
    pub elem_w: u8,
    /// Whether the element is signed.
    pub elem_signed: bool,
    /// The array's length, so an index past it is refused rather than bound.
    pub len: u64,
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
    /// A *nested* field path, keyed by the exact source spelling the contract
    /// writes (`o.i.v`) → the mangled name it is rewritten to.
    ///
    /// A single field is a property of the argument (`arg.field`), but a nested
    /// path is a property of the *path*: `o.i.v` and `o.i.w` share the outer
    /// projection `o.i` and differ only in the inner field. So the binding is
    /// keyed by the whole dotted spelling, and the rewrite matches the longest
    /// prefix that exists. The key is the source spelling because that is what the
    /// scanner has in hand; the value is the variable the path names, seeded into
    /// the executor's `nested` store under the same projection chain, so the
    /// contract's `o.i.v` and the body's `(((*_1).0).0)` are one input rather than
    /// two that look alike.
    pub nested_paths: BTreeMap<String, String>,
    /// The argument names that are aggregates *with a readable layout*, used only
    /// to *diagnose* a nested path that walks off the layout: `o.i` where `i` is a
    /// scalar, or `o.nope.v`. A name here that is followed by a dotted path with no
    /// binding gets a message naming the segment rather than a parser error about
    /// the `.` it cannot reduce.
    pub aggregate_args: BTreeSet<String>,
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
    /// The `bool` is the field's signedness, carried here so the executor can
    /// build a `Val::Sym` that *knows* its sign. A seed without one would force
    /// the executor to guess, which is the bug class this closes.
    pub seeds: Vec<(u32, u32, Var, bool)>,
    /// `(local, projection chain, variable, signed)` for each *nested* path a
    /// contract names, so the executor's nested store holds the same variable the
    /// contract's `o.i.v` was rewritten to.
    ///
    /// The chain is the MIR projection from the argument's base local: for `o.i.v`
    /// it is `[Field(0), Field(0)]`, and the executor seeds `((local, 0), 0)`. The
    /// chain is stored rather than a single index because a nested path is a walk,
    /// not a field: the executor has to place the value at the *end* of the walk,
    /// and the walk's shape is what makes `o.i.v` a different input from `o.j.v`.
    pub nested_seeds: Vec<(u32, Vec<u32>, Var, bool)>,
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
    pub len_seeds: Vec<(u32, Var, u8, bool)>,
    /// `(local, index, element variable)` for each slice or array element the
    /// contract names. The body's `(*_1)[0]` reads the same variable, so `xs[0]`
    /// in a contract and `xs[0]` in the body are one value, not two that look
    /// alike.
    pub elem_seeds: Vec<(u32, u64, Var, bool)>,
    /// `(local, field chain, index, variable, signed)` for each element of an array
    /// reached through a *field path* (`o.a[0]`) that a contract names.
    ///
    /// Separate from [`elem_seeds`](Self::elem_seeds) because the executor keys these by the
    /// whole path: `o.a[0]` and `o.b[0]` are different words, and a store keyed by the local
    /// and index alone would collide them.
    pub path_elem_seeds: Vec<(u32, Vec<u32>, u64, Var, bool)>,
    /// `path -> array-field layout` for every array-typed field a contract may subscript
    /// (`o.a` in `o.a[0]`): the argument name, the local, the field chain to the array, the
    /// element width and signedness, and the array's length.
    pub path_elem_types: BTreeMap<String, PathElem>,
    /// `(local, tag variable, tag width, discriminants)` for each enum-typed
    /// argument.
    ///
    /// An enum argument has no bit width of its own, but its *tag* does, and the
    /// tag is the only thing a contract can say about an enum without naming a
    /// variant. It is a symbolic input whose domain is the set of variant
    /// discriminants — a fact about the type, so the run may assume it. The
    /// discriminants travel with the seed rather than a variant count, because
    /// `tag < count` is only the same domain when the numbering is `0..count`,
    /// which an explicit discriminant (`B = 3`) breaks. Seeding the tag here is
    /// what makes the contract's `m` and the body's `discriminant(_1)` one
    /// variable.
    pub tag_seeds: Vec<(u32, Var, u8, Vec<u64>)>,
    /// `(local, variant, variable, width, signed)` for each variant payload.
    ///
    /// A payload is a symbolic input like any other: the frontend cannot know what
    /// the caller put in it, so assuming a relation would be unsound. Seeding it
    /// means the body's `((_1 as Data).0)` and a contract's `m.Data` name one
    /// variable rather than two that look alike.
    pub payload_seeds: Vec<(u32, u64, Var, u8, bool)>,
    /// `Enum::Variant` → `(discriminant, tag width)`, so a contract can write
    /// `m == Mode::Idle` and have it mean the tag equals that variant's index.
    /// A name not in here is refused, which keeps a misspelled variant from being
    /// read as an unrelated integer.
    pub variant_consts: BTreeMap<String, (u64, u8)>,
    /// Named `const` items, name → the value rustc printed for them.
    ///
    /// A contract may name a constant the way the body does (`requires: x <=
    /// LIMIT`), and the name has to resolve to the same value the body reads at its
    /// use site. This is the *same table* the executor folds a body's `const LIMIT`
    /// from (`MirProgram::consts`), so the contract and the body cannot disagree:
    /// there is one value, read once by rustc.
    ///
    /// A name that is *not* here is refused rather than guessed at, which keeps a
    /// misspelled constant from being read as an argument that does not exist, or
    /// as zero. Only a constant whose printed body is a literal is in the table, so
    /// a constant built by an expression is refused too -- its value is in its own
    /// body, not in a declaration the reader can fold.
    pub consts: BTreeMap<String, Const>,
    /// `arg.Variant` → the mangled payload name, so a contract can name a payload
    /// the way the body's downcast reads it.
    pub payload_paths: BTreeMap<String, String>,
    /// The names of enum-typed arguments, for diagnostics: a contract naming
    /// `m.Nope` where `Nope` is not a variant gets a message about the variant.
    pub enum_args: BTreeSet<String>,
    /// Indexed arguments (slices and arrays): name → (local, element width, the
    /// array's fixed length if it is one), so a contract's `xs.len()` and `xs[0]`
    /// can be bound without the IR's `Ty` in hand.
    ///
    /// The length is `Some(n)` for an array and `None` for a slice, which is what
    /// lets a contract naming `a[9]` on a `[u8; 4]` be refused as out of range
    /// rather than bound to a fresh variable for an element that does not exist.
    indexed: BTreeMap<String, (u32, u8, Option<u64>, bool)>,
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
    /// `arg -> every index spelling` for an array a contract subscripts
    /// symbolically, so the rewrite can tell `a[i]` (which has a chain) from
    /// `a[j]` (which does not) instead of rewriting both to the same chain.
    ///
    /// A *set*, not one name: one index variable can be spelled more than once —
    /// `a[i]` and `a[k]` where `let k = i`, or the same name twice — and every
    /// spelling of the bound index names the same element, so every spelling has
    /// to rewrite to the same chain. Keeping only the first left the second
    /// subscript unrewritten and the whole contract unreadable, which skipped a
    /// function that should have verified.
    sym_index_names: BTreeMap<String, BTreeSet<String>>,
    /// `arg -> the ite chain` for an array a contract subscripts symbolically.
    ///
    /// Built once by [`bind_sym_index`](Self::bind_sym_index) from the element
    /// variables, so the rewrite can replace `a[i]` with a *name* the parser
    /// resolves, and the chain is the same term every time it is used. An array
    /// argument has no variable of its own (its type has no bit width), so
    /// without this the parser would refuse `a` as an unknown name.
    sym_chain: BTreeMap<String, Var>,
    /// `arg -> the bound its chain is valid under` for an array or slice a
    /// contract subscripts symbolically.
    ///
    /// An array's bound is its type length; a slice's is its length *variable*,
    /// which is symbolic, so the chain is exact only under `len <=
    /// MAX_INDEX_CHAIN`. The caller turns this into the obligations the
    /// precondition must establish, and the executor takes the same bound so its
    /// own chain covers the same range the contract's does.
    sym_bound: BTreeMap<String, IndexBound>,
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
    /// An environment carrying only a `const` table, for evaluating a contract
    /// that names a constant but binds no fields.
    ///
    /// A constant's value does not depend on the call site, so the table is the
    /// entry state's, not a fresh one; this is the constructor for the places
    /// (a recursive call) that need the constants without the field bindings.
    pub fn with_consts(consts: BTreeMap<String, Const>) -> FieldEnv {
        FieldEnv { consts, ..FieldEnv::default() }
    }

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

    /// `bind` by width and signedness, for callers outside the crate that
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
        self.seeds.push((local, index, v, signed));
        if signed {
            self.signed.insert(mangled.clone());
        }
        self.paths.insert(format!("{arg}.{field}"), mangled);
        self.known_args.insert(arg.to_string());
        Some(())
    }

    /// Bind a *nested* field path (`o.i.v`) to a fresh variable of the leaf
    /// field's width and signedness.
    ///
    /// `chain` is the MIR projection from the argument's base local to the leaf:
    /// for `o.i.v` it is `[0, 0]`, and the executor seeds the value at
    /// `((local, 0), 0)`. The whole chain is the identity of the input, because
    /// `o.i.v` and `o.j.v` are different words: the mangled name is derived from
    /// the chain, not from the leaf name, so the two cannot collide even though
    /// both end in `.v`.
    ///
    /// Every intermediate segment must itself be a *struct or tuple* with a
    /// readable layout. A segment that is a scalar, a reference, or an unknown
    /// type stops the walk, and the path is refused -- binding a fabricated word
    /// for `o.i` where `i` is a `u8` would let a contract about a field that does
    /// not exist be proved.
    pub fn bind_nested(&mut self, local: u32, arg: &str, path: &str, chain: &[u32], ty: &Ty) -> Option<()> {
        let w = ty.width()?;
        let slot = self.base + self.next_slot;
        if slot as usize >= crate::smt::MAX_VARS {
            return None;
        }
        // The mangled name is the chain, so `o.i.v` and `o.j.v` differ even though
        // they share the leaf name. `__n` marks it as nested, keeping it distinct
        // from the single-field `__f` form for the same local.
        let mangled = format!(
            "{arg}__n{}",
            chain.iter().map(|i| i.to_string()).collect::<Vec<_>>().join("_")
        );
        if !self.name_is_free(&mangled) {
            return None;
        }
        self.next_slot += 1;
        let v = smt::var_named(slot, w);
        self.vars.insert(mangled.clone(), v);
        if ty.is_signed() {
            self.signed.insert(mangled.clone());
        }
        self.nested_seeds.push((local, chain.to_vec(), v, ty.is_signed()));
        self.nested_paths.insert(path.to_string(), mangled);
        self.aggregate_args.insert(arg.to_string());
        self.known_args.insert(arg.to_string());
        Some(())
    }

    /// Bind an element of an array reached through a field path, `o.a[k]`.
    ///
    /// The key is the whole path -- the local, the field chain, the index -- so `o.a[0]` and
    /// `o.b[0]` are different words and cannot be confused. The mangled name embeds the chain,
    /// which is what keeps the two apart. An index past the array's declared length is refused
    /// rather than bound: the element does not exist, and a fresh variable there would make a
    /// meaningless precondition look real.
    pub fn bind_path_elem(&mut self, path: &str, index: u64) -> Option<Var> {
        let PathElem { arg, local, chain, elem_w, elem_signed, len } =
            self.path_elem_types.get(path)?.clone();
        if !(1..=64).contains(&elem_w) || index >= len {
            return None;
        }
        // The mangled name is built from the *chain*, not the dotted path: a `.` in a
        // generated name would be read by the parser as a field access, and the rewrite
        // hands the name to the parser verbatim. The chain keeps `x.a[0]` and `x.b[0]`
        // distinct even though both end in `.a`/`.b` of the same local.
        let mangled = format!(
            "{arg}__pe{}_e{index}",
            chain.iter().map(|i| i.to_string()).collect::<Vec<_>>().join("_")
        );
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
        if elem_signed {
            self.signed.insert(mangled.clone());
        }
        self.paths.insert(format!("{path}[{index}]"), mangled);
        self.path_elem_seeds.push((local, chain, index, v, elem_signed));
        Some(v)
    }

    /// Bind every nested field path a contract may name on an argument.
    ///
    /// `arg` is the source name, `ty` the argument's type (already read through a
    /// reference), and `structs` the declared layouts. The walk is depth-first over
    /// the fields whose type is itself a struct or tuple with a readable layout, so
    /// `o.i.v` is bound when `o.i` is a struct and `v` is a scalar leaf. A segment
    /// whose type has no layout -- a scalar, a reference, an unknown name -- ends
    /// that branch: the path is not bound, so a contract naming it is *refused*
    /// rather than bound to a fabricated word.
    ///
    /// Only paths of depth >= 2 are bound here: a single field is already bound by
    /// [`bind`](Self::bind), and binding it again under a second name would give one
    /// source field two variables.
    ///
    /// Depth is bounded by the type, not by a constant: a *recursive* type would
    /// make the walk unbounded, so the chain of type names on the current branch is
    /// kept and a type already on it stops the descent. The guard is the branch, not
    /// a global set, so two fields of the same type are both walked.
    pub fn bind_nested_paths(
        &mut self,
        local: u32,
        arg: &str,
        ty: &Ty,
        structs: &BTreeMap<String, StructDef>,
    ) {
        let mut w = NestedWalk { local, arg, structs, on_path: Vec::new() };
        self.walk_nested(&mut w, arg, &[], ty);
    }

    fn walk_nested(
        &mut self,
        w: &mut NestedWalk<'_>,
        prefix: &str,
        chain: &[u32],
        ty: &Ty,
    ) {
        // The fields of this aggregate, in field order, which *is* the MIR index.
        let fields: Vec<(String, Ty)> = match ty {
            Ty::Other(name) => match w.structs.get(name) {
                Some(def) => def.fields.clone(),
                None => return,
            },
            Ty::Tuple(ts) => {
                ts.iter().enumerate().map(|(i, t)| (i.to_string(), t.clone())).collect()
            }
            _ => return,
        };
        if let Ty::Other(name) = ty {
            if w.on_path.iter().any(|n| n == name) {
                return;
            }
            w.on_path.push(name.clone());
        }
        for (index, (fname, fty)) in fields.iter().enumerate() {
            let mut child = chain.to_vec();
            child.push(index as u32);
            let path = format!("{prefix}.{fname}");
            // A leaf with a bit width is the value a contract can compare. An
            // aggregate is *not* bound (it has no single word) but is descended
            // into, so its scalar fields are reachable as deeper paths.
            if child.len() >= 2 && fty.width().is_some() {
                self.bind_nested(w.local, w.arg, &path, &child, fty);
            }
            // An array at any depth is subscriptable: `o.i.a[0]`. The first-level
            // pass only reaches `x.a`, so a nested array is recorded here with the
            // full chain the executor keys its element store by.
            if let Ty::Array(elem, n) = fty {
                if let Some(ew) = elem.width() {
                    self.path_elem_types.insert(
                        path.clone(),
                        PathElem {
                            arg: w.arg.to_string(),
                            local: w.local,
                            chain: child.clone(),
                            elem_w: ew,
                            elem_signed: elem.is_signed(),
                            len: *n,
                        },
                    );
                }
            }
            if matches!(fty, Ty::Other(_) | Ty::Tuple(_)) {
                self.walk_nested(w, &path, &child, fty);
            }
        }
        if matches!(ty, Ty::Other(_)) {
            w.on_path.pop();
        }
    }

    /// Bind an enum-typed argument: its tag, and each variant's payloads.
    ///
    /// The tag is the only thing a contract can compare against a variant, so it
    /// is always bound when the enum's layout is known. The payloads are bound
    /// too, so `m.Data` in a contract names the same input the body's downcast
    /// reads. A payload whose type has no bit width (a nested enum, a reference)
    /// is skipped, and a contract naming it is then refused rather than bound to
    /// a fabricated word.
    ///
    /// The tag's width is the *discriminants'*, not the dump's `isize`: the
    /// `switchInt` compares it against the variant constants, so the width only
    /// has to hold them. Using the discriminants' width keeps the tag and the
    /// payload in a width that `discriminant` reads back consistently.
    pub fn bind_enum(
        &mut self,
        local: u32,
        arg: &str,
        enum_name: &str,
        def: &EnumDef,
    ) -> Option<()> {
        if def.variants.is_empty() {
            return None;
        }
        // The tag needs enough bits for the *largest discriminant*, which an
        // explicit value can push past the variant count: `A, B = 3, C` needs
        // three bits for `4`, not the two a count of three would give.
        let width = def.tag_width();
        let tag_slot = self.base + self.next_slot;
        if tag_slot as usize >= crate::smt::MAX_VARS {
            return None;
        }
        let tag_name = format!("{arg}__tag");
        if !self.name_is_free(&tag_name) {
            return None;
        }
        self.next_slot += 1;
        let tag = smt::var_named(tag_slot, width);
        self.vars.insert(tag_name, tag);
        // The argument's own name is the tag, so `m == Mode::Idle` reads the tag
        // without a projection. Bound after the tag variable exists so the two are
        // the same word.
        self.vars.insert(arg.to_string(), tag);
        // The seeds carry the width and the *discriminant list*, because the
        // executor has to assume exactly the tag's domain -- a disjunction of the
        // real discriminants, not a `0..count` bound.
        let discs: Vec<u64> = def.variants.iter().map(|(_, _, d)| *d).collect();
        self.tag_seeds.push((local, tag, width, discs));
        self.enum_args.insert(arg.to_string());
        for (vname, payload, d) in def.variants.iter() {
            // The variant name is a constant of the tag's width, holding the
            // *discriminant* rustc assigned -- the same number a `match` arm
            // compares against. Numbering by position here is what put a contract
            // and an arm in disagreement.
            self.variant_consts.insert(format!("{enum_name}::{vname}"), (*d, width));
            self.variant_consts.insert(format!("{arg}::{vname}"), (*d, width));
            // A payload: `m.Data` is field 0 of variant `Data`. Only the first
            // payload is bound, because the MIR downcast this frontend models
            // reads `.0`; a second field would need a tuple projection the
            // executor does not carry for payloads.
            let Some(first) = payload.first() else { continue };
            let Some(w) = first.width() else { continue };
            let slot = self.base + self.next_slot;
            if slot as usize >= crate::smt::MAX_VARS {
                continue;
            }
            let mangled = format!("{arg}__v{d}_0");
            if !self.name_is_free(&mangled) {
                continue;
            }
            self.next_slot += 1;
            let v = smt::var_named(slot, w);
            self.vars.insert(mangled.clone(), v);
            // Keyed by the *discriminant*, because that is what a `Downcast`
            // projection carries: the executor stores and reads payloads under the
            // same number, and a positional key would not match a variant after an
            // explicit discriminant.
            self.payload_seeds.push((local, *d, v, w, first.is_signed()));
            if first.is_signed() {
                self.signed.insert(mangled.clone());
            }
            self.payload_paths.insert(format!("{arg}.{vname}"), mangled);
        }
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
    pub fn bind_indexed_len(
        &mut self,
        local: u32,
        arg: &str,
        elem_w: u8,
        elem_signed: bool,
    ) -> Option<Var> {
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
        self.indexed.insert(arg.to_string(), (local, elem_w, None, elem_signed));
        self.len_seeds.push((local, v, elem_w, elem_signed));
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
    pub fn bind_array_len(
        &mut self,
        local: u32,
        arg: &str,
        elem_w: u8,
        elem_signed: bool,
        n: u64,
    ) -> Option<()> {
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
        self.indexed.insert(arg.to_string(), (local, elem_w, Some(n), elem_signed));
        self.len_seeds.push((local, v, elem_w, elem_signed));
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
        let (local, elem_w, fixed_len, elem_signed) = *self.indexed.get(arg)?;
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
        // The element's signedness has to reach the *parser* too, not only the
        // executor's seeds. Every other binding site records it here, and this one
        // did not, so `is_signed_name("xs__e0")` was false for an `i8` element and
        // a contract read `xs[0] < 0` as unsigned -- never true -- which is the
        // exact confusion `signed_slice_element_is_signed` exists to catch. The
        // false reading also refused `xs[0] == i8::MIN` as a signed/unsigned mix
        // once that check was added, so the missing insert showed up twice.
        if elem_signed {
            self.signed.insert(mangled.clone());
        }
        self.paths.insert(format!("{arg}[{index}]"), mangled);
        self.elem_seeds.push((local, index, v, elem_signed));
        Some(v)
    }

    /// Bind a symbolic index: the index variable, and every element of the array
    /// or slice, so the parser can build the ite chain from bindings that already
    /// exist.
    ///
    /// The index is a fresh input (whatever the caller passed) and the elements
    /// are the same ones a literal `a[k]` would bind, so `a[i]` and `a[0]` share
    /// their element variables and the two cannot disagree. The *range* is not
    /// checked here: the bound is recorded in `sym_bound`, and the contract is
    /// refused unless the precondition establishes it.
    ///
    /// The range enumerated is [`IndexBound::Const`] for an array (its type
    /// length) and [`IndexBound::Len`] for a slice (its length variable, which is
    /// symbolic), so a slice's chain enumerates `0..MAX_INDEX_CHAIN` and is exact
    /// only where the length is within that.
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
        bound: IndexBound,
        index_name: &str,
        index: Var,
    ) -> Option<Var> {
        if !(1..=64).contains(&elem_w) {
            return None;
        }
        // A slice has no length in its type, so the chain enumerates
        // `0..MAX_INDEX_CHAIN` and is exact only where the length is within that.
        // The obligation is recorded in `sym_bound` and established by the caller.
        let steps = match bound {
            IndexBound::Const(n) if n <= MAX_INDEX_CHAIN => n,
            IndexBound::Const(_) => return None,
            IndexBound::Len(_) => MAX_INDEX_CHAIN,
        };
        if let Some(v) = self.sym_index.get(arg) {
            // The same array subscripted by two different indices has no single
            // chain to rewrite to. Refusing keeps the second subscript a refusal
            // rather than silently reusing the first chain.
            //
            // The comparison is on the *bound index variable*, not on the name, so
            // two spellings of one index (`a[i]` and `a[k]` where `let k = i`)
            // share a chain rather than colliding. That is what makes an alias a
            // rename and nothing more.
            if *v != index {
                return None;
            }
            // The same index under a new spelling: it names the same element, so
            // record the spelling and let the rewrite replace it too. Returning
            // early here left the second spelling unrewritten, and the parser then
            // refused the whole contract as an unknown name.
            self.sym_index_names.entry(arg.to_string()).or_default().insert(index_name.to_string());
            return Some(*v);
        }
        // The elements first, so the chain has all of them to build from.
        let mut elems = Vec::with_capacity(steps as usize);
        for k in 0..steps {
            elems.push(self.bind_indexed_elem(arg, k)?);
        }
        let v = index;
        self.sym_index.insert(arg.to_string(), v);
        self.sym_index_names.entry(arg.to_string()).or_default().insert(index_name.to_string());
        // `ite(i == 0, e0, ite(i == 1, e1, ... ite(i == N-1, e_{N-1}, 0)))`.
        // The fall-through is unreachable: every use of the chain is guarded by
        // `i < N` (conjoined by `eval_*`, or assumed from the body's own bounds
        // assert), so the value chosen for `i >= N` is never observed.
        let mut chain = smt::word(0, elem_w);
        for k in (0..steps).rev() {
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
        // The chain stands for an element of `arg`, so the parser must know the
        // element's signedness for the same reason `bind_indexed_elem` does: a
        // `a[i]` over `[i8; N]` read as unsigned makes `a[i] < 0` never true.
        if self.indexed.get(arg).is_some_and(|&(_, _, _, es)| es) {
            self.signed.insert(chain_name.clone());
        }
        self.paths.insert(chain_name.clone(), chain_name);
        self.sym_bound.insert(arg.to_string(), bound);
        Some(v)
    }

    /// `(index variable, bound)` for every indexed argument a contract
    /// subscripts symbolically, so the caller can require that the precondition
    /// establishes each index is in range.
    ///
    /// The ite chain has a fall-through for an out-of-range index (it has to
    /// return *something*), so the chain is only an honest model where the index
    /// is in range. Rather than refuse the subscript, the caller proves the
    /// precondition implies the bound; if it does not, the contract is refused.
    /// Conjoining the bound into the precondition instead would be unsound,
    /// because it would quietly strengthen what the source asked to be checked.
    ///
    /// The bound is an [`IndexBound`] rather than a `u64` because a slice's is a
    /// *term*: its length is a symbolic input. An array's is still the constant
    /// from its type, wrapped so the two travel as one shape.
    pub fn index_guards(&self) -> Vec<(Var, IndexBound)> {
        self.sym_index
            .iter()
            .filter_map(|(arg, v)| {
                let bound = *self.sym_bound.get(arg)?;
                Some((*v, bound))
            })
            .collect()
    }

    /// `(local, steps)` for every *slice* the contract subscripts symbolically,
    /// so the executor can build its own chain over the same range.
    ///
    /// Only slices appear here. An array's chain comes from its type length, which
    /// the executor already has from `array_lens`; a slice's has no type length,
    /// so the executor can only build one when the contract established
    /// `len <= MAX_INDEX_CHAIN`, which is exactly what `sym_bound` records. A
    /// slice whose bound the contract did *not* establish is absent, and its
    /// symbolic subscript stays refused rather than becoming a chain that
    /// enumerates a range the length may exceed.
    pub fn slice_chain_steps(&self) -> Vec<(u32, u64)> {
        self.sym_bound
            .iter()
            .filter_map(|(arg, bound)| {
                let (local, _, _, _) = self.indexed.get(arg)?;
                match bound {
                    IndexBound::Len(_) => Some((*local, MAX_INDEX_CHAIN)),
                    IndexBound::Const(_) => None,
                }
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
                // An array reached through a field path, `x.a[0]`. The scanner reads `x` first,
                // so the dotted run has to be recognised from the *start* of the identifier, not
                // from a later segment. A run that has an element type recorded and is followed by
                // `[digits]` binds an element of that array; the whole-argument branch below only
                // sees the bare `a[0]` spelling, so the two do not overlap.
                if chars.get(i) == Some(&'.') {
                    if let Some((end, path)) = longest_dotted_run(&chars, start) {
                        if self.path_elem_types.contains_key(&path) && chars.get(end) == Some(&'[') {
                            let mut j = end + 1;
                            let digits: String =
                                chars[j..].iter().take_while(|c| c.is_ascii_digit()).collect();
                            j += digits.len();
                            if !digits.is_empty() && chars.get(j) == Some(&']') {
                                if let Ok(k) = digits.parse::<u64>() {
                                    self.bind_path_elem(&path, k);
                                }
                                i = j + 1;
                                continue;
                            }
                        }
                    }
                }
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
                        // argument, or a local that is a direct alias of one
                        // (`let k = i; a[k]`). A compound index (`a[i + 1]`) is
                        // left unbound and refused by the parser rather than
                        // mis-modelled.
                        if let Some(&index) = args.get(&inner) {
                            // The bound is the array's type length or, for a
                            // slice, the length *variable* -- which is why the
                            // argument's length has to be bound before this runs.
                            // A slice whose length the contract never named has
                            // no variable to bound the chain by, so it is left
                            // unbound and refused.
                            if let Some((_, elem_w, fixed_len, _)) =
                                self.indexed.get(&ident).copied()
                            {
                                let bound = match fixed_len {
                                    Some(n) => Some(IndexBound::Const(n)),
                                    None => self.vars.get(&format!("{ident}__len")).map(|l| {
                                        IndexBound::Len(*l)
                                    }),
                                };
                                if let Some(bound) = bound {
                                    self.bind_sym_index(
                                        &ident, elem_w, bound, &inner, index,
                                    );
                                }
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

/// The longest dotted run starting at `start` (`ident` then `.seg` repeated), as
/// `(index past the run, the dotted path)`.
///
/// Used to recognise an array reached through a field path (`x.a` in `x.a[0]`). A run that is
/// not all identifiers ends before the offending character, so a subscript or a call is never
/// swallowed.
fn longest_dotted_run(chars: &[char], start: usize) -> Option<(usize, String)> {
    let mut end = start;
    while end < chars.len() && (chars[end].is_alphanumeric() || chars[end] == '_') {
        end += 1;
    }
    if end == start {
        return None;
    }
    let mut last = end;
    while chars.get(end) == Some(&'.') {
        let mut j = end + 1;
        while j < chars.len() && (chars[j].is_alphanumeric() || chars[j] == '_') {
            j += 1;
        }
        if j == end + 1 {
            break;
        }
        end = j;
        last = j;
    }
    Some((last, chars[start..last].iter().collect()))
}

/// The longest dotted run starting at `dot` that has a nested binding, as
/// `(index past the run, mangled name)`.
///
/// `dot` is the index of the first `.` in `ident.field...`. The run is scanned
/// segment by segment, and the longest prefix present in `nested_paths` wins: for
/// `o.i.v` with bindings for both `o.i` and `o.i.v`, the leaf wins, so the parser
/// sees the leaf variable rather than the intermediate one. A segment that is not
/// an identifier (`o.len()`, `o[0]`) ends the run, so a call or subscript is never
/// swallowed by a nested match.
fn longest_nested_match(
    chars: &[char],
    start: usize,
    dot: usize,
    fields: &FieldEnv,
) -> Option<(usize, String)> {
    let mut best: Option<(usize, String)> = None;
    let mut i = dot;
    while chars.get(i) == Some(&'.') {
        let mut j = i + 1;
        while j < chars.len() && (chars[j].is_alphanumeric() || chars[j] == '_') {
            j += 1;
        }
        if j == i + 1 {
            break;
        }
        let candidate: String = chars[start..j].iter().collect();
        if let Some(m) = fields.nested_paths.get(&candidate) {
            best = Some((j, m.clone()));
        }
        i = j;
    }
    best
}

/// The segment name a nested refusal should name: the first dotted segment after
/// the longest prefix that *did* bind.
///
/// For `o.i.nope` where `o.i` binds, the failure is `nope`, so the message says
/// `unknown field \`nope\` of \`o\`` rather than repeating the whole path. When
/// nothing binds (the first segment is the bad one) it names that segment.
fn longest_bound_prefix(chars: &[char], start: usize, dot: usize, fields: &FieldEnv) -> String {
    let mut last_bound_end = dot;
    let mut i = dot;
    while chars.get(i) == Some(&'.') {
        let mut j = i + 1;
        while j < chars.len() && (chars[j].is_alphanumeric() || chars[j] == '_') {
            j += 1;
        }
        if j == i + 1 {
            break;
        }
        let candidate: String = chars[start..j].iter().collect();
        if fields.nested_paths.contains_key(&candidate) {
            last_bound_end = j;
        }
        i = j;
    }
    // The segment right after the last bound prefix.
    let mut k = last_bound_end;
    if chars.get(k) == Some(&'.') {
        k += 1;
    }
    let mut e = k;
    while e < chars.len() && (chars[e].is_alphanumeric() || chars[e] == '_') {
        e += 1;
    }
    chars[k..e].iter().collect()
}

/// The context a nested-field walk carries: the argument being walked and the
/// struct layouts, plus the type names on the current branch (the recursion guard).
struct NestedWalk<'a> {
    local: u32,
    arg: &'a str,
    structs: &'a BTreeMap<String, StructDef>,
    on_path: Vec<String>,
}

fn rewrite_fields(text: &str, fields: &FieldEnv) -> Result<String, SpecError> {
    // A payload path is a rewrite target too, so an enum-only contract must not
    // take the early return: `m.Data` would be left spelled as a field access the
    // parser cannot reduce.
    if fields.paths.is_empty()
        && fields.known_args.is_empty()
        && fields.payload_paths.is_empty()
        && fields.nested_paths.is_empty()
    {
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
                // An enum payload: `m.Data`. It is rewritten to the mangled
                // payload name the executor seeds, so the contract's `m.Data` and
                // the body's `((_1 as Data).0)` are one variable.
                if let Some(mangled) = fields.payload_paths.get(&format!("{ident}.{field}")) {
                    out.push_str(mangled);
                    i = j;
                    continue;
                }
                // A variant of an enum argument that has *no* payload (a unit
                // variant, or a struct variant whose fields are not modelled).
                // There is nothing to bind, so this is refused with a message
                // that names the variant rather than left for the parser to
                // report as a missing comparison operator. Refusing is the
                // honest answer: binding a fabricated value would let a false
                // contract about a payload that does not exist be proved.
                if fields.enum_args.contains(&ident)
                    && fields.variant_consts.contains_key(&format!("{ident}::{field}"))
                {
                    return Err(SpecError {
                        text: text.to_string(),
                        reason: format!(
                            "`{field}` is a variant of `{ident}` with no payload to read; \
                             compare the tag instead (`{ident} == ...`)"
                        ),
                    });
                }
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
                    // An element of an array reached through a field path: `x.a[0]`, or a
                    // deeper `o.i.a[0]`. The dotted run is the array's path and its element
                    // binding is in `paths`. Tried before the nested match so the subscript
                    // is not mistaken for the field `x.a` followed by a bracket. The run is
                    // taken from the start of the identifier, not from the first field, so a
                    // nested path is not cut short at `o.i`.
                    if let Some((end, path)) = longest_dotted_run(&chars, start) {
                        if chars.get(end) == Some(&'[') {
                            let mut k = end + 1;
                            let digits: String =
                                chars[k..].iter().take_while(|c| c.is_ascii_digit()).collect();
                            k += digits.len();
                            if !digits.is_empty() && chars.get(k) == Some(&']') {
                                if let Some(mangled) =
                                    fields.paths.get(&format!("{path}[{digits}]"))
                                {
                                    out.push_str(mangled);
                                    i = k + 1;
                                    continue;
                                }
                            }
                        }
                    }
                    // A *nested* path: `o.i.v`. The longest dotted run that has a
                    // binding wins, so `o.i.v` is preferred to a bare `o.i` when
                    // both exist, and the match ends after the segment it consumed.
                    // The run has to start at the first `.` and be all fields, which
                    // is what keeps `xs.len()` and `a[i]` out of it.
                    if let Some((end, mangled)) = longest_nested_match(&chars, start, dot, fields) {
                        out.push_str(&mangled);
                        i = end;
                        continue;
                    }
                    // A field of a known aggregate that has no binding: the struct
                    // has no such field, or its layout was not readable. Refuse
                    // with a message that names the field, rather than letting the
                    // `.` reach the parser and produce "expected a comparison
                    // operator" — the same refusal, a diagnosable one.
                    if fields.aggregate_args.contains(&ident) {
                        // The *segment* that failed is the one after the longest
                        // prefix that did bind, so the message names `v` in
                        // `o.i.v` rather than the whole path.
                        let bad = longest_bound_prefix(&chars, start, dot, fields);
                        return Err(SpecError {
                            text: text.to_string(),
                            reason: format!("unknown field `{bad}` of `{ident}`"),
                        });
                    }
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
                    let is_bound_index = fields
                        .sym_index_names
                        .get(&ident)
                        .map(|names| names.contains(&inner))
                        .unwrap_or(false);
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
    p.variant_consts = fields.variant_consts.clone();
    p.enum_args = fields.enum_args.clone();
    p.consts = fields.consts.clone();
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
    p.variant_consts = fields.variant_consts.clone();
    p.enum_args = fields.enum_args.clone();
    p.consts = fields.consts.clone();
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
    consts: &BTreeMap<String, Const>,
) -> Result<Pred, SpecError> {
    let mut p = Parser::new(text, names, None, signed, false);
    p.consts = consts.clone();
    let pred = p.parse_or()?;
    p.expect_end()?;
    Ok(pred)
}

/// Read a `decreases:` measure as a *value* rather than a predicate.
///
/// A measure is an expression, not a proposition: `decreases: n` or `decreases:
/// len - i` names the quantity the induction counts down. So this parses at the
/// expression level and returns the term with its signedness, rather than a
/// `Pred`.
///
/// The signedness matters because the decrease test is `m < m_entry`, and the
/// relation that means is the measure's own: a signed measure compares with
/// `slt` and an unsigned one with `ult`. A measure that does not resolve is an
/// error, for the same reason an invariant that does not resolve is: a typo must
/// not become an unconstrained value that makes the decrease test vacuous and the
/// induction unsound.
pub fn eval_measure(
    text: &str,
    names: &BTreeMap<String, Var>,
    signed: &BTreeSet<String>,
    consts: &BTreeMap<String, Const>,
) -> Result<(Var, bool), SpecError> {
    let mut p = Parser::new(text, names, None, signed, false);
    p.consts = consts.clone();
    let (v, sgn) = p.parse_expr()?;
    p.expect_end()?;
    Ok((v, sgn.eval()))
}

/// The signedness of a subexpression: signed, unsigned, or *not yet known*.
///
/// A bare literal has no type of its own -- Rust infers it from the operand it
/// meets -- so reading it as either sign at the point it is parsed is a guess.
/// The guess is harmless where signed and unsigned agree (`+`, `&`, `==`) but
/// wrong where they do not (`>>`, `/`, `%`, an ordering comparison), and the
/// wrong pick *discharged* `ensures: ret <= (!0 >> 1)` for an `i8` (a false
/// proof: `!0 >> 1` is `127` unsigned and `-1` signed).
///
/// So an untyped operand is carried as `Literal` (a bare, non-negative literal,
/// whose value is unambiguous) or `Opaque` (an untyped constant that is not a
/// plain literal -- the complement of one, or a fold of untyped operands -- whose
/// sign cannot be recovered). An untyped operand adopts the typed operand's sign
/// at a bitwise or additive operator; a *sign-sensitive* operator (`>>`, `/`,
/// `%`, an ordering comparison, a widening cast) refuses an `Opaque` operand
/// rather than guessing, because the two readings disagree there.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Sign {
    Signed,
    Unsigned,
    /// A negated *bare* literal, `-1` or `-128`: signed, but — like a literal —
    /// its width is inferred from the operand it meets (`-1 < (x as i16)` is
    /// well-typed). A suffixed or bound constant (`-1i8`, `i8::MIN`) is `Signed`
    /// and carries its own width, so a mismatch with a typed partner is `E0308`.
    NegLiteral,
    Literal,
    /// An untyped constant that is not a bare literal -- the complement of one
    /// (`!0`, `!128`) -- whose sign cannot be recovered, so it takes the operand's.
    /// The payload is the *(min, max) envelope of the operand literals* Rust
    /// range-checks against the type the complement meets -- `(128, 128)` for
    /// `!128`, `(63, 128)` for `!(128 - 63)` -- because Rust checks those literals
    /// even though the reader holds the complement's value. It is carried here
    /// rather than recorded in the `range` map: the complement's value term is a
    /// plain constant (`!128` is `word(127, 8)`), so it is *hash-consed with an
    /// unrelated bare `127`* and attaching the operand's envelope to that id made
    /// the reader refuse the innocent literal. `None` when the operand is not a
    /// tracked constant, which is the conservative reading: the fit cannot be shown.
    Opaque(Option<(i128, i128)>),
}

impl Sign {
    fn from_bool(b: bool) -> Sign {
        if b {
            Sign::Signed
        } else {
            Sign::Unsigned
        }
    }
    /// The sign to *evaluate* with, for a `+ - * & | ^ <<` or `== !=`: signed and
    /// unsigned agree there, so an untyped operand may take the other side's sign
    /// (or unsigned, which is a literal's natural reading).
    fn eval(self) -> bool {
        matches!(self, Sign::Signed | Sign::NegLiteral)
    }
    /// Whether this is an untyped constant that is not a bare literal.
    fn is_opaque(self) -> bool {
        matches!(self, Sign::Opaque(_))
    }
    /// The complement operand literals' envelope, when it is tracked.
    fn opaque_operand(self) -> Option<(i128, i128)> {
        if let Sign::Opaque(m) = self {
            m
        } else {
            None
        }
    }
    /// Whether the operand's *width* is inferred from the other side rather than
    /// fixed by its own type. A bare literal, a bare negation of one, and an
    /// untyped constant that is not a bare literal (the complement of one, or a
    /// fold of untyped operands -- `!0`, `(!0 + 1)`) all have no type of their own,
    /// so Rust infers their width from the operand they meet. Only a value whose
    /// type is fixed (`1i8`, `i8::MIN`, a cast, a name) has a width of its own, and
    /// a mismatch between it and a typed partner is `E0308`.
    fn adapts(self) -> bool {
        !self.fixes_type()
    }
    /// Whether the operand's type is *fixed* by its own form (`1i8`, `i8::MIN`, a
    /// cast, a name) rather than inferred from context. Such a value cannot meet
    /// an operand of another width or signedness.
    fn fixes_type(self) -> bool {
        matches!(self, Sign::Signed | Sign::Unsigned)
    }
    /// The sign a *typed* operand forces on an untyped partner, if any.
    fn typed(self) -> Option<bool> {
        match self {
            Sign::Signed | Sign::NegLiteral => Some(true),
            Sign::Unsigned => Some(false),
            Sign::Literal | Sign::Opaque(_) => None,
        }
    }
    /// Resolve a pair: the typed operand's sign, or `None` when neither is typed.
    fn resolve(a: Sign, b: Sign) -> Option<bool> {
        a.typed().or_else(|| b.typed())
    }
    /// The sign of `a <op> b`: the typed operand's, or the untyped pair's own.
    ///
    /// A pair with a *fixed* operand takes that operand's sign. With neither fixed
    /// the result keeps the pair's own nature: `Opaque` when a width-dependent
    /// untyped constant is involved (`!0 + 2`), `NegLiteral` when the pair is a
    /// signed but width-adaptive value (`-1 + 1`), and `Literal` otherwise.
    fn combine(a: Sign, b: Sign) -> Sign {
        if a.fixes_type() || b.fixes_type() {
            if a == Sign::Signed || b == Sign::Signed {
                Sign::Signed
            } else {
                Sign::Unsigned
            }
        } else if a.is_opaque() || b.is_opaque() {
            // A fold of complements (`!0 + 2`) has no tracked operand of its own;
            // the operands' literal envelopes are unioned, so a literal anywhere
            // under the fold is still range-checked where the fold is read. `None`
            // only when neither side carried one (the conservative reading).
            Sign::Opaque(Sign::union_env(a.opaque_operand(), b.opaque_operand()))
        } else if a == Sign::NegLiteral || b == Sign::NegLiteral {
            Sign::NegLiteral
        } else {
            Sign::Literal
        }
    }
    /// Is this a sign-*ambiguous* operand: an untyped constant that is not a bare
    /// literal, so signed and unsigned readings of it differ?
    fn ambiguous(self) -> bool {
        self.is_opaque()
    }
    /// The union of two optional envelopes: the min of the mins and the max of the
    /// maxes, or the one that is present when only one is.
    fn union_env(a: Option<(i128, i128)>, b: Option<(i128, i128)>) -> Option<(i128, i128)> {
        match (a, b) {
            (Some((alo, ahi)), Some((blo, bhi))) => Some((alo.min(blo), ahi.max(bhi))),
            (Some(e), None) | (None, Some(e)) => Some(e),
            (None, None) => None,
        }
    }
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
    /// `Enum::Variant` → `(discriminant, tag width)`. Empty outside a contract
    /// evaluation, which is what makes `eval_invariant` (which has no enum
    /// layouts in hand) refuse such a name rather than guess a constant.
    variant_consts: BTreeMap<String, (u64, u8)>,
    /// The enum-typed argument names, so a variant name that is *not* in
    /// `variant_consts` can be reported as a bad variant rather than an unknown
    /// constant.
    enum_args: BTreeSet<String>,
    /// Named `const` items, name → the literal the item was defined with, so a
    /// contract can name a constant the way the body does. Empty outside a
    /// contract evaluation that was given the program's table, in which case a
    /// `const` name is refused rather than guessed at -- the same answer the
    /// reader gave before this table existed. See [`FieldEnv::consts`].
    consts: BTreeMap<String, Const>,
    /// The `(min, max)` envelope, as `i128`, of the *literals and folded
    /// intermediate values* in the term a `Var` holds. Rust range-checks every
    /// literal and every constant `+ - *` intermediate against the type the
    /// expression is read at, not only the value that meets the comparison:
    /// `2 & 128` for an `i8` is `literal out of range for i8` although the fold's
    /// value is `0`, and `128 - 63` is rejected although its value `65` fits.
    /// The engine folds the term, so the reader can only see the result; this
    /// map remembers what the result was built from. Terms are hash-consed
    /// (`smt::mk_term`), so keying on the term id is exact.
    ///
    /// A complement (`!128`) is *not* propagated into the envelope through its
    /// value: the complement's own `Opaque` payload already carries the operand
    /// that Rust range-checks (`128`), and the complement's *value* (`127`) is
    /// not a literal. Only a bare literal, a unary `-`, and a `+ - *` fold
    /// contribute.
    range: BTreeMap<u32, (i128, i128)>,
    /// The term ids of *pristine bare literals* (`128`, `1`). A bare literal is
    /// the one thing Rust does *not* check as written when it sits directly under
    /// a unary `-`: `-128` is legal for an `i8` even though `128` alone is not,
    /// because the negated value, not the magnitude, is what meets the type. This
    /// set tells `parse_neg` apart that case from a literal *inside* a fold, whose
    /// magnitude is checked as written (`-(128 - 63)` is rejected for its `128`).
    bare_literals: BTreeSet<u32>,
    /// The width a shift amount's bare literals are floored at, or `0` outside an
    /// amount.
    ///
    /// A shift amount is a value of its *own* type, not of the shifted operand's:
    /// Rust leaves the amount's type unconstrained, so an unsuffixed amount
    /// expression defaults to `i32` and is folded at 32 bits. Sizing the amount's
    /// bare literals to the scope's width instead made `x >> (2 << 7)` fold the
    /// amount to `0` at an eight-bit scope (the eight-bit `2 << 7` wraps) where
    /// rustc computes `256` and rejects the shift, so the reader *decided* a
    /// comparison on a program rustc rejects. Flooring at 32 bits makes the fold
    /// agree with rustc's `i32` evaluation, so the wrapped value never appears.
    ///
    /// The floor is the amount's *inferred* type, which is [`amount_width`]'s job:
    /// `i32` when nothing in the amount fixes it, or the width of a *typed*
    /// (suffixed) operand when one does -- `1u8 + (2 << 7)` is a `u8` expression,
    /// so its `2 << 7` is `0u8`, not the `256` a blind `i32` floor would build.
    /// The field is set at each shift and restored after the amount is parsed, so a
    /// nested shift's *operand* still sees the enclosing amount's floor.
    ///
    /// [`amount_width`]: Self::amount_width
    amount_floor: u8,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Tok {
    Ident(String),
    /// A numeric literal, with its type suffix's `(width, signed)` if it has one.
    ///
    /// `0u8` is *unsigned* and `0i8` is *signed*: rustc gives the literal that
    /// type, so `-1 <= 0u8` is `E0277` (a `u8` cannot be negated) rather than a
    /// signed comparison. Dropping the suffix left the reader no way to tell
    /// `0u8` from a bare `0`, so a mismatched constant pair was read as signed and
    /// an invalid program was silently decided. The *width* matters just as much:
    /// a suffixed literal has a fixed width, and building it at the scope's width
    /// instead turned `128i16` into `0x80` in an 8-bit scope, which a later
    /// `as i32` sign-extended to `-128` and *verified* a false
    /// `ensures: 128i16 as i32 == -128`. A bare literal has no suffix and stays
    /// untyped (`None`), sized contextually.
    Num(u64, Option<(u8, bool)>),
    /// A numeric literal the tokenizer could not read *exactly* -- a digit that
    /// is invalid for its radix, or a value past `u64`.
    ///
    /// It is a distinct token so the parser refuses it rather than reading it as
    /// `0`. Reading every literal as decimal silently truncated `0xFF` to `0`
    /// (the digit run stopped at `x` and the rest was skipped as a type suffix),
    /// and a mis-read constant in a precondition is a false proof: `requires: x
    /// == 0xFF` became `x == 0`, so `ensures: ret == 0` was "proved" for a
    /// function returning `255`. A refusal is safe; a wrong number is not.
    BadNum,
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
            // A radix prefix, or a plain decimal. `0x`/`0b`/`0o` is always a prefix
            // when it starts a literal: `0xg` is a malformed hex literal, not a
            // decimal `0` followed by an identifier, and reading it as the latter
            // would be the same silent truncation this scan exists to avoid.
            let radix = if c == '0' {
                match b.get(i + 1) {
                    Some('x' | 'X') => {
                        i += 2;
                        16
                    }
                    Some('b' | 'B') => {
                        i += 2;
                        2
                    }
                    Some('o' | 'O') => {
                        i += 2;
                        8
                    }
                    _ => 10,
                }
            } else {
                10
            };
            // Take the longest run of digits and `_` separators. A `_` between
            // digits is a separator; the run stops at anything else, which is how a
            // type suffix (`100u32`) is left for the loop below.
            let mut digits = String::new();
            // The signedness and width of the literal's type suffix, if it has one.
            let mut suffix: Option<(u8, bool)> = None;
            while i < b.len() && (b[i].is_digit(radix) || b[i] == '_') {
                if b[i] != '_' {
                    digits.push(b[i]);
                }
                i += 1;
            }
            // Skip a type suffix (`100u32`, `0xFF_i32`) so the literal stays a
            // number. It must be one of the integer type names: `0xFFg` is
            // malformed, and swallowing the `g` as a suffix would read the literal
            // as a well-formed `255` -- the same silent mis-read this scan exists
            // to avoid. A trailing `_` (`100_`) is a separator, not a suffix, and
            // Rust accepts it.
            if b.get(i).is_some_and(|d| d.is_ascii_alphabetic()) {
                let sfx_start = i;
                while i < b.len() && (b[i].is_alphanumeric() || b[i] == '_') {
                    i += 1;
                }
                let sfx: String = b[sfx_start..i].iter().collect();
                if !matches!(
                    sfx.as_str(),
                    "i8" | "i16"
                        | "i32"
                        | "i64"
                        | "i128"
                        | "isize"
                        | "u8"
                        | "u16"
                        | "u32"
                        | "u64"
                        | "u128"
                        | "usize"
                ) {
                    out.push(Tok::BadNum);
                    continue;
                }
                // The suffix is the literal's *type*, so it is what makes `0u8`
                // unsigned and gives it a fixed width. Both are recorded rather
                // than dropped: dropping the sign left a mismatched constant pair
                // (`-1 <= 0u8`) with no unsigned side to see, so it was read as a
                // signed comparison and an invalid program was silently decided;
                // dropping the *width* built `128i16` at the scope's width, which a
                // later widening cast sign-extended to `-128` -- a false proof.
                let ty = Ty::parse(&sfx);
                // The width is recorded as the suffix's *own* width, including
                // `u128`/`i128`'s 128: the reader refuses that width in `parse_atom`
                // (the engine's words stop at 64), and keeping the true number here
                // is what lets the refusal name it. A `usize`/`isize` suffix is 64.
                let (signed, width) = (ty.is_signed(), ty.width().unwrap_or(64));
                suffix = Some((width, signed));
            }
            // Anything the run did not consume is a malformed literal: a digit not
            // valid for the radix (`0b12`, `0o9`), or a value past `u64`. Refuse
            // rather than take a partial value -- a wrong number in a precondition
            // is a false proof, a refusal is not.
            let exact = i == b.len() || (!b[i].is_alphanumeric() && b[i] != '_');
            let val = if digits.is_empty() {
                None
            } else {
                u64::from_str_radix(&digits, radix).ok()
            };
            match (exact, val) {
                (true, Some(v)) => out.push(Tok::Num(v, suffix)),
                _ => out.push(Tok::BadNum),
            }
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
        if ["==", "!=", "<=", ">=", "<<", ">>", "&&", "||"].contains(&two.as_str()) {
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
            variant_consts: BTreeMap::new(),
            enum_args: BTreeSet::new(),
            consts: BTreeMap::new(),
            range: BTreeMap::new(),
            bare_literals: BTreeSet::new(),
            amount_floor: 0,
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
        self.paren_is_predicate_from(self.pos)
    }

    /// [`Self::paren_is_predicate`], starting at an explicit token index.
    ///
    /// The `!` lookahead needs this: to decide whether `!` negates a *predicate* it
    /// must ask about the `(` that follows the `!`, not the one at the cursor.
    fn paren_is_predicate_from(&self, start: usize) -> bool {
        let mut depth = 0usize;
        for t in &self.toks[start..] {
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

    /// Whether the `!` at the cursor applies to a *predicate* rather than a value.
    ///
    /// True for `!(a == b)` (a parenthesized predicate) and `!true`/`!false`; false
    /// for `!x`, `!7` and `!x == 5`, where `!` is the unary prefix on a value.
    fn bang_is_predicate(&self) -> bool {
        match self.toks.get(self.pos + 1) {
            Some(Tok::Op(o)) if o == "(" => self.paren_is_predicate_from(self.pos + 1),
            Some(Tok::Ident(n)) if n == "true" || n == "false" => true,
            _ => false,
        }
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

    /// Record the `(min, max)` of the *literals and folded intermediates* a
    /// constant term was built from. Rust range-checks every literal and every
    /// constant `+ - *` intermediate against the type the expression is read at,
    /// so `2 & 128` is an `i8` error although the fold's value is `0`; the engine
    /// folds the term, so this remembers what the value was built from. Terms are
    /// hash-consed, so the id is a faithful key, and the envelope is only ever
    /// widened (never narrowed), so a shared subterm keeps the union of its uses.
    fn record_range(&mut self, v: Var, lo: i128, hi: i128) {
        let e = self.range.entry(v.0 .0).or_insert((lo, hi));
        e.0 = e.0.min(lo);
        e.1 = e.1.max(hi);
    }

    /// The envelope [`record_range`](Self::record_range) recorded for `v`, if any.
    fn range_of(&self, v: Var) -> Option<(i128, i128)> {
        self.range.get(&v.0 .0).copied()
    }

    /// A constant of width `w` that is *not* hash-consed with a plain `word(k, w)`.
    ///
    /// A named bound (`i8::MIN`, `i8::MAX`) and an enum variant are the same bit
    /// pattern as a bare or suffixed literal of that value, so `smt::word` returns
    /// the *one* shared term: `i8::MIN` and `128i8` are both `word(128, 8)`. The
    /// `range` map is keyed by term, so an envelope recorded for the literal --
    /// `128i8` records the written magnitude `128`, which is out of range for an
    /// `i8` -- was read back as the *bound's* envelope and refused a valid
    /// `y == -128i8 && y == i8::MIN`. A bound's fit is known by construction (it is
    /// the type's own extreme), so it must not inherit a literal's envelope.
    ///
    /// The term is built as `truncate(word(k, 64), w)`, which the engine folds to
    /// the same value but which hash-conses separately from `word(k, w)`: no
    /// literal path ever builds a 64-bit word for a value that fits `w`, so this
    /// node is the bound's alone. It carries no `range` entry, so `check_range`
    /// passes it, exactly as the plain bound did before the envelope map existed.
    fn unshared_const(&self, k: u64, w: u8) -> Var {
        smt::truncate(smt::word(k, 64), w)
    }

    /// The value a named `const` item denotes, at the item's own width and sign.
    ///
    /// The dump prints the item's body const-evaluated and typed (`const LIMIT:
    /// u8 = const 10_u8;`), so the width and the sign come from the type suffix
    /// rather than from the operand the constant meets -- a constant has a type of
    /// its own, unlike a bare literal. The term is built through
    /// [`Self::unshared_const`] so it does not hash-cons with a literal of the same
    /// bit pattern, whose recorded envelope would otherwise be read back as the
    /// constant's and could refuse a valid contract.
    ///
    /// A name that is not a literal is refused rather than guessed at: an
    /// expression-bodied item has its value in its own body, not in a declaration
    /// the reader can fold, so nothing here can decide it.
    fn const_item(&self, name: &str, c: &Const) -> Result<(Var, Sign), SpecError> {
        match c {
            Const::UInt(n, ty) => match ty.as_ref().and_then(|t| t.width()) {
                Some(1) => Ok((smt::word(*n as u64 & 1, 1), Sign::Literal)),
                Some(w) if w <= 64 => {
                    let signed = ty.as_ref().map(Ty::is_signed).unwrap_or(false);
                    // A signed item's printed value is two's complement at its width
                    // (`const NEG: i8 = -1` prints `0xff`), and the sign travels with
                    // the term so a later comparison reads it as `-1`; an unsigned
                    // item's is its plain value.
                    Ok((self.unshared_const(*n as u64, w), Sign::from_bool(signed)))
                }
                _ => Err(self.err(format!(
                    "the constant `{name}` has no bit-vector width, so it is not modelled"
                ))),
            },
            Const::Bool(b) => Ok((smt::word(u64::from(*b), 1), Sign::Literal)),
            Const::Unit | Const::Other(_) => Err(self.err(format!(
                "the constant `{name}` is not a literal, so its value is not known to the \
                 contract reader"
            ))),
        }
    }

    /// Record `v`'s envelope as the union of its operands' envelopes, so a
    /// bitwise, shift or `/`/`%` result carries the literals underneath it to the
    /// later range check even though the operation itself adds no literal.
    fn record_range_union(&mut self, v: Var, a: Var, b: Var) {
        let (mut lo, mut hi) = (i128::MAX, i128::MIN);
        let mut any = false;
        for x in [a, b] {
            if let Some((l, h)) = self.range_of(x) {
                lo = lo.min(l);
                hi = hi.max(h);
                any = true;
            }
        }
        if any {
            self.record_range(v, lo, hi);
        }
    }

    /// Record a constant term's own value as its envelope, as the value Rust
    /// range-checks it at: an unsigned constant is its magnitude, a signed one is
    /// its two's-complement value (`128i8` and `i8::MIN` are both `-128`, which is
    /// legal, where the bare `128` is `+128`, which is not).
    fn record_const(&mut self, v: Var, signed: bool) {
        if let Some(val) = self.const_value(v) {
            let w = smt::bits(v);
            let sv: i128 = if signed {
                if w >= 64 {
                    val as i64 as i128
                } else if val & (1u64 << (w - 1)) != 0 {
                    val as i128 - (1i128 << w)
                } else {
                    val as i128
                }
            } else {
                val as i128
            };
            self.record_range(v, sv, sv);
        }
    }

    /// Record a folded `+ - *` result: the union of its operands' envelopes (the
    /// literals underneath) and the result's own value (the intermediate Rust
    /// checks). `2 & 128` keeps the `128`; `100 + 100` adds the `200`.
    ///
    /// An *opaque* result (a fold that touched a complement) records only its
    /// operands. Its own value is a *guess*: the reader evaluates it unsigned
    /// because the fold's type is not known here, so `!1 + 1` records `255` where
    /// the `i8` the fold finally meets makes it `-1`. Range-checking that guess
    /// refused a valid `y == !(!1 + 1)` for an `i8` -- the `255` is out of range
    /// for the signed type, though no `255` is written. The genuine operand
    /// envelopes still carry, so a literal anywhere under the fold is still
    /// checked, and an overflowing intermediate is refused in `fold_const_arith`
    /// before it can reach here.
    fn record_fold_result(&mut self, v: Var, a: Var, b: Var, sgn: Sign) {
        self.record_range_union(v, a, b);
        if !sgn.is_opaque() && self.const_value(v).is_some() {
            self.record_const(v, sgn.eval());
        }
    }

    /// Record the envelope of a unary negation. Rust checks the *negated value*,
    /// so the operand's literals carry over (negated) -- `-(128 - 63)` is rejected
    /// for the inner `128` even though the negated value `-65` fits. The one
    /// exception is a pristine bare literal: `-128` is legal for an `i8` even
    /// though `128` alone is not, because there the negated value *replaces* the
    /// magnitude rather than sitting inside a fold, so its magnitude is not
    /// checked. `bare` says the operand is such a literal.
    fn record_negation(&mut self, nv: Var, operand: Var, bare: bool) {
        if let Some((lo, hi)) = self.range_of(operand) {
            if !bare {
                self.record_range(nv, lo, hi);
            }
            self.record_range(nv, -hi, -lo);
        }
    }

    /// Refuse a constant whose *literals or folded intermediates* do not fit the
    /// type they meet. Rust range-checks every literal and every constant `+ - *`
    /// intermediate against the type the expression is read at -- `2 & 128` is an
    /// `i8` error although the fold's value is `0`, and `128 - 63` is rejected
    /// although its value `65` fits -- so a contract the reader would otherwise
    /// *decide* on a program rustc rejects is refused instead. The envelope is
    /// recorded by [`record_const`](Self::record_const) and friends; a term with
    /// no entry (a name, a cast) has nothing to check.
    fn check_range(&self, v: Var, wide: u8, signed: bool) -> Result<(), SpecError> {
        let Some((lo, hi)) = self.range_of(v) else {
            return Ok(());
        };
        let fits = |x: i128| {
            if signed {
                x >= -(1i128 << (wide - 1)) && x < (1i128 << (wide - 1))
            } else {
                x >= 0 && (x as u128) < (1u128 << wide)
            }
        };
        if !fits(lo) || !fits(hi) {
            let shown = if !fits(lo) { lo } else { hi };
            return Err(self.err(format!(
                "a constant value `{shown}` does not fit the operand's {wide}-bit {} type, so \
                 the shape is refused",
                if signed { "signed" } else { "unsigned" }
            )));
        }
        Ok(())
    }

    /// Refuse a *signed* operand meeting an *unsigned* one, in either order.
    ///
    /// Rust never lets the two sides of a comparison or an arithmetic operator
    /// differ in signedness. A literal takes its type from the operand it meets,
    /// so `x == -1` and `x + -1` for a `u8` are compile errors ("cannot apply
    /// unary operator `-` to type `u8`"). The reader carries a negation as a bit
    /// pattern at the operand's width, which reads `-1` as `255`: a wrong *value*,
    /// and a wrong value in a precondition is a false proof (`requires: x + -1 >= 0`
    /// is trivially true, so any postcondition is proved). So the shape is refused
    /// wherever two operands of one operator can meet, which is the comparison
    /// *and* the arithmetic levels.
    ///
    /// Two *names* of different signedness are the same mistake. `a > b` for an
    /// `i8` and a `u8` is `E0308: mismatched types`, and the reader has to read it
    /// as *some* sign. It picks signed, which is a real reading and not a false
    /// proof, but it is a reading of a program rustc rejects -- so the shape is
    /// refused rather than decided, the same answer as the constant case. It also
    /// closes a semantic hole between this parser and the body: the body reads each
    /// operand at *its own* signedness, so the contract and the body could disagree
    /// about which of `a > b` or `ule(b, a)` is meant.
    ///
    /// The check is narrow. An *untyped* operand (a bare literal, or the complement
    /// of one) is not this shape -- it adopts the typed operand's sign instead, and
    /// is resolved by `Sign::combine`. Two constants are aligned and range-checked
    /// by `align_widths`/`fold_const_arith`. Only a signed *typed* operand against
    /// an unsigned *typed* operand, or a signed constant against an unsigned name,
    /// triggers it -- exactly the pairs rustc rejects.
    fn refuse_mixed_signedness(
        &self,
        l: Var,
        ls: Sign,
        r: Var,
        rs: Sign,
    ) -> Result<(), SpecError> {
        // An untyped operand adopts the other side's sign, so it never clashes.
        let (Some(lb), Some(rb)) = (ls.typed(), rs.typed()) else {
            return Ok(());
        };
        if lb == rb {
            return Ok(());
        }
        let lconst = self.const_value(l).is_some();
        let rconst = self.const_value(r).is_some();
        // Both sides are typed names: `a > b` for an `i8` and a `u8`.
        if !lconst && !rconst {
            return Err(self.err("operands of different signedness cannot be combined"));
        }
        // At least one side is a constant, and the signs differ. rustc rejects the
        // pairing whether the other side is a name (`-1 > x` for a `u8`) or another
        // constant (`-1 > 0u8`, `-1i8 == 0u8`): a signed constant cannot adopt the
        // unsigned operand's type. The both-constants case used to fall through --
        // the earlier check required exactly *one* constant -- and was read as a
        // *signed* comparison, silently deciding an invalid program (`-1 <= 0u8`
        // "verified" as `-1 <= 0`).
        Err(self.err(
            "a signed constant cannot be combined with an unsigned operand",
        ))
    }

    /// The value a constant *denotes*, at its own width.
    ///
    /// A bare literal is non-negative, so its bit pattern is its value. A signed
    /// constant (`i8::MIN`) or a negation (`-1`) is two's-complement, so the top
    /// bit is a sign bit and the value is negative when it is set. `128` and
    /// `i8::MIN` share the bit pattern `0x80` and mean different things, which is
    /// why the flag is passed rather than inferred.
    fn signed_value(&self, v: Var, sgn: bool) -> i128 {
        let w = smt::bits(v);
        let val = self.const_value(v).unwrap_or(0);
        if !sgn {
            return val as i128;
        }
        if w >= 64 {
            val as i64 as i128
        } else if val & (1u64 << (w - 1)) != 0 {
            val as i128 - (1i128 << w)
        } else {
            val as i128
        }
    }

    /// Fold a constant `+`, `-` or `*` *exactly*, widening past the operand width
    /// when the true result does not fit it.
    ///
    /// Rust const-eval rejects a constant expression that overflows its type --
    /// `200u8 + 100u8` is an error, `0u8 - 1u8` too -- and the range check in
    /// [`Self::resize_const`] is what turns that into a refusal. But the check
    /// only sees the value the fold produced, and letting the width-`w` engine
    /// wrap first produced the *wrong* value: `200 + 100` became `44`, so
    /// `x <= 200 + 100` for a `u8` read as `x <= 44` -- a *stronger* precondition
    /// than the author wrote, and `ensures: ret <= 44` was proved for a body that
    /// fails at `x == 100`. That is a false proof, not a refusal.
    ///
    /// Widening keeps the value exact so the later check refuses the shape when
    /// the operand it meets is too narrow, and still reads a result that fits a
    /// wider operand (`x as u16 <= 200 + 100` is `300`, which rustc accepts). An
    /// unsigned expression that goes negative is refused outright: the reader's
    /// own model says such an expression is unsigned, and `0u8 - 1u8` is a
    /// rustc error, so handing the comparison a negative value would only make it
    /// read the wrong predicate.
    ///
    /// Returns `None` when the exact result already fits, in which case the
    /// ordinary wrapping operator produces the same term and nothing changes.
    fn fold_const_arith(
        &self,
        op: &str,
        a: Var,
        sa: Sign,
        b: Var,
        sb: Sign,
    ) -> Result<Option<(Var, Sign)>, SpecError> {
        // Only a fold of two constants can be decided here; a symbolic operand
        // leaves the operation to the engine.
        let (Some(_), Some(_)) = (self.const_value(a), self.const_value(b)) else {
            return Ok(None);
        };
        let w = smt::bits(a);
        let signed = sa.eval() || sb.eval();
        let (va, vb) = (self.signed_value(a, sa.eval()), self.signed_value(b, sb.eval()));
        // The signed minimum, which is the one value a division can overflow on.
        let min = -(1i128 << (w - 1));
        if matches!(op, "/" | "%") {
            // `i8::MIN / -1` and `i8::MIN % -1` are a rustc *panic*/const-eval
            // error; the engine's divider would wrap them to `MIN` and `0`, a
            // wrong value rather than a refusal.
            if signed && vb == -1 && va == min {
                return Err(self.err(format!(
                    "a constant `{op}` overflows the {w}-bit signed operand width"
                )));
            }
            return Ok(None);
        }
        if !matches!(op, "+" | "-" | "*") {
            return Ok(None);
        }
        let r: i128 = match op {
            "+" => va + vb,
            "-" => va - vb,
            _ => va * vb,
        };
        // An *opaque* operand (a complement, or a fold that touched one) has no
        // signedness of its own: Rust infers it from the type the fold meets, which
        // is not known here. The reader guesses from the other operand, and when
        // *no* operand fixes a sign the guess can disagree with the reading the fold
        // finally gets. Two shapes follow, both of which the reader would otherwise
        // *decide* on a program rustc rejects.
        let untyped_opaque =
            (sa.is_opaque() || sb.is_opaque()) && !sa.fixes_type() && !sb.fixes_type();
        if untyped_opaque && (sa == Sign::NegLiteral || sb == Sign::NegLiteral) {
            // A negated bare literal (`-0`) beside an opaque operand is `E0277`
            // (`cannot apply unary - to type u16`) when the fold meets an unsigned
            // type and legal when it meets a signed one: `!100 * -0` is rejected for
            // a `u16` but accepted for an `i16`. The reader cannot tell which, so
            // the shape is refused rather than decided on the wrong reading.
            return Err(self.err(format!(
                "a constant `{op}` of an untyped operand and a negated literal is \
                 sign-ambiguous: the negation is legal only at a signed type"
            )));
        }
        let fits = if signed {
            let hi = (1i128 << (w - 1)) - 1;
            r >= min && r <= hi
        } else {
            r >= 0 && (r as u128) < (1u128 << w)
        };
        // A fold that *fits* under the reader's guess can still overflow under the
        // other reading: `!127 - 63` is `128 - 63 = 65` unsigned but `i8::MIN - 63`
        // -- a rustc overflow -- signed. The reader decided it (`65`) for a program
        // rustc rejects. The two readings disagree on the overflow, so the shape is
        // refused. (When the guess does *not* fit, the width-dependent refusal below
        // is the answer, and its message is kept.)
        if untyped_opaque && fits {
            let alt = !signed;
            let (av, bv) = (self.signed_value(a, alt), self.signed_value(b, alt));
            let ar: i128 = match op {
                "+" => av + bv,
                "-" => av - bv,
                _ => av * bv,
            };
            let alt_fits = if alt {
                ar >= min && ar < (1i128 << (w - 1))
            } else {
                ar >= 0 && (ar as u128) < (1u128 << w)
            };
            if !alt_fits {
                return Err(self.err(format!(
                    "a constant `{op}` of an untyped operand is sign-ambiguous: it overflows the \
                     {w}-bit operand width under one reading and not the other"
                )));
            }
        }
        if fits {
            return Ok(None);
        }
        if !signed && r < 0 {
            return Err(self.err(format!(
                "a constant expression underflows the {w}-bit unsigned operand width"
            )));
        }
        // The narrowest width that holds the exact result, *at the expression's
        // own signedness*. The signed case matters: `i8::MAX + 1` is `128`, which
        // fits an unsigned `u8` but not a signed one, and an unsigned test here
        // would leave it at eight bits where it reads as `-128` -- a new false
        // proof in place of the one being fixed.
        let mut width = 1u8;
        let mut holds = false;
        while width <= 64 {
            holds = if signed {
                r >= -(1i128 << (width - 1)) && r < (1i128 << (width - 1))
            } else {
                (r as u128) < (1u128 << width)
            };
            if holds {
                break;
            }
            width += 1;
        }
        if !holds {
            // Wider than any engine word: nothing to compare against.
            return Err(self
                .err("a constant expression is wider than the engine's 64-bit words"));
        }
        // The widened result keeps a *typed* operand's sign. With two untyped
        // operands the result is one of two very different things, and conflating
        // them was a false proof:
        //
        // * A fold of *bare literals* (`200 + 100`) is a width-independent
        //   **value**: `300` is `300` at any width that holds it, so it may widen
        //   exactly like a literal. It is `Literal`.
        // * A fold that touches a *complement* (`!0 + 2`) is a width-dependent bit
        //   pattern: `!0` is `-1`/`255`/`65535` according to the width, so
        //   `!0 + 2` is `1` against an `i16` but the reader holds it at the
        //   scope's width. Emitting it at the engine's full width let a later
        //   resize *truncate* it to the operand -- `ensures: (x as i16 + 2) == !0
        //   + 2` was *verified* for `257 == 1`. It is `Opaque`, and `resize_const`
        //   refuses its widening.
        let out = if signed {
            Sign::Signed
        } else if sa == Sign::Unsigned || sb == Sign::Unsigned {
            Sign::Unsigned
        } else if sa.is_opaque() || sb.is_opaque() {
            // An untyped fold whose exact result does not fit the operand width:
            // `!0 + 1` is `256` at the scope's width, `!0 + 2` is `257`. Its value
            // depends on the width Rust infers for it, and the reader learns that
            // width only at the operator that consumes the fold. Carrying the
            // scope-width value and letting `resize_const` truncate it later was a
            // false proof: `(!0 + 1) < 1u8` *verified* (`0 < 1`) and
            // `(!0 + 2) == 1u8` did too (`257` truncated to `1`), though rustc
            // rejects both as an arithmetic overflow.
            //
            // A *signed* partner is no safer, so the refusal cannot be narrowed to
            // the unsigned case: `(!0 + 200) == x` for an `i8` `x` *verified* with
            // `x == -57` (the scope-width `!0` is `255`, `255 + 200` is `455`,
            // truncated to an `i8`'s `-57`), and rustc rejects the fold as `literal
            // out of range for i8`. The value is simply not known until the width
            // is, so it is refused.
            //
            // Only the overflowing branch is reached here, so a fold that fits (a
            // value that is the same at any width holding it, like `200 + 100`) is
            // unaffected -- the control the corpus asserts still reads.
            return Err(self.err(format!(
                "a constant `{op}` of an untyped operand is width-dependent and overflows the \
                 {w}-bit operand width, so its value is not known where it is read"
            )));
        } else {
            Sign::Literal
        };
        // Emit at the narrowest width that holds the exact result, at the
        // expression's own signedness. A fold with a *typed* operand keeps that
        // operand's type, so this is where its exact value lands. (An untyped
        // `Opaque` fold was refused above, so it never reaches here.)
        let mask = if width >= 64 { u64::MAX } else { (1u64 << width) - 1 };
        Ok(Some((smt::word(r as u64 & mask, width), out)))
    }

    /// Resize a constant operand to `wide` bits, refusing one that does not fit.
    ///
    /// Widening is exact: zero-extend unsigned, sign-extend signed. Narrowing is
    /// where a contract can be wrong rather than merely imprecise -- `a <= 300`
    /// for a `u8` would become `a <= 44` if the value were truncated -- so a
    /// value that does not fit is an error and the function is skipped, not a
    /// weaker proof.
    ///
    /// The check runs at *equal* width too, which is what `own_signed` is for. A
    /// bare literal is non-negative, but a signed bound (`i8::MIN`) or a negation
    /// (`-1`) is its two's-complement value; `128` and `i8::MIN` share the bit
    /// pattern `0x80` and mean different things. Without the distinction, `128`
    /// meeting an `i8` was accepted as the bit pattern for `-128`, so `x <= 128`
    /// was read as `x <= -128` -- a wrong value, and a false proof (`ensures: x !=
    /// 127` "held"). The constant's `Sign` tells the two apart: a non-negative
    /// literal is checked as `+val`, a signed one as its two's-complement value, and
    /// an *opaque* one (`!0`) takes the operand's sign, which is the type Rust infers
    /// for it.
    fn resize_const(
        &self,
        v: Var,
        wide: u8,
        signed: bool,
        own: Sign,
    ) -> Result<Var, SpecError> {
        let w = smt::bits(v);
        let val = self.const_value(v).expect("resize_const is only called on a constant");
        // Every literal and every constant `+ - *` intermediate in the term is
        // range-checked against the type it meets here, not only the value that
        // reaches the comparison: `2 & 128` is an `i8` error although its value is
        // `0`. This is what makes a contract the reader would otherwise decide on a
        // rustc-rejected program a refusal instead.
        self.check_range(v, wide, signed)?;
        // An *opaque* constant (`!0`, or a fold that touched a complement) is held
        // at the *scope's* width, and its value depends on the operand width Rust
        // would infer -- `!0` is `-1`/`255`/`65535` by context. A *narrowing* to the
        // operand is exact (the complement at width W is the low W bits of the
        // scope-width complement), so it truncates without a value check. A
        // *widening* cannot be modelled: no fixed extension of the scope-width
        // pattern recovers the operand-width value, and guessing was the false
        // proof (`!0 + 2` read as `257` and truncated into an `i16`).
        //
        // The value check the plain-literal path performs is *not* the one that
        // applies here. A complement's value is always the operand's low `W` bits,
        // so it fits any `W` by construction; what Rust range-checks is the
        // complement's *operand*, against the type the complement meets. `!128`
        // for an `i8` is a `literal out of range for i8` error even though the
        // reader holds `127`, and truncating that to the operand silently turned a
        // rejected program into `y <= 127` -- `i8::MAX` -- which *verified*. So the
        // tracked operand is checked against the operand type here.
        if own.is_opaque() {
            if wide > w {
                return Err(self.err(
                    "a widening of an untyped constant is not modelled: its value depends on the \
                     operand's width, which is not known where it is read",
                ));
            }
            if let Some((lo, hi)) = own.opaque_operand() {
                // The type the complement meets is the operand's: signed up to
                // `2^(W-1) - 1`, unsigned up to `2^W - 1`. A tracked operand
                // literal that exceeds it is a shape rustc rejects, so the contract
                // is refused. The envelope is the operand literals' union, so a
                // literal anywhere under the complement is checked (`!(128 - 63)`
                // is refused for its `128`), and its *low* end is checked too: a
                // negated operand can leave the envelope negative (`!(-7)`).
                let (min, max) = if signed {
                    (-(1i128 << (wide - 1)), (1i128 << (wide - 1)) - 1)
                } else {
                    (0, (1i128 << wide) - 1)
                };
                if lo < min || hi > max {
                    let shown = if lo < min { lo } else { hi };
                    return Err(self.err(format!(
                        "the complement of `{shown}` does not fit the operand's {wide}-bit \
                         {} type, so the shape is refused",
                        if signed { "signed" } else { "unsigned" }
                    )));
                }
            }
            return Ok(if wide < w { smt::truncate(v, wide) } else { v });
        }
        // A *typed* constant -- a bare literal (non-negative) or a signed
        // bound/negation (two's-complement) -- has its own signedness, and that is
        // what decides whether it fills or sign-extends.
        let effective_signed = own.eval();
        // The value the constant denotes, at its own width. A literal written
        // without a type is non-negative; a signed bound or a negation is its
        // two's-complement value.
        let sval: i128 = if effective_signed {
            if w >= 64 {
                val as i64 as i128
            } else if val & (1u64 << (w - 1)) != 0 {
                val as i128 - (1i128 << w)
            } else {
                val as i128
            }
        } else {
            val as i128
        };
        let fits = if signed {
            let lo = -(1i128 << (wide - 1));
            let hi = (1i128 << (wide - 1)) - 1;
            sval >= lo && sval <= hi
        } else {
            sval >= 0 && (sval as u128) < (1u128 << wide)
        };
        if !fits {
            // Report the value as written: a signed constant (`-129`, `i8::MIN`)
            // reads as its negative value, not the two's-complement bit pattern,
            // so the message names the number the contract author wrote.
            let shown: i128 = if effective_signed { sval } else { val as i128 };
            return Err(self.err(format!(
                "literal {shown} does not fit the operand's {wide}-bit width"
            )));
        }
        // Truncate rather than rebuild from `val`. A negative literal is the bit
        // pattern `2^w - 10` at its *source* width, so `word(val, wide)` would be
        // handed a value that does not fit `wide` and would set the engine's
        // ill-formed flag -- turning a valid contract into `Unknown`. Truncation
        // takes the low `wide` bits, which is the same bit pattern the value
        // denotes, and the `fits` check above is what keeps it from being silent.
        //
        // How a *widened* constant fills the new high bits follows the value it
        // *denotes*, which is `effective_signed`. A bare literal is non-negative, so
        // it zero-extends: Rust's `(255u8 as i16) == 255` is *true*, and filling
        // from the operand's sign instead sign-extended the `255` to `65535` and
        // *refuted* a postcondition Rust accepts -- a false refutation, the mirror
        // of a false proof. A typed signed constant (`-1`, a `MIN` bound)
        // sign-extends. An opaque constant never reaches here: it returned above.
        if wide >= w {
            Ok(if effective_signed && wide > w {
                smt::sign_extend(v, wide)
            } else {
                smt::word(val, wide)
            })
        } else {
            Ok(smt::truncate(v, wide))
        }
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
    fn align_widths(
        &self,
        a: Var,
        sa: Sign,
        b: Var,
        sb: Sign,
        signed: Sign,
    ) -> Result<(Var, Var), SpecError> {
        let signed = signed.eval();
        let (wa, wb) = (smt::bits(a), smt::bits(b));
        // Which operand is a *bare* literal, or a bare negation of one, and so
        // has no type of its own: Rust infers its width from the operand it meets,
        // and only such a value may be resized to the other side (`Sign::Literal`).
        //
        // Every other constant carries a type of its own -- a suffix (`1i8`), a
        // named bound (`i8::MIN`), a cast, or a fold with a typed operand -- and a
        // width mismatch between it and a typed partner is a Rust error (`E0308`),
        // not a resize. Resizing it instead let `-1i8 < (x as i16)` and
        // `1i8 == 1i16` *verify* although rustc rejects both: the signedness gate
        // sees two signed operands and passes, so the width was the only remaining
        // evidence, and it was being erased.
        let a_adapts = sa.adapts();
        let b_adapts = sb.adapts();
        let mismatch = || self.err("operands of different widths cannot be combined");
        match (self.const_value(a), self.const_value(b)) {
            // Both constants: give the pair one width. The range check runs on
            // whichever operand is resized: a contract that meets no typed name
            // still has to be one rustc would accept. `128 <= i8::MAX` is a
            // `literal out of range` error in Rust, and without the check here it
            // read as `-128 <= 127` -- always true -- so the shape is refused
            // rather than decided. A bare literal is checked as `+val` and a named
            // bound as its two's-complement value (see `resize_const`), so
            // `i8::MIN <= i8::MAX` still reads while `128 <= i8::MAX` does not.
            //
            // A *bare* literal's width is only a placeholder (it holds its value
            // at the scope's width); it must take the *other* operand's width,
            // whichever side is wider. Aligning to the narrower unconditionally
            // instead resized the *wider* side down -- `128i16 as i32 == 128`,
            // where the cast result is 32 bits and the literal is 8, narrowed the
            // 32-bit `128` to eight bits and refused a valid comparison.
            //
            // With *neither* operand a bare literal the two types are both fixed,
            // so a width mismatch is the Rust error and is refused; at equal width
            // the resize is the identity term but the range check still runs.
            (Some(_), Some(_)) => match (a_adapts, b_adapts) {
                (true, false) => Ok((self.resize_const(a, wb, signed, sa)?, b)),
                (false, true) => Ok((a, self.resize_const(b, wa, signed, sb)?)),
                (false, false) => {
                    if wa == wb {
                        let a = self.resize_const(a, wa, signed, sa)?;
                        let b = self.resize_const(b, wb, signed, sb)?;
                        Ok((a, b))
                    } else {
                        Err(mismatch())
                    }
                }
                (true, true) => {
                    if wa > wb {
                        Ok((self.resize_const(a, wb, signed, sa)?, b))
                    } else if wb > wa {
                        Ok((a, self.resize_const(b, wa, signed, sb)?))
                    } else {
                        let a = self.resize_const(a, wa, signed, sa)?;
                        let b = self.resize_const(b, wb, signed, sb)?;
                        Ok((a, b))
                    }
                }
            },
            // One constant: resize it to the other operand's width. This runs at
            // *equal* width too, where the resize is the identity term but the
            // range check is not: `128` meeting an `i8` must be refused, not read
            // as the bit pattern for `-128`. Skipping the call at equal width is
            // what let `x <= 128` mean `x <= -128` -- a wrong value and a false
            // proof. `sa`/`sb` carry each constant's own signedness, so a bare
            // literal (non-negative) is told apart from a signed bound that
            // happens to share its bit pattern.
            //
            // A constant whose type is *fixed* (not a bare literal) may only meet
            // a name of its own width; a mismatch is refused, as above.
            (Some(_), None) => {
                if a_adapts || wa == wb {
                    Ok((self.resize_const(a, wb, signed, sa)?, b))
                } else {
                    Err(mismatch())
                }
            }
            (None, Some(_)) => {
                if b_adapts || wa == wb {
                    Ok((a, self.resize_const(b, wa, signed, sb)?))
                } else {
                    Err(mismatch())
                }
            }
            (None, None) => {
                if wa == wb {
                    Ok((a, b))
                } else {
                    Err(mismatch())
                }
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
        if self.bang_is_predicate() && self.eat_op("!") {
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
                // language will not compare an `i8` with a `u8`), so the typed
                // operand decides it and a literal on one side leaves the other to
                // say. With *no* typed operand the reading is a guess, and where
                // the two readings differ the shape is refused.
                //
                // The two readings differ whenever an operand is `Opaque` -- an
                // untyped constant that is not a bare literal (the complement of
                // one, or a fold of untyped operands). Such a constant has no type
                // of its own, and Rust defaults an untyped constant to `i32`, so
                // `!0` is `-1` and `!0 == 255` is `false`; the reader carries the
                // complement as a bit pattern at the scope's width, so it built
                // `255u8 == 255` and *verified* `ensures: !0 == 255` -- a false
                // proof, and one the maintainer's ordering-only refusal left open
                // because `==`/`!=` "compare bit patterns". They do not here: the
                // two readings are different *values* (`-1` vs `255`), not a
                // different ordering of one value. So an opaque operand with no
                // typed partner is refused at *every* comparison, not only the
                // ordering ones. Two bare literals stay unambiguous (`2 == 2`), and
                // any typed operand fixes the reading, so the common cases read.
                let signed = match Sign::resolve(ls, rs) {
                    Some(b) => b,
                    None => {
                        if ls.ambiguous() || rs.ambiguous() {
                            return Err(self.err(
                                "a comparison with no typed operand is sign-ambiguous: an untyped \
                                 constant reads differently as signed and as unsigned",
                            ));
                        }
                        false
                    }
                };
                // A *signed* constant cannot meet an *unsigned* typed operand.
                // Rust infers a literal's type from the operand it is compared
                // with, and `x == -1` for a `u8` does not compile ("cannot apply
                // unary operator `-` to type `u8`"). The reader carries the
                // negation as a bit pattern at the operand's width, so it would
                // read `x == -1` as `x == 255` -- a wrong *value*, and
                // `ensures: ret == 255` was verified for a body returning `x`,
                // which is a false proof. So the shape is refused.
                self.refuse_mixed_signedness(left, ls, right, rs)?;
                // A literal is written without a type, so its width comes from
                // the operand it meets. Sizing it from the widest name in scope
                // makes `ret <= 255` a 64-bit comparison whenever a slice or
                // array length is also in scope, and an 8-bit `ret` against a
                // 64-bit constant is ill-formed -- which poisons *every*
                // obligation in the run, not just this one.
                let (left, right) =
                    self.align_widths(left, ls, right, rs, Sign::from_bool(signed))?;
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

    /// An arithmetic expression, plus whether it is *signed*.
    ///
    /// The flag is carried alongside the value because a comparison's meaning
    /// depends on it, and the grammar has no casts or type names to recover it
    /// later. An expression is signed when any name in it is, which is exact:
    /// Rust would reject a mixed-sign arithmetic expression.
    ///
    /// The ladder mirrors Rust's precedence, so the entry point is the *loosest*
    /// level and each level's operands are the next tighter one:
    /// `|` < `^` < `&` < `<< >>` < `+ -` < `* / %`. Getting this order wrong is
    /// not a cosmetic matter: `x & 1 + 1` is `x & (1 + 1)` in Rust, and reading it
    /// as `(x & 1) + 1` makes a contract pass or fail against a different number.
    fn parse_expr(&mut self) -> Result<(Var, Sign), SpecError> {
        self.parse_bitor()
    }

    fn parse_bitor(&mut self) -> Result<(Var, Sign), SpecError> {
        let (mut left, mut sgn) = self.parse_bitxor()?;
        while self.eat_op("|") {
            let (r, rs) = self.parse_bitxor()?;
            self.refuse_mixed_signedness(left, sgn, r, rs)?;
            let (pl, pr) = (left, r);
            let (l, r) = self.align_widths(left, sgn, r, rs, Sign::combine(sgn, rs))?;
            left = smt::bor(l, r);
            self.record_range_union(left, pl, pr);
            sgn = Sign::combine(sgn, rs);
        }
        Ok((left, sgn))
    }

    fn parse_bitxor(&mut self) -> Result<(Var, Sign), SpecError> {
        let (mut left, mut sgn) = self.parse_bitand()?;
        while self.eat_op("^") {
            let (r, rs) = self.parse_bitand()?;
            self.refuse_mixed_signedness(left, sgn, r, rs)?;
            let (pl, pr) = (left, r);
            let (l, r) = self.align_widths(left, sgn, r, rs, Sign::combine(sgn, rs))?;
            left = smt::bxor(l, r);
            self.record_range_union(left, pl, pr);
            sgn = Sign::combine(sgn, rs);
        }
        Ok((left, sgn))
    }

    fn parse_bitand(&mut self) -> Result<(Var, Sign), SpecError> {
        let (mut left, mut sgn) = self.parse_shift()?;
        while self.eat_op("&") {
            let (r, rs) = self.parse_shift()?;
            self.refuse_mixed_signedness(left, sgn, r, rs)?;
            let (pl, pr) = (left, r);
            let (l, r) = self.align_widths(left, sgn, r, rs, Sign::combine(sgn, rs))?;
            left = smt::band(l, r);
            self.record_range_union(left, pl, pr);
            sgn = Sign::combine(sgn, rs);
            // `a & mask` is a width-independent *value* when the *whole* result
            // is constant and the mask is width-independent: `&` keeps only the
            // mask's low bits, which are the same at any width, so `(!0 & 1)` is
            // `1` at any width and may widen exactly like a literal. Only that
            // case is marked `Literal` -- carrying it as opaque refused the
            // widening, dropping `(x as u16) == (!0 & 1)`.
            //
            // A *symbolic* masked operand must keep its own sign. Marking it
            // `Literal` would erase a typed argument's type: `x & 128` for a `u8`
            // is still a `u8`, and `Literal` made `refuse_mixed_signedness` accept
            // `(x & 128) == y` for a signed `y`, a pairing rustc rejects (E0308).
            //
            // A *constant* result may be marked `Literal` (a width-independent
            // value that may widen) only when **neither operand carries a type**.
            // A typed operand -- signed *or* unsigned -- fixes the result's type,
            // and `&` cannot erase it: `-1i8 & 1` is an `i8` and `1u8 & 1` is a
            // `u8`, even though both compute the small positive `1`. Marking
            // either `Literal` hid the type, so `(...) == y` against a partner of
            // the *other* signedness -- `E0308` in Rust -- was read as `1 == y`
            // and decided. `(!0 & 1)` has no typed operand (`!0` is `Opaque`, `1`
            // a bare literal), so it still widens exactly.
            if self.const_value(left).is_some()
                && (sgn == Sign::Literal || rs == Sign::Literal)
                && Sign::combine(sgn, rs).typed().is_none()
            {
                // `&` keeps only the mask's low bits, so the *value* is
                // width-independent and may widen like a literal -- but the operand
                // literals are still range-checked by Rust (`!200 & 64` is rejected
                // for its `200`, `!128 & 255` for its `128`). Those literals travel
                // in the operands' `Opaque` envelopes, not the `range` map, so they
                // must be folded into the result *before* the sign is downgraded and
                // the envelopes are lost. The result term is a compound `&` node,
                // never hash-consed with a bare literal, so recording on it cannot
                // pollute an unrelated constant the way the complement's own value
                // term did.
                if let Some((lo, hi)) = Sign::union_env(sgn.opaque_operand(), rs.opaque_operand()) {
                    self.record_range(left, lo, hi);
                }
                sgn = Sign::Literal;
            }
        }
        Ok((left, sgn))
    }

    /// The width Rust infers for the shift amount at the cursor, so the amount's
    /// bare literals are floored at that width instead of a blind `i32`.
    ///
    /// An amount's type is not tied to the shifted operand's, so an unsuffixed
    /// amount defaults to `i32`. A *typed* operand at the amount's own level -- a
    /// suffixed literal (`1u8`), a cast (`n as u8`) -- instead fixes the amount's
    /// type to its width, and every bare literal in the amount takes that width.
    /// Reading `1u8 + (2 << 7)` as `i32` built the inner `2 << 7` as `256` and
    /// refused a shift rustc accepts (`2 << 7` is `0u8` there, so the amount is
    /// `1u8`).
    ///
    /// The scan mirrors the grammar rather than flattening it, because only an
    /// operand at the *amount's own level* fixes its type. In `2 << 7u8` the suffix
    /// is inside the nested shift's *amount*, not an operand of the outer shift, so
    /// it does not make the outer amount `u8`: the outer amount is the `i32`
    /// `2 << 7u8` = `256`, a rustc overflow. A flat scan that took any suffix would
    /// read the outer amount as `u8` and accept a program rustc rejects.
    fn amount_width(&self) -> u8 {
        match self.scan_amount_add(self.pos).0 {
            0 => 32,
            w => w,
        }
    }

    /// Scan an add-level term (the amount's own level) for a typed operand,
    /// returning its width and the index just past the scanned span.
    fn scan_amount_add(&self, mut i: usize) -> (u8, usize) {
        loop {
            let (w, j) = self.scan_amount_mul(i);
            if w != 0 {
                return (w, j);
            }
            i = j;
            match self.toks.get(i) {
                Some(Tok::Op(o)) if o == "+" || o == "-" => i += 1,
                _ => return (0, i),
            }
        }
    }

    /// Scan a mul-level term for a typed operand.
    fn scan_amount_mul(&self, mut i: usize) -> (u8, usize) {
        loop {
            let (w, j) = self.scan_amount_atom(i);
            if w != 0 {
                return (w, j);
            }
            i = j;
            match self.toks.get(i) {
                Some(Tok::Op(o)) if o == "*" || o == "/" || o == "%" => i += 1,
                _ => return (0, i),
            }
        }
    }

    /// Scan one atom (any unary prefixes, and a trailing cast) for a typed width.
    ///
    /// A parenthesized group is scanned at the amount's own level, so a suffix
    /// inside a nested shift's amount is not mistaken for the amount's own type.
    /// A cast fixes the width and *overrides* what it casts -- `(1u8) as u16` is a
    /// `u16` amount, so the inner `1u8` must not win.
    fn scan_amount_atom(&self, i: usize) -> (u8, usize) {
        let mut i = i;
        while matches!(self.toks.get(i), Some(Tok::Op(o)) if o == "-" || o == "!") {
            i += 1;
        }
        let (mut w, mut j) = match self.toks.get(i) {
            Some(Tok::Num(_, Some((w, _)))) => (u8::min(*w, 64), i + 1),
            Some(Tok::Op(o)) if o == "(" => (self.scan_amount_add(i + 1).0, self.after_paren(i)),
            _ => (0, i + 1),
        };
        if matches!(self.toks.get(j), Some(Tok::Ident(n)) if n == "as") {
            if let Some(Tok::Ident(ty)) = self.toks.get(j + 1) {
                if let Some(cw) = Ty::parse(ty).width() {
                    w = cw.min(64);
                    j += 2;
                }
            }
        }
        (w, j)
    }

    /// The index just past the `)` matching the `(` at `i`.
    fn after_paren(&self, i: usize) -> usize {
        let mut depth = 0usize;
        let mut j = i;
        while let Some(t) = self.toks.get(j) {
            match t {
                Tok::Op(o) if o == "(" => depth += 1,
                Tok::Op(o) if o == ")" => {
                    depth -= 1;
                    if depth == 0 {
                        return j + 1;
                    }
                }
                _ => {}
            }
            j += 1;
        }
        j
    }

    /// The shift level: `<<` and `>>`, which bind tighter than `&` but looser
    /// than `+`.
    ///
    /// Two things make a shift unlike the other operators. Its result has the
    /// *left* operand's width, so the amount is a count rather than a value of
    /// that width and the two operands are deliberately *not* width-aligned. And
    /// `>>` means arithmetic or logical according to the left operand's sign, so
    /// a signed operand is the only thing that separates them -- which is why the
    /// signedness carried through decides it.
    ///
    /// The amount must be a *constant*. A symbolic amount is a barrel shifter
    /// (see `smt::shift_var`), and modelling one in a contract would mean
    /// agreeing with the body about what happens when the amount reaches the
    /// width -- a case rustc turns into a panic before the shift. Rather than
    /// guess at that interaction, a symbolic amount is refused, which leaves the
    /// function visibly undecided instead of silently mis-modelled. A constant at
    /// or above the width is a compile error in Rust and is refused here too.
    fn parse_shift(&mut self) -> Result<(Var, Sign), SpecError> {
        let (mut left, sgn) = self.parse_add()?;
        while let Some(op) = self.eat_any(&["<<", ">>"]) {
            // The amount is a value of its *own* type, unconstrained by the
            // operand, so its bare literals are floored at the amount's inferred
            // width (`amount_width`): `i32` when nothing in the amount fixes a
            // type, or a typed operand's width when one does. The *operand* is not
            // floored: rustc reads `(2 << 7)` in an `i8` comparison at eight bits
            // (it accepts `y == (2 << 7)`, which is `y == 0` there).
            //
            // The floor is inherited, not recomputed, when the shift is itself
            // inside an amount: the enclosing type unifies inward through the
            // parentheses, so `x >> (1u8 + (2 << 7))` folds the inner `2 << 7` at
            // eight bits. Recomputing from the inner amount's own tokens would miss
            // the outer `1u8` and build `256`, refusing a shift rustc accepts.
            let saved = self.amount_floor;
            self.amount_floor = if saved == 0 { self.amount_width() } else { saved };
            let amount = self.parse_add();
            self.amount_floor = saved;
            let (r, rs) = amount?;
            // An *opaque* amount (a complement, or a fold that touched one) has no
            // width of its own: `!254` is `-255` at the `i32` Rust infers -- a
            // negative shift amount, and an overflow error -- but `1` at eight bits.
            // Its value, and whether the shift is in range at all, depends on the
            // width the result is read at, so the shape is refused rather than read
            // at the scope's width. A bare literal or a fold of bare literals has
            // one value at any width (`1 + 1` is `2`), and `!0 & 1` is masked to
            // `1` and marked `Literal`, so those still read.
            if rs.is_opaque() {
                return Err(self.err(
                    "a shift amount that is an untyped complement is not modelled: its value \
                     depends on the operand's width",
                ));
            }
            // The amount must be *constant*, but not necessarily a bare literal:
            // `x >> 1 + 1` is `x >> 2` in Rust, and the additive level above has
            // already folded it. `const_value` evaluates a variable-free term, so a
            // folded constant is accepted while a symbolic amount still falls
            // through to the refusal below. Using the raw-literal `const_of` here
            // instead made `x >> 1 + 1` unreadable -- a dropped obligation on a
            // shape rustc accepts, and one the README's own examples use.
            let Some(k) = self.const_value(r) else {
                return Err(self.err("a shift amount in a contract must be a constant"));
            };
            let base = left;
            let w = smt::bits(left);
            if k >= w as u64 {
                return Err(self.err(format!(
                    "shift amount {k} is not below the operand width {w}"
                )));
            }
            // An *untyped* operand has no width of its own: Rust infers it from
            // where the shift result is read, and that is not known here. The width
            // can be as narrow as 8 bits, so a shift of an untyped constant is
            // refused unless it is valid at *every* width it could be read at: the
            // amount below 8, and a literal operand that fits an 8-bit signed
            // value. Without this, the amount was checked against the *scope's*
            // width (32, from the `u32` name in scope), so `255 >> 8` passed and
            // `255 >> 8 <= x` for a `u8` `x` *verified* -- for a program rustc
            // rejects as an overflow (`255` is a `u8`, and a shift by its own width
            // is a compile error). The operand's value was never range-checked
            // either, so `(255 >> 1) >= y` for an `i8` `y` verified although rustc
            // rejects `255` as `literal out of range for i8`.
            //
            // An `Opaque` operand (a complement, or a fitted fold) needs no value
            // check: its value at any width is `-1`/`2^W - 1`, which fits that
            // width by construction.
            if !sgn.fixes_type() {
                if k >= 8 {
                    return Err(self.err(format!(
                        "a shift of an untyped constant by {k} is refused: the operand's width is \
                         inferred from where the result is read, and {k} is not below the \
                         narrowest width"
                    )));
                }
                if matches!(sgn, Sign::Literal | Sign::NegLiteral) {
                    let sval = self.signed_value(left, sgn.eval());
                    if !(-128..=127).contains(&sval) {
                        return Err(self.err(format!(
                            "a shift of an untyped constant {sval} is refused: the operand's width \
                             is inferred from where the result is read, and {sval} does not fit \
                             the narrowest width"
                        )));
                    }
                }
            }
            left = if op == "<<" {
                // A left shift of an untyped constant is sign-insensitive (the bit
                // pattern is the same either way), so it keeps its `Untyped` state.
                smt::shl(left, k as u32)
            } else if k == 0 {
                // A shift by zero is the identity: it preserves the exact bit
                // pattern under *both* readings, so even an opaque constant is
                // unambiguous. `!0 >> 0` is `!0` -- `255` at 8 bits, `-1` at signed
                // -- and its sign stays `Opaque` until the surrounding expression
                // fixes a type. Refusing it before this check dropped a valid
                // postcondition (`ret == (!0 >> 0)`).
                left
            } else {
                match sgn {
                    Sign::Signed | Sign::NegLiteral => smt::ashr(left, k as u32),
                    // An untyped *bare literal* (a small non-negative value) shifts
                    // the same either way, so the unsigned reading is exact.
                    Sign::Unsigned | Sign::Literal => smt::lshr(left, k as u32),
                    // `>>` of an *opaque* untyped constant (the complement of a
                    // literal, or a fold of untyped operands) is the false proof's
                    // shape: with no typed operand the reader has no sign to pick,
                    // and the two readings differ (`!0 >> 1` is `-1` arithmetic,
                    // `127` logical). Refuse rather than guess.
                    Sign::Opaque(_) => {
                        return Err(self.err(
                            "a right shift with no typed operand is sign-ambiguous: it reads \
                             differently as an arithmetic and as a logical shift",
                        ))
                    }
                }
            };
            // The shift's operand literals are still checked by Rust
            // (`128 >> 0` is rejected for its `128`), so they carry through.
            self.record_range_union(left, base, base);
        }
        Ok((left, sgn))
    }

    /// The additive level: `+` and `-`, tighter than the bitwise operators.
    fn parse_add(&mut self) -> Result<(Var, Sign), SpecError> {
        let (mut left, mut sgn) = self.parse_mul()?;
        while let Some(op) = self.eat_any(&["+", "-"]) {
            let (r, rs) = self.parse_mul()?;
            // A signed constant added to an unsigned name (`x + -1` for a `u8`) is
            // a rustc error, and reading the negation as `255` would prove
            // `x + -1 >= 0` for every `x` -- a false proof, exactly as at the
            // comparison level. Refused before the operands are aligned.
            self.refuse_mixed_signedness(left, sgn, r, rs)?;
            // Capture the pre-align operands: `align_widths` rebuilds a constant
            // at the common width, and the rebuilt term carries no envelope, so the
            // union must be taken from the terms the literals were recorded on.
            let (pl, pr) = (left, r);
            let (l, r) = self.align_widths(left, sgn, r, rs, Sign::combine(sgn, rs))?;
            // A constant sum or difference is folded *exactly*, so a result that
            // overflows the operand width is refused (as rustc refuses the
            // constant expression) instead of wrapping to a wrong value. A result
            // that fits is left to the ordinary operator.
            if let Some((v, s)) = self.fold_const_arith(op, l, sgn, r, rs)? {
                self.record_fold_result(v, pl, pr, s);
                left = v;
                sgn = s;
                continue;
            }
            left = if op == "+" { smt::add(l, r) } else { smt::sub(l, r) };
            self.record_fold_result(left, pl, pr, Sign::combine(sgn, rs));
            sgn = Sign::combine(sgn, rs);
        }
        Ok((left, sgn))
    }

    /// The multiplicative level: `*`, `/` and `%`, the tightest arithmetic.
    ///
    /// Division and remainder take the *signed* engine when either operand is
    /// signed, the same choice the body makes and for the same reason: the
    /// unsigned divider returns a huge positive quotient for `-7 / 2`, a wrong
    /// value rather than a weaker proof. A *constant* zero divisor is refused, in
    /// whatever form it is written -- `0`, `1 - 1`, `2 - 2` -- because Rust rejects
    /// it at compile time, so a contract carrying one is malformed, not merely
    /// imprecise. A *symbolic* divisor is modelled exactly (the engine's divider is
    /// total), which mirrors the body.
    fn parse_mul(&mut self) -> Result<(Var, Sign), SpecError> {
        let (mut left, mut sgn) = self.parse_cast()?;
        while let Some(op) = self.eat_any(&["*", "/", "%"]) {
            let (r, rs) = self.parse_cast()?;
            // The divisor must be checked for *zero*, not for "is a bare zero
            // literal". `x % (1 - 1)` folds to `x % 0` at the additive level, and
            // the raw-literal `const_of` missed it, so the reader built `srem(x, 0)`
            // -- an undefined operation the engine nevertheless evaluates -- and
            // produced a definite verdict from it. A *constant* zero is refused
            // however it is spelled; a symbolic divisor is still modelled exactly.
            if op != "*" && self.const_value(r) == Some(0) {
                return Err(self.err("a division or remainder by a constant zero"));
            }
            // A signed constant divisor with an unsigned name (`x % -1` for a
            // `u8`) is a rustc error, and the negation read as `255` would build
            // `urem(x, 255)` -- a value the author never wrote. Same refusal as the
            // additive and comparison levels.
            self.refuse_mixed_signedness(left, sgn, r, rs)?;
            // A `/` or `%` with no typed operand and an *opaque* constant (the
            // complement of a literal, or a fold) is sign-ambiguous: `!4 / 2` is
            // `125` unsigned and `-2` signed, and the reader would take the unsigned
            // engine. Refuse rather than guess. A bare literal is unambiguous, and a
            // typed operand fixes the reading.
            //
            // The test is `Sign::resolve`, not "does either side evaluate signed":
            // `eval()` is `false` for both `Unsigned` and `Opaque`, so an unsigned
            // name beside `!0` (`x / !0` for a `u8`) was mistaken for a pair with
            // no typed operand and refused, though `resolve` reads the unsigned
            // type off `x` and the division is well-modelled. Only a genuinely
            // untyped pair (`!0 / !1`) is refused.
            if op != "*" && Sign::resolve(sgn, rs).is_none() && (sgn.ambiguous() || rs.ambiguous())
            {
                return Err(self.err(
                    "a `/` or `%` with no typed operand is sign-ambiguous: it reads differently \
                     as signed and as unsigned",
                ));
            }
            // Same width rule as the other operators: a literal product, divisor
            // or mask is sized to the operand it meets.
            let (pl, pr) = (left, r);
            let (l, r) = self.align_widths(left, sgn, r, rs, Sign::combine(sgn, rs))?;
            // A constant `/` or `%` can overflow (`i8::MIN / -1`), which rustc
            // rejects; the fold refuses it rather than wrapping. `*` is folded
            // exactly, so a constant product too wide for the operand is refused
            // instead of wrapping to a wrong value.
            if let Some((v, s)) = self.fold_const_arith(op, l, sgn, r, rs)? {
                self.record_fold_result(v, pl, pr, s);
                left = v;
                sgn = s;
                continue;
            }
            let signed = sgn.eval() || rs.eval();
            left = match op {
                "*" => smt::mul(l, r),
                "/" if signed => smt::sdiv(l, r),
                "/" => smt::udiv(l, r),
                "%" if signed => smt::srem(l, r),
                _ => smt::urem(l, r),
            };
            self.record_fold_result(left, pl, pr, Sign::combine(sgn, rs));
            sgn = Sign::combine(sgn, rs);
        }
        Ok((left, sgn))
    }

    /// Consume whichever of `ops` is at the cursor, returning the one matched.
    fn eat_any<'b>(&mut self, ops: &[&'b str]) -> Option<&'b str> {
        if let Some(Tok::Op(o)) = self.peek() {
            for op in ops {
                if o == op {
                    self.pos += 1;
                    return Some(op);
                }
            }
        }
        None
    }

    /// The cast level: a unary-negated primary, then any `as <type>` chain.
    ///
    /// Rust binds unary `-` *tighter* than `as`, so `-x as u8` is `(-x) as u8`,
    /// not `-(x as u8)`. The two readings agree on the *value* here (negation and
    /// truncation commute) but not on the *type*: Rust's is `u8`, and `-(...)` is
    /// signed. That difference is observable — `-x as u8 > 127` is satisfiable
    /// (`x == 1` gives `255`), where the signed reading is `i8 > 127`, which no
    /// input satisfies, so the function is reported *vacuous* instead of verified.
    /// Hence the negation is applied to the primary first, and the cast chain runs
    /// after it.
    fn parse_cast(&mut self) -> Result<(Var, Sign), SpecError> {
        let (v, sgn) = self.parse_neg()?;
        self.cast_chain(v, sgn)
    }

    /// A unary negation, applied to the primary below it and *before* any cast.
    ///
    /// The result is signed whatever the operand was. Negation is only defined on
    /// a signed type in Rust (`let x: u32 = -1;` does not compile), so a negation
    /// *is* the evidence that the expression is signed. The operand's own flag
    /// cannot be used: `-7` negates the literal `7`, which is unsigned, and
    /// reading the flag through would make `-7 % 3` take the unsigned remainder
    /// (`4294967289 % 3`, i.e. `0`) where Rust says `-1`. Only `% / >>` and the
    /// comparisons consult the flag, so the mistake is a *wrong value* rather than
    /// a refusal -- the one outcome a verifier must not produce silently.
    fn parse_neg(&mut self) -> Result<(Var, Sign), SpecError> {
        if self.eat_op("-") {
            let (v, sgn) = self.parse_neg()?;
            // Rust rejects `-x` for an unsigned `x` (`E0600: cannot apply unary
            // operator `-` to type `u8``). The reader models the negation as
            // `0 - x` at the operand's width, which is a *value* Rust never
            // produces, so the shape is refused rather than decided -- the same
            // answer as the mixed-signedness pair. A bare literal is untyped (Rust
            // defaults it to a signed `i32`) and a signed operand is legal, so
            // `-5` and `-x` for an `i8` still read.
            if sgn == Sign::Unsigned {
                return Err(self.err("cannot apply unary `-` to an unsigned operand"));
            }
            let w = smt::bits(v);
            // The negation of a *bare* literal keeps the literal's adaptive width
            // (`-1 < (x as i16)` is well-typed), so it is `NegLiteral`; the
            // negation of a suffixed or bound constant (`-1i8`, `-i8::MIN`) keeps
            // that constant's fixed width, so it is `Signed`. Both are signed.
            let out = if sgn == Sign::Literal { Sign::NegLiteral } else { Sign::Signed };
            // A negated *constant* is widened by one bit when its magnitude does
            // not fit signed at its own width, so the true value survives for the
            // later range check. `-129` for an `i8` is a Rust error ("literal out
            // of range"), but at 8 bits the two's-complement `-129` *is* `127`, so
            // the negation alone would hand the check a value that fits and
            // `x >= -129` would silently mean `x >= 127` -- a false proof, the
            // mirror of the bare-literal wrap. One spare bit keeps `-129` as
            // `-129`, which the check then refuses. `-128` (i8::MIN) still fits at
            // 8 bits, so it is left alone.
            let bare = self.bare_literals.contains(&v.0 .0);
            if let Some(mag) = self.const_value(v) {
                // `-mag` fits signed at `w` bits iff `mag <= 2^(w-1)`.
                let fits = w >= 64 || mag <= (1u64 << (w - 1));
                if !fits {
                    let nv = smt::sub(smt::word(0, w + 1), smt::word(mag, w + 1));
                    self.record_negation(nv, v, true);
                    return Ok((nv, out));
                }
                // A constant that denotes a *value* rather than a written
                // magnitude -- a named bound (`i8::MIN`), an inner negation, or a
                // fold that wrapped to the type's minimum (`3 << 7` at eight bits)
                // -- negates to `-sval`, and that is the value Rust checks.
                // `i8::MIN` is the bit pattern `128` and the value `-128`;
                // negating the *value* is `+128`, out of range, where negating the
                // literal `128i8` is `-128`, which is not. The magnitude check
                // above reads the bit pattern, which is the same `128` for both, so
                // it passed and the negation overflow went unrecorded: the reader
                // *decided* `y == -(i8::MIN)` and `y == -(3 << 7)` on programs
                // rustc rejects. Only a pristine literal (`-128`, `-(128i8)`,
                // `-(128)`) is exempt, because there the negation *is* what makes
                // the magnitude legal.
                if !bare {
                    let sval: i128 = if w >= 64 {
                        mag as i64 as i128
                    } else if mag & (1u64 << (w - 1)) != 0 {
                        mag as i128 - (1i128 << w)
                    } else {
                        mag as i128
                    };
                    // `-sval` fits a signed `w`-bit type iff it is at most
                    // `2^(w-1) - 1`, i.e. `sval > -2^(w-1)`. The negation is
                    // computed at the *operand's* type, so the overflow is a Rust
                    // error wherever the result is read -- `-(i8::MIN) as i16` does
                    // not compile either -- and the shape is refused here rather
                    // than recorded, which a wider target would re-accept.
                    let fits_neg = if w >= 64 {
                        sval != i64::MIN as i128
                    } else {
                        sval > -(1i128 << (w - 1))
                    };
                    if !fits_neg {
                        return Err(self.err(
                            "negating a signed constant at its own type is out of range, so the \
                             shape is refused",
                        ));
                    }
                }
            }
            // A unary `-` is checked as Rust checks the *negated value*: `-(-128)`
            // is `128`, out of range for an `i8`, where `-128` is fine. The one
            // exception is a pristine bare literal (`-128`), whose magnitude is
            // *replaced* by the negation rather than checked, so the operand's own
            // value is not carried through -- but a literal inside a fold is
            // (`-(128 - 63)` is rejected for its `128`).
            let nv = smt::sub(smt::word(0, w), v);
            self.record_negation(nv, v, bare);
            // A negated complement carries the complement's operand envelope
            // forward: the negation is a *value*, so the envelope cannot ride in
            // the sign, and `-!128` for an `i8` is a rustc error for the same `128`
            // that `!128` is. The negation term is a compound `Sub` node, never
            // hash-consed with a bare literal, so recording on it cannot pollute an
            // unrelated constant.
            if let Some((lo, hi)) = sgn.opaque_operand() {
                self.record_range(nv, lo, hi);
            }
            return Ok((nv, out));
        }
        // `!` is a unary prefix on a *value* here, because `bang_is_predicate`
        // ruled out the predicate reading above. On an integer it is bitwise NOT,
        // which is `x ^ all_ones` -- the same term the body builds for `UnOp::Not`
        // in `mir/exec.rs`. Reading it at the predicate level instead made
        // `!x == 5` mean `!(x == 5)` (`x != 5`) where Rust means `(!x) == 5`
        // (`x == 250`): a different predicate, so a wrong verdict, not a refusal.
        if self.eat_op("!") {
            let (v, sgn) = self.parse_neg()?;
            // A *typed* operand keeps its sign and width: `!x` for a `u8` is
            // `x ^ 0xFF`, an 8-bit value.
            if sgn.typed().is_some() {
                let w = smt::bits(v);
                return Ok((smt::bxor(v, smt::all_ones(w)), sgn));
            }
            // The complement of an *untyped* constant (`!0`, `!128`) has no type of
            // its own -- it is `-1`/`255`/`65535` according to the operand it meets,
            // so it is carried as `Opaque` and refused at a sign-sensitive operator
            // rather than guessed. It is built as a *constant word* at the scope's
            // width, not as a `bxor` of `all_ones`: the engine folds a `truncate` of
            // a constant word to a constant, but leaves a `truncate` of a compound
            // term as an opaque node, so `ret == !0` was decided against a free
            // 8-bit variable and *refuted* -- a false refutation.
            if self.const_value(v).is_some() {
                let val = self.const_value(v).expect("checked above");
                let w = smt::bits(v);
                let mask = if w >= 64 { u64::MAX } else { (1u64 << w) - 1 };
                // The operand's literal envelope is carried so its fit can be
                // checked against the type the complement meets (`!128` is an `i8`
                // range error). A bare literal operand contributes its value; a
                // nested complement (`!!128`) propagates the innermost envelope,
                // because Rust checks those same literals against the type the
                // outermost complement meets. A fold's operand carries the union of
                // its literals (`!(128 - 63)` is `(63, 128)`). It travels in the
                // `Opaque` payload, *not* in the `range` map: the complement's value
                // is a plain constant (`!128` is `word(127, 8)`), so it is
                // hash-consed with an unrelated bare `127`, and recording the
                // operand's envelope on that shared id refused the innocent literal
                // (`x == !128 && y == 127` for a `u8` and an `i8` was skipped).
                let operand = match sgn {
                    Sign::Literal | Sign::NegLiteral => self.range_of(v),
                    // A nested complement's sign carries the envelope it inherited,
                    // but the operand term may *also* have recorded one of its own
                    // (a fold: `!(!1 - 200)` folds `!1` and `200`, and the fold term
                    // carries `200`). Both must survive, so they are unioned -- taking
                    // the inherited envelope alone dropped the fold's `200` and let the
                    // reader decide a contract rustc rejects.
                    Sign::Opaque(env) => Sign::union_env(env, self.range_of(v)),
                    _ => None,
                };
                let cv = smt::word(!val & mask, w);
                return Ok((cv, Sign::Opaque(operand)));
            }
            let w = smt::bits(v);
            let cv = smt::bxor(v, smt::all_ones(w));
            self.record_range_union(cv, v, v);
            return Ok((cv, sgn));
        }
        self.parse_atom()
    }

    fn parse_atom(&mut self) -> Result<(Var, Sign), SpecError> {
        let (v, s) = self.parse_primary()?;
        self.parse_wrapping_postfix(v, s)
    }

    /// A postfix `.wrapping_add(arg)` / `.wrapping_sub(arg)` / `.wrapping_mul(arg)`
    /// / `.wrapping_neg()` on a value -- the method-call spelling of the wrapping
    /// operators the contract language already models.
    ///
    /// The desugaring is exact, and that is the whole reason it can be read: `a + b`
    /// in a contract *is* a bit-vector add, which wraps at the operand width, so
    /// `a.wrapping_add(b)` and `a + b` denote the same term. The one deliberate
    /// difference is the constant-overflow refusal: `200 + 100` is refused because
    /// rustc rejects that constant expression, where `200u8.wrapping_add(100u8)` is
    /// a legal program whose value is `44`, so the sugar must *not* run the fold --
    /// the engine's own wrapping operator is the value Rust computes. The operands'
    /// literals are still range-checked against the type they meet (`x.wrapping_add(300)`
    /// is a rustc error for its `300`), which is what `align_widths` does.
    ///
    /// The receiver's type must be *fixed*. Rust refuses `1.wrapping_add(2)` with
    /// `E0689` (the receiver is an ambiguous `{integer}`), so a receiver that is
    /// only a bare literal is refused rather than silently given the scope's width.
    fn parse_wrapping_postfix(&mut self, v: Var, sgn: Sign) -> Result<(Var, Sign), SpecError> {
        let (mut v, mut sgn) = (v, sgn);
        loop {
            if !matches!(self.peek(), Some(Tok::Op(o)) if o == ".") {
                return Ok((v, sgn));
            }
            let Some(Tok::Ident(name)) = self.toks.get(self.pos + 1).cloned() else {
                return Ok((v, sgn));
            };
            let takes_arg = match name.as_str() {
                "wrapping_add" | "wrapping_sub" | "wrapping_mul" => true,
                "wrapping_neg" => false,
                // Any other method is left in place: the caller reports the
                // trailing token, exactly as before this sugar existed.
                _ => return Ok((v, sgn)),
            };
            if !sgn.fixes_type() {
                return Err(self.err(format!(
                    "`{name}` needs a receiver whose integer type is known; a bare literal is an \
                     ambiguous `{{integer}}` in Rust"
                )));
            }
            self.pos += 2;
            if !self.eat_op("(") {
                return Err(self.err(format!("`{name}` is a call: write `{name}(..)`")));
            }
            let (r, rs) = if takes_arg {
                self.parse_expr()?
            } else {
                (v, sgn)
            };
            if !self.eat_op(")") {
                return Err(self.err(format!("`{name}` is missing its closing `)`")));
            }
            let out = Sign::combine(sgn, rs);
            let (l, r) = self.align_widths(v, sgn, r, rs, out)?;
            v = match name.as_str() {
                "wrapping_add" => smt::add(l, r),
                "wrapping_sub" => smt::sub(l, r),
                "wrapping_mul" => smt::mul(l, r),
                // `wrapping_neg` is `0 - x` at the operand's width, and it is legal
                // for an *unsigned* receiver too -- `(1u8).wrapping_neg()` is `255`,
                // which the unary `-` (signed-only) deliberately refuses.
                _ => smt::sub(smt::word(0, smt::bits(l)), l),
            };
            self.record_fold_result(v, l, r, out);
            sgn = out;
        }
    }

    fn parse_primary(&mut self) -> Result<(Var, Sign), SpecError> {
        match self.peek().cloned() {
            Some(Tok::Num(n, suffix)) => {
                self.pos += 1;
                // A *suffixed* literal has a fixed Rust type: its width and sign
                // come from the suffix, not from the scope. Building it at the
                // scope's width instead lost the value's high bits -- `128i16`
                // became `0x80` in an 8-bit scope, which a later widening cast
                // sign-extended to `-128` and *verified* a false
                // `ensures: 128i16 as i32 == -128`. So it is built at its own
                // width, and the value is range-checked against the suffix.
                if let Some((w, signed)) = suffix {
                    // The engine's words are 1..=64 bits, and `smt::word` refuses a
                    // wider one by flagging the term ill-formed. A `u128`/`i128`
                    // suffix has to be refused *here*, before the range check: the
                    // check computes `1u128 << (w - 1)` and `1u128 << w`, and a
                    // shift of 128 panics in a debug build (it wraps to a wrong
                    // `max` in release). The reader cannot hold a 128-bit literal,
                    // so the contract is refused rather than decided -- the same
                    // answer `cast_chain` gives a cast to `u128`.
                    if w > 64 {
                        return Err(self.err(format!(
                            "a `{w}`-bit type suffix is wider than the engine's 64-bit words, so \
                             a literal of that type is not modelled"
                        )));
                    }
                    // A signed literal is allowed up to `2^(w-1)` because it may
                    // be negated: `-128i8` needs the literal `128i8` to exist
                    // first, and the negation is what makes the min magnitude
                    // legal. A positive use of that magnitude is a Rust error
                    // this check cannot see from here.
                    let max = if signed {
                        1u128 << (w - 1)
                    } else {
                        (1u128 << w) - 1
                    };
                    if u128::from(n) > max {
                        return Err(self.err(format!(
                            "literal `{n}` is out of range for its `{}` type suffix",
                            if signed { "i" } else { "u" }
                        )));
                    }
                    let sign = if signed { Sign::Signed } else { Sign::Unsigned };
                    let v = smt::word(n, w);
                    // Rust range-checks the *written magnitude* of a suffixed
                    // literal, not the two's-complement value it denotes: `128i8`
                    // alone is out of range, and only `-128i8` is legal, because the
                    // negation is what meets the type. Recording the signed value
                    // instead made the negation add `+128` to the envelope and refuse
                    // the valid `-128i8` (and, worse, made the positive `128i8` --
                    // which rustc rejects -- read as the in-range `-128`). Recording
                    // the magnitude, and marking the literal pristine so a direct `-`
                    // *replaces* it, keeps both right: `-128i8` reads, `128i8` is
                    // refused, and `-(-128i8)` (`128`, out of range) is refused too.
                    let mag = i128::from(n);
                    self.record_range(v, mag, mag);
                    self.bare_literals.insert(v.0 .0);
                    return Ok((v, sign));
                }
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
                // A bare literal inside a shift *amount* is floored at the
                // amount's inferred width (see `amount_floor`): 32 bits when
                // nothing in the amount fixes a type, or a typed operand's width
                // when one does. Outside an amount there is no floor.
                let w = scope.max(need).max(self.amount_floor).min(64);
                // A *bare* literal is untyped and non-negative: its value is
                // unambiguous, but its signedness is not yet known.
                let v = smt::word(n, w);
                self.record_const(v, false);
                self.bare_literals.insert(v.0 .0);
                Ok((v, Sign::Literal))
            }
            Some(Tok::Ident(name)) => {
                self.pos += 1;
                if name == "ret" || name == "result" {
                    let v = self.ret.ok_or_else(|| self.err(self.ret_absent))?;
                    return Ok((v, Sign::from_bool(self.ret_signed)));
                }
                if name == "true" || name == "false" {
                    // A boolean literal is a one-bit word, so a `bool`-returning
                    // function can write `ensures: ret == false`. It used to be
                    // an error here, which left such contracts unreadable; the
                    // width check then refuses a literal compared against a
                    // wider operand, which is the right refusal.
                    return Ok((smt::word(u64::from(name == "true"), 1), Sign::Literal));
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
                    // `Mode::Idle` — an enum variant named in a contract, which is
                    // a constant of the tag's width. Checked before `type_bound`
                    // because a variant name is not an integer bound, and the two
                    // spellings (`i8::MIN`, `Mode::Idle`) are distinguished by
                    // which table has the name.
                    let key = format!("{ty}::{a}");
                    if let Some((k, w)) = self.variant_consts.get(&key).copied() {
                        return Ok((self.unshared_const(k, w), Sign::Literal));
                    }
                    if self.enum_args.contains(&ty) {
                        return Err(self.err(format!(
                            "`{ty}` has no variant `{a}` (or its layout was not readable)"
                        )));
                    }
                    // A module-qualified `const` item: `requires: x <= low::K`. The
                    // dump prints both the definition and the use with the same
                    // path (`const low::K`), so the table is keyed by it and this is
                    // an exact lookup -- the same key the executor folds the body's
                    // `low::K` with. A module-nested item is resolved only when the
                    // contract spells the path, which is what keeps it from
                    // colliding with a top-level constant of the same last segment.
                    if let Some(c) = self.consts.get(&format!("{ty}::{a}")) {
                        let key = format!("{ty}::{a}");
                        let c = c.clone();
                        return self.const_item(&key, &c);
                    }
                    if let Some((k, w)) = type_bound(&ty, &a) {
                        // The bound is built at the width of the type it *names*,
                        // not at the widest name in scope. `i8::MIN` is the bit
                        // pattern `0x80`, which is exactly 8 bits; widening it to
                        // a 64-bit `128` and then narrowing it back would test
                        // `128 <= i8::MAX` and refuse the constant as out of range
                        // for a signed 8-bit operand -- a refusal of a bound that
                        // is by definition in range.
                        //
                        // It is built as a term *of its own* rather than the shared
                        // `word(k, w)`: `i8::MIN` and a bare or suffixed `128` are
                        // the same bit pattern and hash-cons to one term, so an
                        // out-of-range envelope recorded for the literal (`128i8`
                        // records `128`) was read back as the bound's and refused a
                        // valid `y == -128i8 && y == i8::MIN`. The bound's fit is
                        // known by construction, so it must not inherit a literal's
                        // envelope. See `unshared_const`.
                        return Ok((self.unshared_const(k, w), Sign::from_bool(ty.starts_with('i'))));
                    }
                    return Err(self.err(format!("unknown constant `{ty}::{a}`")));
                }
                // An argument wins over a constant of the same name, so a contract
                // that names an argument keeps resolving to it and the constant
                // table only ever adds names the reader would otherwise refuse.
                // Rust lets a parameter shadow a `const` of the same name, and
                // reading the constant there would bind the wrong value -- a false
                // proof, not a refusal.
                if let Some(v) = self.args.get(&name).copied() {
                    let s = self.is_signed_name(&name);
                    return Ok((v, Sign::from_bool(s)));
                }
                // A named `const` item: `requires: x <= LIMIT`, where the body
                // reads `_0 = const LIMIT`. Resolved from the program's own table,
                // the same one the executor folds the use site from, so the
                // contract and the body name one value and cannot disagree. Built
                // at the *item's* own width and sign -- the dump prints the body
                // const-evaluated and typed (`const 10_u8`) -- and as a term of its
                // own, so an envelope recorded for a literal of the same bit pattern
                // is not read back as this constant's.
                //
                // Checked *after* the associated-constant forms (`i8::MIN`), which
                // are recognized above: a name like `i8::MIN` is not in the table,
                // and a table entry is always a plain identifier.
                if let Some(c) = self.consts.get(&name) {
                    let c = c.clone();
                    return self.const_item(&name, &c);
                }
                Err(self.err(format!("unknown name `{name}` (not an argument)")))
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
            Some(Tok::BadNum) => {
                Err(self.err("a numeric literal that is not an exact integer (bad digit for its radix, or past u64)"))
            }
            Some(t) => Err(self.err(format!("unexpected token {t:?}"))),
            None => Err(self.err("unexpected end of contract")),
        }
    }

    /// Apply any `as <type>` casts that immediately follow an atom, returning the
    /// value and its signedness.
    ///
    /// The result of `x as T` has `T`'s width and `T`'s sign, and it *extends*
    /// rather than reinterprets: `-1i8 as i16` is `-1`, not `255`. A widening cast
    /// of a signed source sign-extends; an unsigned one zero-fills, which is
    /// `truncate`; a narrowing cast keeps the low bits, which `sign_extend` and
    /// `truncate` both do when the target is no wider.
    ///
    /// An unknown source sign is a refusal, not a guess, for the same reason the
    /// body refuses one: zero-filling a signed value would prove `-1i8 as i16 ==
    /// 255`, a reachable false proof, and sign-extending an unsigned one would
    /// turn `255u8 as u16` into `65535`. Guessing the sign is exactly the failure
    /// this crate exists to avoid.
    ///
    /// A cast *chain* (`x as u16 as u32`) applies left to right, and each step's
    /// source sign is the previous step's *target* sign -- which the cast just
    /// set, so it is always known. That is what makes the chain well-defined even
    /// when the first source's sign was not.
    fn cast_chain(&mut self, v: Var, sgn: Sign) -> Result<(Var, Sign), SpecError> {
        let (mut v, mut sgn) = (v, sgn);
        while matches!(self.peek(), Some(Tok::Ident(n)) if n == "as") {
            let Some(Tok::Ident(ty_name)) = self.toks.get(self.pos + 1).cloned() else {
                // `as` with no type after it is not a cast; leave it for the
                // caller to report as a trailing token rather than consuming it.
                break;
            };
            let ty = Ty::parse(&ty_name);
            let Some(w) = ty.width() else {
                break;
            };
            // The engine's words are 1..=64 bits, so a cast to `u128`/`i128` has
            // no width to truncate or extend to. Refusing it here is what stops
            // the cast from reaching `truncate`, whose width assertion would take
            // the whole run down with a panic instead of reporting this function
            // as undecided. A `break` would be wrong: it would leave `as` as a
            // trailing token and blame the syntax, when the cast is well-formed
            // Rust and it is the *engine* that cannot hold the result.
            if w > 64 {
                return Err(self.err(format!(
                    "`{ty_name}` is wider than the engine's 64-bit words, so a cast to it is not \
                     modelled"
                )));
            }
            self.pos += 2;
            // A *widening* cast of an untyped operand would have to guess whether
            // to sign-extend or zero-fill, and the two disagree (`!0 as i16` is
            // `-1` or `255`), so an opaque untyped operand is refused. A narrowing
            // cast keeps the low bits either way, so it is exact. A bare literal is
            // non-negative and zero-extends exactly.
            let src_signed = if sgn.ambiguous() {
                if w > smt::bits(v) {
                    return Err(self.err(
                        "a widening cast of a sign-ambiguous constant is not modelled: it would \
                         have to guess whether to sign-extend or zero-fill",
                    ));
                }
                false
            } else {
                sgn.eval()
            };
            v = if src_signed { smt::sign_extend(v, w) } else { smt::truncate(v, w) };
            sgn = Sign::from_bool(ty.is_signed());
        }
        Ok((v, sgn))
    }
}

/// The parsed head of a `struct` declaration.
///
/// Two shapes are recognised, and they are distinct because they carry their
/// fields differently. A *named-field* struct (`pub struct C { lo: u8 }`) may
/// close on its head line or need a cursor to collect the body; that is the
/// `closed_inline` flag, which keeps an open cursor from swallowing every
/// following line as a field and silently dropping the functions after it.
/// A *tuple* struct (`pub struct P(pub u8, pub u8);`) carries its fields in the
/// head itself, numbered by position, and needs no cursor.
///
/// A unit struct is neither: it has no fields to project, so returning `None`
/// leaves a contract naming `.0` as an "unknown name" refusal rather than
/// inventing a layout with no fields.
enum StructHead {
    Named { name: String, closed_inline: bool },
    Tuple { name: String, fields: Vec<(String, String)> },
}

fn struct_head(line: &str) -> Option<StructHead> {
    let t = line.trim_start_matches("pub(crate) ").trim_start_matches("pub ").trim();
    let rest = t.strip_prefix("struct ")?;
    let name = rest.split(|c: char| c == '{' || c == '(' || c == '<' || c.is_whitespace()).next()?;
    if name.is_empty() {
        return None;
    }
    // A tuple struct: the parenthesised list is the field list, and its
    // position in the list *is* the MIR field index, exactly as a named
    // struct's declaration order is. `pub u8` and a bare `u8` are the same
    // field, so the `pub` is stripped the way a named field's is.
    if let Some(open) = rest.find('(') {
        // The brace form wins if a `{` precedes the `(`: `struct S { f: fn(u8) }`
        // has a paren inside a field type, not a tuple body.
        let brace = rest.find('{');
        if brace.is_none() || open < brace.unwrap() {
            let close = rest[open + 1..].find(')')? + open + 1;
            let inner = &rest[open + 1..close];
            let fields = split_top_level(inner, ',')
                .into_iter()
                .enumerate()
                .filter_map(|(i, f)| {
                    let f = f.trim();
                    if f.is_empty() {
                        return None;
                    }
                    let f = f.trim_start_matches("pub(crate) ").trim_start_matches("pub ").trim();
                    // A tuple field cannot be empty and has no name of its own,
                    // so its name is its index. A field type with a trailing
                    // attribute is left as-is: `Ty::parse` reads the front of it,
                    // and an unreadable one widens to `Other`, which refuses a
                    // contract on it rather than fabricating a width.
                    Some((i.to_string(), f.to_string()))
                })
                .collect();
            return Some(StructHead::Tuple { name: name.to_string(), fields });
        }
    }
    // Only a brace body on this line is a named-field struct.
    let open = rest.find('{')?;
    // Closed on the head line iff a `}` follows the `{`.
    let closed_inline = rest[open + 1..].contains('}');
    Some(StructHead::Named { name: name.to_string(), closed_inline })
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
/// The parsed head of an `enum` declaration.
///
/// The three cases are distinct on purpose. A *one-line* body carries its
/// variants already; a *multi-line* body needs a cursor to collect them; and a
/// body whose explicit discriminant cannot be read is *refused* -- and, because
/// its closing brace has already been seen, that refusal must not be mistaken for
/// "a cursor is needed". Returning the multi-line case for a refused one-line body
/// would leave the cursor open past the brace and swallow every following line,
/// including contracts, so those functions would silently leave the check set.
enum EnumHead {
    /// A one-line body, fully parsed.
    Inline(Vec<(String, Vec<Ty>, u64)>),
    /// A multi-line body whose `{` opens the last thing on the line.
    MultiLine,
    /// A body this reader refuses (an unreadable discriminant). The layout is
    /// dropped, and the enum is *closed*: nothing after it belongs to it.
    Refused,
}

/// Pull the enum name out of a `pub enum Name {` head line.
///
/// Only a *braced* enum is recognised, and only when the body opens on the same
/// line. An enum whose variants are all written inline on the head line
/// (`pub enum E { A, B }`) is not read: the variants would have to be split out of
/// the head text, and getting that wrong would number the variants wrongly, which
/// is the one thing this layout must not do. A missing layout makes a contract
/// naming a variant a refusal, which is the safe direction.
fn enum_head(line: &str) -> Option<(String, EnumHead)> {
    let t = line.trim_start_matches("pub(crate) ").trim_start_matches("pub ").trim();
    let rest = t.strip_prefix("enum ")?;
    // A generic enum (`enum E<T>`) is read for its name, but a variant payload
    // naming `T` has no bit width and is skipped downstream.
    let name = rest.split(|c: char| c == '{' || c == '<' || c.is_whitespace()).next()?;
    if name.is_empty() {
        return None;
    }
    let open = rest.find('{')?;
    let after = &rest[open + 1..];
    // A one-line body (`pub enum E { A, B }`): the variants are split out of the
    // head text itself. Splitting on top-level commas is exactly what the
    // multi-line reader does per line, so the two agree on numbering by
    // construction.
    if let Some(close) = after.rfind('}') {
        let inner = &after[..close];
        let mut def = EnumDef::default();
        for v in split_top_level(inner, ',') {
            match enum_variant(&v) {
                VariantLine::Variant { name, payload, explicit } => {
                    push_variant(&mut def, name, payload, explicit);
                }
                VariantLine::NotAVariant => {}
                // An unreadable discriminant on a one-line body refuses the whole
                // enum, the same as the multi-line path. The body is already
                // closed, so this is a *refusal*, not an open cursor.
                VariantLine::UnreadableDiscriminant => {
                    return Some((name.to_string(), EnumHead::Refused))
                }
            }
        }
        return Some((name.to_string(), EnumHead::Inline(def.variants)));
    }
    // A multi-line body: the brace must end the line, so nothing but the brace
    // follows it.
    if !after.trim().is_empty() {
        return None;
    }
    Some((name.to_string(), EnumHead::MultiLine))
}

/// One line of an enum body, as far as the layout reader can tell.
enum VariantLine {
    /// A variant, with the explicit discriminant when the source wrote a literal
    /// one (`B = 3`).
    Variant {
        /// The variant's name.
        name: String,
        /// Its payload types; empty for a unit or struct variant.
        payload: Vec<Ty>,
        /// The explicit discriminant, when the source gave a literal one.
        explicit: Option<u64>,
    },
    /// A line that is not a variant (a comment, an attribute, a nested item).
    NotAVariant,
    /// A variant whose explicit discriminant is not a literal this reader can
    /// evaluate. The *whole* layout is refused: dropping the variant would shift
    /// every later discriminant, and guessing one would put a contract on the
    /// wrong tag. A refused layout makes a contract naming any of its variants a
    /// refusal, which is the safe direction.
    UnreadableDiscriminant,
}

/// Pull one variant out of a line of an enum body.
///
/// The line looks like `Off,`, `Idle,`, `Data(u8),`, `Pair { x: u8, y: u8 },` or
/// `B = 3,`. A unit variant and a tuple variant are both modelled; a *struct*
/// variant records no payload types, so a contract naming one of its fields is
/// refused rather than bound to a wrong index. A line that is not a variant (a
/// nested item, an attribute, a comment) is skipped, which loses a variant rather
/// than inventing one -- and a lost variant shifts every discriminant after it, so
/// the skip is restricted to lines that clearly are not variants.
fn enum_variant(line: &str) -> VariantLine {
    // A trailing line comment is not part of the variant. Stripping it *first*
    // matters because the comma that ends the variant sits before the comment:
    // `B = 3, // tag` would otherwise keep the comma (the line no longer ends in
    // one) and the discriminant reader would reject the whole line, dropping the
    // layout and skipping every contract that names one of its variants.
    let line = strip_line_comment(line);
    let t = line.trim().trim_end_matches(',').trim();
    if t.is_empty() || t.starts_with("//") || t.starts_with('#') || t.starts_with("}") {
        return VariantLine::NotAVariant;
    }
    let t = t.trim_start_matches("pub(crate) ").trim_start_matches("pub ").trim();
    // The variant name is the leading identifier.
    let name: String = t.chars().take_while(|c| c.is_alphanumeric() || *c == '_').collect();
    if name.is_empty() || !name.chars().next().map(|c| c.is_alphabetic() || c == '_').unwrap_or(false)
    {
        return VariantLine::NotAVariant;
    }
    let after = t[name.len()..].trim_start();
    let (payload, rest) = if after.is_empty() {
        // A unit variant: nothing follows the name.
        (Vec::new(), "")
    } else if let Some(inner_rest) = after.strip_prefix('(') {
        // A tuple variant: `Name(u8, u16)`. The payload types are what a `match`
        // arm's downcast reads, so they are recorded even though the tag does not
        // need them.
        let Some(close) = inner_rest.find(')') else { return VariantLine::NotAVariant };
        let inner = inner_rest[..close].trim();
        let tys = if inner.is_empty() {
            Vec::new()
        } else {
            split_top_level(inner, ',').iter().map(|t| Ty::parse(t.trim())).collect()
        };
        (tys, inner_rest[close + 1..].trim_start())
    } else if after.starts_with('{') {
        // A struct variant: the fields are not modelled, but the *variant* is, so
        // it still takes its discriminant.
        let Some(close) = after.rfind('}') else { return VariantLine::NotAVariant };
        (Vec::new(), after[close + 1..].trim_start())
    } else if after.starts_with('=') {
        (Vec::new(), after)
    } else {
        return VariantLine::NotAVariant;
    };
    // An explicit discriminant: `B = 3`. Only a literal is accepted; an
    // expression (`= 1 << 4`) would have to be evaluated, and evaluating it wrongly
    // is exactly the failure this reader exists to avoid, so the layout is refused
    // instead.
    if rest.is_empty() {
        return VariantLine::Variant { name, payload, explicit: None };
    }
    let Some(expr) = rest.strip_prefix('=') else { return VariantLine::NotAVariant };
    match parse_discriminant_literal(expr) {
        Some(d) => VariantLine::Variant { name, payload, explicit: Some(d) },
        None => VariantLine::UnreadableDiscriminant,
    }
}

/// A discriminant literal: decimal, `0x`/`0b`/`0o`, with an optional type suffix.
///
/// Only a literal is accepted. Anything else -- an expression, a `const` path, a
/// negative value under a signed `repr` -- returns `None`, and the caller refuses
/// the whole layout rather than guessing a number.
fn parse_discriminant_literal(s: &str) -> Option<u64> {
    let s = s.trim().trim_end_matches(';').trim();
    if s.is_empty() {
        return None;
    }
    // A negative literal (`= -1` under a signed `repr`) is refused: its value
    // depends on the tag's width, which the reader does not know here.
    if s.starts_with('-') {
        return None;
    }
    let body = strip_int_suffix(s);
    let (radix, digits) = if let Some(r) = body.strip_prefix("0x").or_else(|| body.strip_prefix("0X")) {
        (16u32, r)
    } else if let Some(r) = body.strip_prefix("0b").or_else(|| body.strip_prefix("0B")) {
        (2, r)
    } else if let Some(r) = body.strip_prefix("0o").or_else(|| body.strip_prefix("0O")) {
        (8, r)
    } else {
        (10, body)
    };
    // The whole remainder must be digits (underscores allowed), so `1 << 4` is
    // refused rather than silently read as `1`. A partial read is exactly the
    // kind of wrong number this reader exists to avoid.
    let mut seen = false;
    for c in digits.chars() {
        if c == '_' {
            continue;
        }
        if !c.is_digit(radix) {
            return None;
        }
        seen = true;
    }
    if !seen {
        return None;
    }
    let digits: String = digits.chars().filter(|c| *c != '_').collect();
    u64::from_str_radix(&digits, radix).ok()
}

/// Drop a trailing `// …` line comment, respecting string and char literals.
///
/// The enum reader is handed one trimmed source line at a time, and a comment on
/// that line is not part of the variant. A `//` inside a string or character
/// literal is not a comment, so the scan tracks those; a variant line has no such
/// literal in practice, but the scan keeps the rule true by construction rather
/// than by luck.
fn strip_line_comment(line: &str) -> &str {
    let bytes = line.as_bytes();
    let mut i = 0;
    let mut in_str = false;
    let mut in_char = false;
    while i < bytes.len() {
        let c = bytes[i];
        if in_str {
            if c == b'\\' {
                i += 2;
                continue;
            }
            if c == b'"' {
                in_str = false;
            }
        } else if in_char {
            if c == b'\\' {
                i += 2;
                continue;
            }
            if c == b'\'' {
                in_char = false;
            }
        } else if c == b'"' {
            in_str = true;
        } else if c == b'\'' {
            in_char = true;
        } else if c == b'/' && bytes.get(i + 1) == Some(&b'/') {
            return &line[..i];
        }
        i += 1;
    }
    line
}

/// Drop a trailing integer type suffix (`3u8`, `0x10_i32`) if one is present.
fn strip_int_suffix(s: &str) -> &str {
    for suf in [
        "i8", "i16", "i32", "i64", "i128", "isize", "u8", "u16", "u32", "u64", "u128", "usize",
    ] {
        if let Some(head) = s.strip_suffix(suf) {
            return head.trim_end_matches('_');
        }
    }
    s
}

/// Push a variant, computing its discriminant.
///
/// Without an explicit value the discriminant is the previous one plus one,
/// starting at zero -- rustc's rule. The explicit value is stored as written, so
/// a variant after it continues from *that* value and not from its position.
fn push_variant(def: &mut EnumDef, name: String, payload: Vec<Ty>, explicit: Option<u64>) {
    let d = match explicit {
        Some(d) => d,
        None => def.variants.last().map(|(_, _, d)| d + 1).unwrap_or(0),
    };
    def.variants.push((name, payload, d));
}

/// The layout of `Option<T>` or `Result<T, E>`, reconstructed from the type's
/// own generic arguments.
///
/// These are the two enums a real function reads without any source file
/// declaring them: `checked_add` returns `Option<u8>`, and `?` threads a
/// `Result`. `variant_index` already knows their fixed numbering
/// (`None`/`Ok` = 0, `Some`/`Err` = 1) for a *construction*; this gives an
/// *argument* of the same type a tag and payload seeds, so a `match` on it is
/// modelled instead of refused as an unmodelled switch discriminant.
///
/// `Option`'s payload type is the type argument (`Option<u8>` → `Some(u8)`);
/// `Result`'s is its two type arguments in order (`Result<T, E>` → `Ok(T)`,
/// `Err(E)`). The split is top-level, so a nested type (`Result<Option<u8>, u8>`)
/// stays one argument rather than being cut at its own comma.
///
/// A *declared* enum always wins — the caller consults `enums` first — so a user
/// `enum E { Some, None }` is not read as `Option`. An unrecognised spelling
/// yields `None`, which leaves the argument unbound and the function refused, the
/// conservative direction.
pub fn std_enum_def(name: &str) -> Option<EnumDef> {
    let name = name.trim();
    let inner = |head: &str| -> Option<String> {
        let rest = name.strip_prefix(head)?.trim_start();
        if !rest.starts_with('<') {
            return None;
        }
        // The opening `<` is still in `rest`, so the scan starts at depth 0 and
        // the matching `>` is the index where the depth returns to 0.
        let close = {
            let mut d = 0i32;
            let mut end = None;
            for (i, c) in rest.char_indices() {
                match c {
                    '<' => d += 1,
                    '>' => {
                        d -= 1;
                        if d == 0 {
                            end = Some(i);
                            break;
                        }
                    }
                    _ => {}
                }
            }
            end?
        };
        let args = &rest[1..close];
        // Reject anything after the closing `>` that is not whitespace, so a
        // spelling like `Option<u8>X` is not silently read as `Option<u8>`.
        if !rest[close + 1..].trim().is_empty() {
            return None;
        }
        Some(args.to_string())
    };
    let variant = |vname: &str, payload: Vec<Ty>, d: u64| (vname.to_string(), payload, d);
    if let Some(args) = inner("Option") {
        let t = Ty::parse(args.trim());
        return Some(EnumDef {
            variants: vec![variant("None", vec![], 0), variant("Some", vec![t], 1)],
        });
    }
    if let Some(args) = inner("Result") {
        let parts = split_top_level(&args, ',');
        if parts.len() != 2 {
            return None;
        }
        let ok = Ty::parse(parts[0].trim());
        let err = Ty::parse(parts[1].trim());
        return Some(EnumDef {
            variants: vec![variant("Ok", vec![ok], 0), variant("Err", vec![err], 1)],
        });
    }
    None
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
    enums: &BTreeMap<String, EnumDef>,
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
                env.bind_indexed_len(l, &arg, w, elem.is_signed());
            }
            continue;
        }
        // An array argument: `[u8; 4]`. Its length is the constant in its type,
        // so unlike a slice there is nothing for the caller to choose; the
        // elements are still distinct inputs per index.
        if let Ty::Array(elem, n) = base {
            if let Some(w) = elem.width() {
                env.bind_array_len(l, &arg, w, elem.is_signed(), *n);
            }
            continue;
        }
        let Ty::Other(name) = base else { continue };
        // An enum argument: its tag is a symbolic input with the enum's arity as
        // its domain, and each variant's payload is its own input. Checked before
        // the struct path because an enum name is an `Other` too, and binding it
        // as a struct with no fields would silently lose the tag.
        //
        // A *declared* layout always wins. `Option` and `Result` are the two the
        // reader knows without a declaration, because `checked_*` and the `?`
        // operator hand them to real functions and no source file declares them;
        // `std_enum_def` reconstructs their layout from the type's generic
        // arguments. `Shadow` is a declared `enum { Some, None }` and is not
        // `Option`, so it must reach `enums` first.
        if let Some(def) = enums.get(name) {
            env.bind_enum(l, &arg, name, def);
            continue;
        }
        if let Some(def) = std_enum_def(name) {
            env.bind_enum(l, &arg, name, &def);
            continue;
        }
        // Recorded whether or not a layout was found, so a contract naming a field
        // gets a message about the field even when the struct's definition was not
        // readable.
        env.declare_arg(&arg);
        let Some(def) = structs.get(name) else { continue };
        for (i, (fname, fty)) in def.fields.iter().enumerate() {
            env.bind(l, &arg, fname, i as u32, fty);
            // An array-typed field is subscriptable: `o.a[0]`. Recorded so a contract's
            // `o.a[0]` can bind an element variable of the right width, and the executor seeds
            // it under the same `(local, [i], index)` key the body's write lands on.
            if let Ty::Array(elem, n) = fty {
                if let Some(w) = elem.width() {
                    env.path_elem_types.insert(
                        format!("{arg}.{fname}"),
                        PathElem {
                            arg: arg.clone(),
                            local: l,
                            chain: vec![i as u32],
                            elem_w: w,
                            elem_signed: elem.is_signed(),
                            len: *n,
                        },
                    );
                }
            }
        }
        // Nested paths: `o.i.v` and, for a *named-field* struct, `o.i` too (its
        // field names are not numeric, so the single-field pass above skipped them).
        // A tuple struct's `.0` is already bound by `bind`, and `bind_nested` only
        // takes depth >= 2, so the two passes do not overlap.
        env.bind_nested_paths(l, &arg, base, structs);
    }
    env
}

/// The argument names whose declared type is signed, for comparison signedness.
///
/// Alias names are included for the same reason they are in [`arg_vars`]: `k` in
/// `let k = i;` stands for `i`, so a signed `i` makes `k` signed too. Omitting
/// them would make `k < 0` an unsigned comparison — the exact class of bug the
/// `Sign` type was introduced to prevent.
pub fn signed_args(f: &crate::mir::parse::MirFn) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    for &l in &f.arg_locals {
        if f.ty_of(l).map(|t| t.is_signed()).unwrap_or(false) {
            out.insert(f.name_of(l));
        }
    }
    for (name, local) in f.alias_locals() {
        if f.ty_of(local).map(|t| t.is_signed()).unwrap_or(false) {
            out.insert(name);
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
/// appear in the MIR dump, plus any source name that is a direct alias of an
/// argument.
///
/// The alias names are added here rather than only to the index binder because
/// they are ordinary contract names: `let k = i;` makes `k` usable wherever `i`
/// is, so a `requires: k < 4` has to resolve too. `MirFn::alias_locals` decides
/// which names qualify, and it only ever names an argument that the body never
/// writes, so every entry here stands for the very value the body uses.
pub fn arg_vars(f: &crate::mir::parse::MirFn) -> BTreeMap<String, Var> {
    let mut out = BTreeMap::new();
    for &l in &f.arg_locals {
        let ty = f.ty_of(l).cloned().unwrap_or(Ty::Other("?".into()));
        if let Some(w) = ty.width() {
            out.insert(f.name_of(l), smt::var_named(l, w));
        }
    }
    for (name, local) in f.alias_locals() {
        let ty = f.ty_of(local).cloned().unwrap_or(Ty::Other("?".into()));
        if let Some(w) = ty.width() {
            out.insert(name, smt::var_named(local, w));
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn def(src: &str) -> EnumDef {
        let specs = extract(src);
        specs.enums.get("E").cloned().unwrap_or_default()
    }

    /// The two standard enums a real function reads are reconstructed from the
    /// type's own generic arguments, with the payloads at their declared widths.
    #[test]
    fn a_standard_enum_argument_gets_a_layout() {
        let o = std_enum_def("Option<u8>").expect("Option<u8> has a layout");
        assert_eq!(o.index_of("None"), Some(0));
        assert_eq!(o.index_of("Some"), Some(1));
        assert_eq!(o.tag_width(), 1);
        assert_eq!(o.variants[1].1, vec![Ty::U8], "`Some` carries the type argument");

        let r = std_enum_def("Result<u8, u16>").expect("Result<u8, u16> has a layout");
        assert_eq!(r.index_of("Ok"), Some(0));
        assert_eq!(r.index_of("Err"), Some(1));
        assert_eq!(r.variants[0].1, vec![Ty::U8], "`Ok` carries the first argument");
        assert_eq!(r.variants[1].1, vec![Ty::U16], "`Err` carries the second");
    }

    /// The argument split is top-level, so a nested type stays one argument.
    #[test]
    fn a_nested_standard_enum_payload_is_one_type() {
        let r = std_enum_def("Result<Option<u8>, u8>").expect("nested Result has a layout");
        assert_eq!(r.variants[0].1, vec![Ty::Other("Option<u8>".into())]);
        assert_eq!(r.variants[1].1, vec![Ty::U8]);
    }

    /// A spelling that is not `Option`/`Result`, or is malformed, is refused
    /// rather than guessed -- an unrecognised type must leave the argument
    /// unbound so the function is refused, not modelled at the wrong width.
    #[test]
    fn a_non_standard_or_malformed_name_is_refused() {
        assert!(std_enum_def("Mode").is_none());
        assert!(std_enum_def("Option").is_none(), "no type argument is not Option<T>");
        assert!(std_enum_def("Option<u8>X").is_none(), "trailing text is not Option<u8>");
        assert!(std_enum_def("Result<u8>").is_none(), "Result needs two arguments");
    }

    /// A contract cast sets the target's width *and* sign, and a chain applies
    /// left to right. Pinned here, not only in the nightly-gated MIR tests, so
    /// the parse rule has a guard that runs without a toolchain.
    #[test]
    fn a_contract_cast_sets_the_target_width_and_sign() {
        let mut args = BTreeMap::new();
        args.insert("x".to_string(), smt::word(0, 8));
        let unsigned = BTreeSet::new();
        let signed: BTreeSet<String> = ["x".to_string()].into_iter().collect();

        // `x as u32` from an unsigned source: 32 bits, unsigned.
        let mut p = Parser::new("x as u32", &args, None, &unsigned, false);
        let (v, s) = p.parse_expr().expect("`x as u32` parses");
        assert_eq!(smt::bits(v), 32);
        assert!(!s.eval());

        // `x as i32` from a *signed* source: 32 bits, signed.
        let mut p = Parser::new("x as i32", &args, None, &signed, false);
        let (v, s) = p.parse_expr().expect("`x as i32` parses");
        assert_eq!(smt::bits(v), 32);
        assert!(s.eval());

        // A chain applies left to right: the last cast decides width and sign.
        let mut p = Parser::new("x as u16 as i32", &args, None, &unsigned, false);
        let (v, s) = p.parse_expr().expect("the chain parses");
        assert_eq!(smt::bits(v), 32);
        assert!(s.eval());
    }

    /// The operator precedence must match Rust's, because a contract is Rust
    /// syntax. The earlier reader put `|`/`^` with `+`/`-` and `&` with `*`, so
    /// `x & 1 + 1` was read as `(x & 1) + 1` where Rust means `x & (1 + 1)` -- a
    /// different *value*, not a different proof. The values below are evaluated
    /// on the engine, so a wrong tree shows up as a wrong number.
    #[test]
    fn a_contract_expression_uses_rust_precedence() {
        let mut args = BTreeMap::new();
        args.insert("x".to_string(), smt::word(1, 8));
        let unsigned = BTreeSet::new();
        let eval = |text: &str| {
            let mut p = Parser::new(text, &args, None, &unsigned, false);
            let (v, _) = p.parse_expr().expect("parses");
            p.expect_end().expect("no trailing tokens");
            smt::evaluate(v, |_| None).expect("a constant")
        };
        // `1 & (1 + 1)` is `1 & 2` is `0`; `(1 & 1) + 1` would be `2`.
        assert_eq!(eval("x & 1 + 1"), 0, "`&` must bind looser than `+`");
        // `(1 + 1) << 1` is `4`; `1 + (1 << 1)` would be `3`, so `+` binds
        // tighter than `<<`.
        assert_eq!(eval("x + 1 << 1"), 4, "`+` must bind tighter than `<<`");
        // `1 | 1 ^ 1` is `1 | (1 ^ 1)` is `1`; `(1 | 1) ^ 1` would be `0`.
        assert_eq!(eval("x | 1 ^ 1"), 1, "`^` must bind tighter than `|`");
        // `8 / 4 / 2` is left-associative: `(8 / 4) / 2` is `1`.
        assert_eq!(eval("8 / 4 / 2"), 1, "`/` is left-associative");
    }

    /// A negated literal is *signed*, and the flag has to say so or `%`, `/` and
    /// `>>` pick the unsigned engine and return a different number.
    ///
    /// This is the shape the precedence test cannot reach: signedness is read from
    /// the *names* in an expression, and `-7 % 3` has no name. The operand of the
    /// negation is the literal `7`, which is unsigned, so passing the operand's own
    /// flag through made the whole expression unsigned. Only `%`, `/` and `>>`
    /// consult the flag, so the mistake produced a *wrong value* rather than a
    /// refusal: `4294967289 % 3` is `0`, where Rust says `-1`. The flag is asserted
    /// directly here, because the values are what the corpus entries cover.
    #[test]
    fn a_negated_literal_is_signed() {
        // An 8-bit name in scope, so a bare literal is built 8 bits wide and the
        // value below is the readable `0xF9` rather than a 64-bit pattern.
        let mut args = BTreeMap::new();
        args.insert("x".to_string(), smt::word(1, 8));
        let unsigned = BTreeSet::new();
        let parse = |text: &str| {
            let mut p = Parser::new(text, &args, None, &unsigned, false);
            let (v, sgn) = p.parse_expr().expect("parses");
            p.expect_end().expect("no trailing tokens");
            (v, sgn)
        };
        // A negation is only defined on a signed type, so `-7` is signed even
        // though the `7` it negates is not.
        let (_, sgn) = parse("-7");
        assert!(sgn.eval(), "a negated literal is signed");
        let (_, sgn) = parse("-7 % 3");
        assert!(sgn.eval(), "a remainder of a negated literal is signed");
        // A bare literal stays unsigned, or `x % 3` for an unsigned `x` would
        // take the signed engine -- the mirror of the same mistake.
        let (_, sgn) = parse("7 % 3");
        assert!(!sgn.eval(), "a bare literal is unsigned");
        // The value is still a *value* negation: `-7` is the two's-complement
        // `7` subtracted from `0`, so it evaluates to `-1` at 8 bits.
        let (v, _) = parse("-7");
        assert_eq!(smt::evaluate(v, |_| None).expect("a constant"), 0xF9);
    }

    /// A bare literal widened to meet a *signed* operand zero-fills, not
    /// sign-extends.
    ///
    /// The fill is a property of the *constant's* own signedness, not the operand
    /// it meets. A bare literal is non-negative, so `(x as i16) == 255` for a `u8`
    /// `x` is true in Rust; filling from the operand's signed `i16` sign-extended
    /// the `255` to `65535` and *refuted* a postcondition Rust accepts — a false
    /// refutation, the mirror of a false proof. A signed constant keeps
    /// sign-extending, which the last assertion pins.
    #[test]
    fn a_literal_widened_to_a_signed_operand_zero_fills() {
        let mut args = BTreeMap::new();
        args.insert("x".to_string(), smt::var(8));
        let unsigned = BTreeSet::new();
        let eval_const = |text: &str| {
            let mut p = Parser::new(text, &args, None, &unsigned, false);
            let (v, _) = p.parse_expr().expect("parses");
            p.expect_end().expect("no trailing tokens");
            smt::evaluate(v, |_| None).expect("a constant")
        };
        // The comparison as a whole, so the widened literal is what is decided.
        let pred = |text: &str, x: u64| {
            let mut p = Parser::new(text, &args, None, &unsigned, false);
            let pr = p.parse_or().expect("parses as a predicate");
            p.expect_end().expect("no trailing tokens");
            smt::evaluate_pred(pr, |_| Some(x)).expect("decides")
        };
        // `(x as i16)` at `x == 255` is `255`, so the equality is *true*. Sign-
        // extending the literal to `65535` would make it false.
        assert!(pred("(x as i16) == 255", 255), "`255` widened to i16 is `255`");
        // The widened literal itself, at 32 bits, is still `255`.
        assert_eq!(eval_const("255 as i32"), 255, "a bare literal zero-fills");
        // A *signed* constant must still sign-extend: `-1 as i32` is all ones.
        assert_eq!(eval_const("-1 as i32"), u32::MAX as u64, "a signed constant sign-extends");
    }

    /// An *opaque* constant is refused where a widening would have to guess its
    /// value, and a *fold* is not, so the refusal is not over-broad.
    ///
    /// A complement's value is the complement of a literal at the *operand's*
    /// width, but the reader holds it at the *scope's* width. `!0` against a `u16`
    /// is `65535`; the reader held `255` and zero-extended it, and *verified*
    /// `ensures: (x as u16 + !0) == 255` -- a false proof. The signed case fails
    /// the same way when the literal's top bit is clear: `!128` against an `i16` is
    /// `-129`, but `0x7F` sign-extends to `127`, *verifying* `== 127`. Both are
    /// refused. A *fold* (`200 + 100`) is a value, not a bit pattern, and is emitted
    /// at full width so it *truncates* to the operand exactly -- it must still read.
    #[test]
    fn an_opaque_constant_widening_is_refused_but_a_fold_is_not() {
        let mut args = BTreeMap::new();
        args.insert("x".to_string(), smt::var(8));
        let unsigned = BTreeSet::new();
        let parses = |text: &str| {
            let mut p = Parser::new(text, &args, None, &unsigned, false);
            p.parse_or().is_ok()
        };
        // A widening that would have to guess a complement's operand-width value.
        assert!(!parses("(x as u16 + !0) == 255"), "`!0` against a `u16` is `65535`");
        assert!(!parses("(x as u16 + !0) == 65535"), "the reader cannot model it either way");
        assert!(!parses("(x as i16 + !128) == 127"), "`!128` against an `i16` is `-129`");
        // A fold is a value and still reads, even into a wider operand.
        assert!(parses("x as u16 <= 200 + 100"), "`300` is a value, not a bit pattern");
        assert!(parses("x <= 100 + 44"), "a fold that fits its operand still reads");
        // The complement at its *own* width is fine, and the literal zero-extends.
        assert!(parses("(x as i16) == 255"), "a bare literal zero-extends");
        // A *suffixed* literal keeps its own width, so the pair is not narrowed to
        // the literal's placeholder width. `128i16 as i32` is a 32-bit `128`, and
        // the bare `128` beside it must widen to meet it, not the other way round.
        assert!(parses("128i16 as i32 == 128"), "the bare literal widens to the cast width");
    }

    /// A *suffixed* literal is built at its own width, and a bare literal beside it
    /// takes that width rather than forcing the suffixed one down to the scope's.
    ///
    /// `128i16` is a sixteen-bit `128`; the reader sized it from the scope's names
    /// (eight bits here) instead, so `0x80` was read as `-128` and a widening cast
    /// sign-extended it -- *verifying* `ensures: 128i16 as i32 == -128`, which Rust
    /// calls false. The true `== 128` must read, which is what fails if the pair is
    /// narrowed to the literal's placeholder width.
    #[test]
    fn a_suffixed_literal_is_sized_from_its_suffix_not_the_scope() {
        let mut args = BTreeMap::new();
        args.insert("x".to_string(), smt::var(8));
        let unsigned = BTreeSet::new();
        let pred = |text: &str| {
            let mut p = Parser::new(text, &args, None, &unsigned, false);
            let pr = p.parse_or().expect("parses");
            p.expect_end().expect("no trailing tokens");
            smt::evaluate_pred(pr, |_| Some(0)).expect("decides")
        };
        assert!(pred("128i16 as i32 == 128"), "`128i16 as i32` is `128`");
        assert!(pred("128i16 == 128"), "the suffixed literal is its own value");
        // The false reading must not verify. It is refused rather than refuted --
        // the reader cannot model the untyped `-128` beside a 32-bit cast -- which
        // is the sound direction, so assert the *predicate* is not proved, not that
        // it parses.
        let mut p = Parser::new("128i16 as i32 == -128", &args, None, &unsigned, false);
        if let Ok(pr) = p.parse_or() {
            assert!(!smt::prove(pr).is_proved(), "`128i16 as i32` is `128`, never `-128`");
        }
    }

    /// A `u128`/`i128` suffix is *refused* before the range check, which would
    /// otherwise shift `1u128` by 128 and panic in a debug build.
    ///
    /// The suffix records the type's true width (128), so the range check's
    /// `1u128 << w` overflows; in release the shift wraps and hands a 128-bit
    /// value to `smt::word`, itself an assertion. Both literals here are small, so
    /// the refusal must come from the *type*, not the value.
    #[test]
    fn a_u128_suffix_is_refused_before_the_range_shift() {
        let mut args = BTreeMap::new();
        args.insert("x".to_string(), smt::var(8));
        let unsigned = BTreeSet::new();
        for text in ["0u128 == 0u128", "0i128 == 0i128", "1u128 == 1"] {
            let mut p = Parser::new(text, &args, None, &unsigned, false);
            let err = p.parse_or().expect_err("a 128-bit suffix must be refused");
            let msg = format!("{err}");
            assert!(msg.contains("128") && msg.contains("64-bit"), "`{text}`: got {msg}");
        }
        // A 64-bit suffix beside a 128-bit one is still fine on its own.
        let mut p = Parser::new("1u64 == 1", &args, None, &unsigned, false);
        assert!(p.parse_or().is_ok(), "a `u64` suffix is modelled");
    }

    /// A *typed* constant mask keeps its type, so a pairing of the other
    /// signedness is refused rather than decided -- in **both** directions.
    ///
    /// `-1i8 & 1` is an `i8` and `1u8 & 1` is a `u8`, even though both compute the
    /// small positive `1`: the mask takes the typed operand's type, and `==` never
    /// coerces, so `(...) == y` against a partner of the other signedness is
    /// `E0308`. Marking the constant result `Literal` hid the type and read the
    /// comparison as `1 == y`. The first fix excluded only a *signed* typed operand,
    /// which left the unsigned half open; both must be refused now, while the same
    /// mask against a partner of its *own* signedness still reads.
    #[test]
    fn a_typed_constant_mask_keeps_its_type() {
        let mut args = BTreeMap::new();
        args.insert("y".to_string(), smt::var(8));
        // `y` is unsigned: a signed typed mask cannot be compared with it.
        let unsigned = BTreeSet::new();
        for text in ["(-1i8 & 1) == y", "(1i8 & 1) == y", "(-1i8 & 1) < y"] {
            let mut p = Parser::new(text, &args, None, &unsigned, false);
            let err = p.parse_or().expect_err("a signed mask vs an unsigned name must be refused");
            let msg = format!("{err}");
            assert!(msg.contains("signed constant"), "`{text}`: got {msg}");
        }
        // `y` is signed: an unsigned typed mask cannot be compared with it either.
        let mut signed = BTreeSet::new();
        signed.insert("y".to_string());
        for text in ["(1u8 & 1) == y", "(1u8 & 1) < y"] {
            let mut p = Parser::new(text, &args, None, &signed, false);
            let err = p.parse_or().expect_err("an unsigned mask vs a signed name must be refused");
            let msg = format!("{err}");
            assert!(msg.contains("signed constant"), "`{text}`: got {msg}");
        }
        // A mask with no *typed* operand stays untyped and may widen.
        let mut p = Parser::new("(!0 & 1) == y", &args, None, &unsigned, false);
        assert!(p.parse_or().is_ok(), "an untyped constant mask still reads");
    }

    /// A constant whose *type is fixed* may not meet a partner of another width,
    /// while a bare literal (and a bare negation) infers its width and may.
    ///
    /// `1i8`, `i8::MIN` and a cast carry a width of their own, so a comparison with
    /// a differently-sized operand is `E0308` in Rust, and `refuse_mixed_signedness`
    /// does not catch it because both operands are signed. `align_widths` used to
    /// *resize* the constant instead, which erased the only evidence and let
    /// `-1i8 < (x as i16)` and `1i8 == 1i16` verify. A bare literal (and `-1`, a
    /// negation of one) has no width of its own -- Rust infers it -- so those must
    /// still align to the other operand.
    #[test]
    fn a_fixed_width_constant_may_not_meet_a_partner_of_another_width() {
        let mut args = BTreeMap::new();
        args.insert("x".to_string(), smt::var(8));
        let mut signed = BTreeSet::new();
        signed.insert("x".to_string());
        // A fixed-width constant (suffix or bound) against a name of another width
        // is refused, whatever the comparison.
        for text in [
            "(x as i16) == 1i8",
            "-1i8 < (x as i16)",
            "(x as i16) < i8::MIN",
            "1i8 == 1i16",
        ] {
            let mut p = Parser::new(text, &args, None, &signed, false);
            let err = p.parse_or().expect_err("a fixed-width mismatch must be refused");
            let msg = format!("{err}");
            assert!(msg.contains("different widths"), "`{text}`: got {msg}");
        }
        // A bare literal, and a bare negation, have no width of their own and take
        // the other operand's -- these are well-typed and must read. So does a
        // width-independent untyped constant (`!0 & 1`, which is `1` at any width).
        for text in ["(x as i16) == 1", "-1 < (x as i16)", "-1 < x", "(!0 & 1) == x"] {
            let mut p = Parser::new(text, &args, None, &signed, false);
            assert!(p.parse_or().is_ok(), "`{text}` infers its width and reads");
        }
    }

    /// An untyped fold whose exact result *overflows* the operand width is refused,
    /// while a fold that fits still reads.
    ///
    /// `!0 + 1` is `256` at the scope's width. Against an unsigned partner rustc
    /// rejects it (`!0` is `255`, so `255 + 1` overflows), but the reader carried
    /// the scope-width value and let a later resize truncate it, reading
    /// `(!0 + 1) < 1u8` as `0 < 1` -- a *verified* contract for a program rustc
    /// rejects. The fold's value depends on the width it is read at, so it is
    /// refused. `200 + 100` is `300` at any width holding it, so it is
    /// width-independent and still reads -- the control the refusal must not catch.
    #[test]
    fn an_untyped_fold_that_overflows_the_operand_width_is_refused() {
        let mut args = BTreeMap::new();
        args.insert("y".to_string(), smt::var(8));
        args.insert("a".to_string(), smt::var(16));
        let unsigned = BTreeSet::new();
        let mut signed = BTreeSet::new();
        signed.insert("y".to_string());
        for text in ["(!0 + 1) < 1u8", "(!0 + 2) == 1u8", "(!0 + 1) <= y"] {
            let mut p = Parser::new(text, &args, None, &signed, false);
            let err = p.parse_or().expect_err("an overflowing untyped fold must be refused");
            assert!(
                format!("{err}").contains("width-dependent"),
                "`{text}`: got {err}"
            );
        }
        // A fold that *fits* the partner's width is a value, not a width-dependent
        // bit pattern, and must still read.
        for text in ["(200 + 100) <= a", "(200 + 100) == 300"] {
            let mut p = Parser::new(text, &args, None, &unsigned, false);
            assert!(p.parse_or().is_ok(), "`{text}` fits and reads");
        }
    }

    /// The complement of an untyped literal is range-checked against the type it
    /// meets, not merely held at the scope's width.
    ///
    /// `!128` for an `i8` is a rustc `literal out of range for i8` error -- `128`
    /// does not fit a signed eight-bit type -- even though the *complement's*
    /// value `127` does. The reader built `!128` as the constant `127` and marked
    /// it `Opaque`, then let the resize truncate it with no check, so `y <= !128`
    /// read as `y <= 127` (`i8::MAX`) and *verified* for a program rustc rejects.
    /// The operand is now checked against the type the complement meets, so this
    /// is refused while `!127` (which does fit) still reads. A complement against
    /// a wide enough partner (`!128` for an `i16`) is untouched.
    #[test]
    fn the_complement_of_an_out_of_range_literal_is_refused() {
        let mut args = BTreeMap::new();
        args.insert("x".to_string(), smt::var(8));
        args.insert("y".to_string(), smt::var(8));
        args.insert("b".to_string(), smt::var(16));
        // The parser is told which names are *signed*; a name it does not know is
        // unsigned. So `x` is a `u8`, `y` an `i8`, `b` an `i16`.
        let mut signed = BTreeSet::new();
        signed.insert("y".to_string());
        signed.insert("b".to_string());
        // `128`, `255` and a nested complement's `128` do not fit an `i8`; rustc
        // rejects each, so the reader must refuse rather than decide.
        for text in ["y <= (!128)", "y <= (!255)", "y <= (!!128)", "y <= (!(64 + 64))"] {
            let mut p = Parser::new(text, &args, None, &signed, false);
            let err = p.parse_or().expect_err("an out-of-range complement must be refused");
            let msg = format!("{err}");
            // Either the complement's own operand check or the per-literal range
            // check may be the one that fires (the fold `64 + 64` is refused for
            // its own `128`); both are the refusal this test is about.
            assert!(
                msg.contains("complement") || msg.contains("does not fit"),
                "`{text}`: got {msg}"
            );
        }
        // A complement whose operand *fits* the type it meets still reads, so the
        // refusal is drawn at the range, not at `!`.
        for text in ["y <= (!127)", "x <= (!255)", "x <= (!0)", "b <= (!128)"] {
            let mut p = Parser::new(text, &args, None, &signed, false);
            let r = p.parse_or();
            assert!(
                r.is_ok(),
                "`{text}` fits the operand type and reads: {:?}",
                r.err().map(|e| format!("{e}"))
            );
        }
    }

    /// Every literal and every constant `+ - *` intermediate is range-checked
    /// against the type the expression meets, not only the fold's value.
    ///
    /// The reader folds a constant expression to a single value, and used to
    /// range-check only that value. So `2 & 128` for an `i8` -- a rustc `literal
    /// out of range` error, since the `128` does not fit -- was read as `0` and
    /// *decided*, and `128 - 63` -- also rejected for its `128`, although its value
    /// `65` fits -- likewise. The envelope of the literals underneath the fold is
    /// what closes this, so both are refused.
    #[test]
    fn a_literal_inside_a_constant_fold_is_range_checked_too() {
        let mut args = BTreeMap::new();
        args.insert("y".to_string(), smt::var(8));
        args.insert("x".to_string(), smt::var(8));
        args.insert("a".to_string(), smt::var(16));
        let mut signed = BTreeSet::new();
        signed.insert("y".to_string());
        // Each is a rustc `literal out of range` error for the type it meets, so
        // the reader refuses rather than decides on a program rustc rejects.
        for text in [
            "y == (200 & 200)",
            "y == (2 & 128)",
            "y == (100 + 100)",
            "y == ((100 + 100) & 0)",
            "y == (128 - 63)",
            "y == (200 | 0)",
            "y <= (2 & 128)",
        ] {
            let mut p = Parser::new(text, &args, None, &signed, false);
            let err = p.parse_or().expect_err("an out-of-range literal must be refused");
            assert!(
                format!("{err}").contains("does not fit"),
                "`{text}`: got {err}"
            );
        }
        // The same value is fine where the literal *does* fit: `200 & 200` is a
        // `u8` expression, and `-128` is the one bare literal a unary `-` may
        // rescue for an `i8` (the negated value is checked, not the magnitude).
        for text in ["x == (200 & 200)", "x == (255 & 255)", "y == -128", "y == (-128)"] {
            let mut p = Parser::new(text, &args, None, &signed, false);
            assert!(
                p.parse_or().is_ok(),
                "`{text}` fits the type it meets and reads"
            );
        }
        // A literal inside a fold is *not* rescued by a surrounding `-`:
        // `-(128 - 63)` is rejected for its inner `128`, unlike `-(128)`.
        for text in ["y == -(128 - 63)", "y == -(-128)"] {
            let mut p = Parser::new(text, &args, None, &signed, false);
            assert!(
                p.parse_or().is_err(),
                "`{text}` has an out-of-range literal and must be refused"
            );
        }
    }

    /// A constant fold that mixes an *untyped* complement with a plain operand is
    /// refused when its value depends on the signedness Rust infers for it.
    ///
    /// A complement has no signedness of its own -- it takes the one the type it
    /// meets gives it -- and the reader guesses it from the other operand. When no
    /// operand fixes a sign, the guess can disagree with the reading the fold
    /// finally gets, and the value, and whether it overflows at all, change with
    /// it. `!127 - 63` is `128 - 63 = 65` unsigned but `i8::MIN - 63`, a rustc
    /// overflow, signed: the reader decided `65` for a program rustc rejects.
    /// `!127 * 2` is the same shape, and `!100 * -0` is `E0277` for a `u16` (the
    /// negation is legal only at a signed type). Each is refused.
    #[test]
    fn a_sign_ambiguous_untyped_fold_is_refused() {
        // The scope holds only eight-bit names, so a complement is held at eight
        // bits too and the fold `!127 - 63` is the signed-overflow shape.
        let mut args = BTreeMap::new();
        args.insert("x".to_string(), smt::var(8));
        args.insert("y".to_string(), smt::var(8));
        let mut signed = BTreeSet::new();
        signed.insert("y".to_string());
        for text in ["y == ((!127) - 63)", "x == ((!127) - 63)"] {
            let mut p = Parser::new(text, &args, None, &signed, false);
            let err = p.parse_or().expect_err("a sign-ambiguous fold must be refused");
            assert!(
                format!("{err}").contains("sign-ambiguous"),
                "`{text}`: got {err}"
            );
        }
        // At eight bits the two readings of `(!0) - 1` (`254` unsigned, `-2` signed)
        // both fit, so it is *not* ambiguous and still reads against a `u8`.
        {
            let text = "x == ((!0) - 1)";
            let mut p = Parser::new(text, &args, None, &signed, false);
            let r = p.parse_or();
            assert!(
                r.is_ok(),
                "`{text}` agrees under both readings and reads: {:?}",
                r.err().map(|e| format!("{e}"))
            );
        }
        // A negated bare literal beside an untyped complement is `E0277` when the
        // fold meets an unsigned type, so it is refused. The scope has a sixteen-bit
        // name to give the fold that width.
        let mut args = BTreeMap::new();
        args.insert("a".to_string(), smt::var(16));
        let unsigned = BTreeSet::new();
        let mut p = Parser::new("a == ((!100) * (-0))", &args, None, &unsigned, false);
        let err = p.parse_or().expect_err("a negated literal beside a complement is refused");
        assert!(
            format!("{err}").contains("sign-ambiguous"),
            "`a == ((!100) * (-0))`: got {err}"
        );
        // The controls at sixteen bits: the same fold where neither reading
        // overflows still reads.
        for text in ["a == ((!127) - 63)", "a == ((!0) * 0)"] {
            let mut p = Parser::new(text, &args, None, &unsigned, false);
            let r = p.parse_or();
            assert!(
                r.is_ok(),
                "`{text}` agrees under both readings and reads: {:?}",
                r.err().map(|e| format!("{e}"))
            );
        }
    }

    /// The written magnitude of a suffixed literal is what Rust range-checks, not
    /// the two's-complement value it denotes.
    ///
    /// `128i8` alone is a `literal out of range for i8` error, and only `-128i8`
    /// is legal, because the negation is what meets the type. Recording the signed
    /// value (`-128`) made the negation add `+128` to the envelope and refuse the
    /// valid `-128i8`; it also made the positive `128i8`, which rustc rejects, read
    /// as the in-range `-128`. Both are pinned here, with the same shape at sixteen
    /// bits.
    #[test]
    fn a_suffixed_minimum_literal_is_checked_as_written() {
        let mut args = BTreeMap::new();
        args.insert("y".to_string(), smt::var(8));
        let mut signed = BTreeSet::new();
        signed.insert("y".to_string());
        // `-128i8` is legal (`i8::MIN`) and must read.
        for text in ["y == -128i8", "y == -(128i8)", "y == i8::MIN"] {
            let mut p = Parser::new(text, &args, None, &signed, false);
            let r = p.parse_or();
            assert!(r.is_ok(), "`{text}` is legal and must read: {:?}", r.err().map(|e| format!("{e}")));
        }
        // A positive use of the magnitude, and a double negation, are errors.
        for text in ["y == 128i8", "y == -(-128i8)"] {
            let mut p = Parser::new(text, &args, None, &signed, false);
            let err = p.parse_or().expect_err("an out-of-range magnitude is refused");
            let msg = format!("{err}");
            assert!(
                msg.contains("does not fit") || msg.contains("out of range"),
                "`{text}`: got {msg}"
            );
        }
        // The same at sixteen bits, where the minimum is `-32768i16`.
        let mut args = BTreeMap::new();
        args.insert("b".to_string(), smt::var(16));
        let mut signed = BTreeSet::new();
        signed.insert("b".to_string());
        for text in ["b == -32768i16", "b == -(32768i16)", "b == i16::MIN"] {
            let mut p = Parser::new(text, &args, None, &signed, false);
            let r = p.parse_or();
            assert!(r.is_ok(), "`{text}` is legal and must read: {:?}", r.err().map(|e| format!("{e}")));
        }
        let mut p = Parser::new("b == 32768i16", &args, None, &signed, false);
        assert!(p.parse_or().is_err(), "`32768i16` alone is out of range for an `i16`");
    }

    /// A complement's operand literals are range-checked where the complement is
    /// read, but they must not leak onto an unrelated literal that shares the
    /// complement's *value* term.
    ///
    /// At eight bits `!128` is the constant `127`, so it is hash-consed with a
    /// separately written bare `127`. Recording the operand's envelope (`128`) in
    /// the global term-keyed map attached it to that innocent `127`, and
    /// `x == !128 && y == 127` for a `u8` and an `i8` -- both valid Rust -- was
    /// skipped. The envelope now travels in the `Opaque` payload, so the bare
    /// literal is untouched while `!128` against an `i8` is still refused.
    #[test]
    fn a_complement_operand_does_not_pollute_a_bare_literal() {
        let mut args = BTreeMap::new();
        args.insert("x".to_string(), smt::var(8));
        args.insert("y".to_string(), smt::var(8));
        let mut signed = BTreeSet::new();
        signed.insert("y".to_string());
        // Both conjuncts are valid Rust; the reader must read the whole contract.
        for text in [
            "x == !128 && y == 127",
            "y == 127 && x == !128",
            "x == !0 && y == 127",
        ] {
            let mut p = Parser::new(text, &args, None, &signed, false);
            let r = p.parse_or();
            assert!(r.is_ok(), "`{text}` is valid Rust and must read: {:?}", r.err().map(|e| format!("{e}")));
        }
        // The complement against an `i8` is still a `literal out of range` error.
        for text in ["y == !128", "y <= (!128)"] {
            let mut p = Parser::new(text, &args, None, &signed, false);
            let err = p.parse_or().expect_err("`!128` for an `i8` is out of range");
            let msg = format!("{err}");
            assert!(
                msg.contains("complement") || msg.contains("does not fit"),
                "`{text}`: got {msg}"
            );
        }
        // The refusal survives a unary `-` around the complement: the envelope must
        // travel through the negation, which is a *value* and cannot carry it in the
        // sign. `-!128` for an `i8` is a rustc error for the same operand `128`.
        let mut p = Parser::new("y <= (-(!128))", &args, None, &signed, false);
        let err = p.parse_or().expect_err("`-!128` for an `i8` is out of range");
        let msg = format!("{err}");
        assert!(
            msg.contains("complement") || msg.contains("does not fit"),
            "`y <= (-(!128))`: got {msg}"
        );
    }

    /// A nested complement whose operand is a *fold* keeps every literal underneath
    /// it, and a named bound does not inherit a literal's envelope.
    ///
    /// Two follow-ups to the envelope work. First, `!(!1 - 200)` for an `i8` is a
    /// rustc error for the `200`: the inner complement `!1` carries `(1, 1)` in its
    /// sign and the fold `!1 - 200` records `200` on its own term, so the outer
    /// complement must *union* the two -- taking the inherited envelope alone
    /// dropped the `200` and the reader decided a contract rustc rejects. Second,
    /// `i8::MIN` and a bare or suffixed `128` are the same eight-bit constant and
    /// hash-cons to one term, so a term-keyed envelope recorded for the literal
    /// (`128i8` records the out-of-range `128`) was read back as the *bound's* and
    /// skipped a valid `y == -128i8 && y == i8::MIN`; the bound is now its own term.
    #[test]
    fn a_nested_complement_keeps_the_fold_and_a_bound_keeps_its_own_fit() {
        let mut args = BTreeMap::new();
        args.insert("x".to_string(), smt::var(8));
        args.insert("y".to_string(), smt::var(8));
        let mut signed = BTreeSet::new();
        signed.insert("y".to_string());
        // The fold's `200` survives the outer complement, so the shape is refused
        // (the exact wording varies: an out-of-range complement operand, or an
        // unsigned fold that underflows -- both are rustc rejections).
        for text in ["y == !(!1 - 200)", "y == !(200 - !1)", "y == !(128 - 63)"] {
            let mut p = Parser::new(text, &args, None, &signed, false);
            assert!(
                p.parse_or().is_err(),
                "`{text}` is a rustc range error and must be refused"
            );
        }
        // The named bound is valid in either conjunct order, and beside a bare
        // `128` on an unsigned name it does not inherit the literal's envelope.
        for text in [
            "y == -128i8 && y == i8::MIN",
            "y == i8::MIN && y == -128i8",
            "x == 128 && y == i8::MIN",
            "y == i8::MIN && x == 128",
            "y == i8::MIN && y == 127",
        ] {
            let mut p = Parser::new(text, &args, None, &signed, false);
            let r = p.parse_or();
            assert!(r.is_ok(), "`{text}` is valid Rust and must read: {:?}", r.err().map(|e| format!("{e}")));
        }
    }

    /// A shift of an *untyped* constant is refused when it is only valid at the
    /// scope's width, not at every width the result could be read at.
    ///
    /// `255 >> 8` looks fine at the scope's width (32, from the `u32` name in
    /// scope), but the operand has no type of its own: Rust infers its width from
    /// where the shift is read, and against a `u8` partner `255` is a `u8` and a
    /// shift by its own width is a compile error. The reader verified
    /// `255 >> 8 <= x` for a `u8` `x` on a program rustc rejects. `(255 >> 1) >= y`
    /// for an `i8` `y` failed the same way, with `255` a rustc `literal out of
    /// range`. The amount must be below the *narrowest* width, and a literal
    /// operand must fit an 8-bit signed value, or the shift is refused. A shift of
    /// a *typed* name (`x >> 1`) is unaffected: its width is known.
    #[test]
    fn a_shift_of_an_untyped_constant_is_refused_when_it_needs_a_wider_operand() {
        let mut args = BTreeMap::new();
        args.insert("x".to_string(), smt::var(8));
        args.insert("y".to_string(), smt::var(8));
        args.insert("a".to_string(), smt::var(16));
        args.insert("c".to_string(), smt::var(32));
        let mut unsigned = BTreeSet::new();
        unsigned.insert("x".to_string());
        unsigned.insert("a".to_string());
        unsigned.insert("c".to_string());
        let mut signed = BTreeSet::new();
        signed.insert("y".to_string());
        // The scope's width is 32, so the amount passes the old scope-width check
        // and the operand passes the old (absent) range check; both are refused.
        for text in ["(255 >> 8) <= x", "(255 >> 16) <= a", "(!0 << 8) <= x",
                     "(1 >> 16) <= a", "(255 >> 1) >= y"] {
            let mut p = Parser::new(text, &args, None, &signed, false);
            assert!(
                p.parse_or().is_err(),
                "`{text}` is only valid at the scope's width and must be refused"
            );
        }
        // A shift of a *typed* name has a known width and still reads; so does a
        // constant shift whose amount is below the narrowest width and whose
        // operand fits an 8-bit signed value (`1 << 4` is `16` at any width).
        for text in ["(x >> 1) == 0", "(a << 2) <= a", "(1 << 4) <= x", "(1 >> 1) <= x",
                     "(2 << 2) <= a"] {
            let mut p = Parser::new(text, &args, None, &signed, false);
            assert!(p.parse_or().is_ok(), "`{text}` has a known width and reads");
        }
    }

    /// A shift *amount* is a value of its own type, so its bare literals are
    /// evaluated at Rust's `i32` (32 bits), not at the shifted operand's width.
    ///
    /// `x >> (2 << 7)` for a `u8` `x` is a rustc error: the amount `2 << 7` is an
    /// `i32` and is `256`, and a shift by 256 overflows. Sizing the amount's
    /// literals to the eight-bit scope instead made `2 << 7` wrap to `0`, so the
    /// shift read as `x >> 0` and the reader *decided* `x >> (2 << 7) == 0` --
    /// false at `x == 0` -- on a program rustc rejects. The floor makes the fold
    /// agree with rustc, so the wrapped amount never appears and the shift is
    /// refused for the amount it really is.
    #[test]
    fn a_shift_amount_is_evaluated_at_its_own_width_not_the_operands() {
        let mut args = BTreeMap::new();
        args.insert("x".to_string(), smt::var(8));
        let mut unsigned = BTreeSet::new();
        unsigned.insert("x".to_string());
        // Each amount is `256` (or wraps through one) at `i32`; every one is a
        // rustc overflow and must be refused rather than folded to a small count.
        for text in ["x >> (2 << 7) == 0", "x >> (2 << 6) == 0"] {
            let mut p = Parser::new(text, &args, None, &unsigned, false);
            assert!(
                p.parse_or().is_err(),
                "`{text}` overflows at the amount's own `i32` width and must be refused"
            );
        }
        // Amounts that fit `i32` and are below the operand width still read.
        for text in ["(x >> (1 + 1)) == 0", "(x >> (2 * 2)) == 0", "(x >> (8 - 1)) == 0",
                     "(x >> 7) == 0"] {
            let mut p = Parser::new(text, &args, None, &unsigned, false);
            assert!(p.parse_or().is_ok(), "`{text}` has an in-range amount and reads");
        }
    }

    /// A typed operand *inside* the amount fixes the amount's type, so the
    /// amount's bare literals must be built at that width, not at a blind `i32`.
    ///
    /// `x >> (1u8 + (2 << 7))` for a `u8` `x` is valid Rust: the suffixed `1u8`
    /// makes the amount a `u8`, so `2 << 7` is `0u8` and the amount is `1u8`. The
    /// earlier reader floored the amount's literals at a flat 32 bits, built
    /// `2 << 7` as `256`, and *refused* the shift -- a false refusal on a program
    /// rustc accepts. The floor now comes from the amount's own inferred width.
    ///
    /// The negative cases pin the other direction, because the fix must not accept
    /// a program rustc rejects: an amount with *no* typed operand is still `i32`
    /// (`2 << 7` is `256`, an overflow), a nested shift's amount suffix does not fix
    /// the outer amount's type (`2 << 7u8` is still the `i32` `256`), a typed
    /// operand outside the amount cannot narrow it (`x >> 300`), and two typed
    /// operands of different widths are a type error.
    #[test]
    fn a_typed_amount_operand_fixes_the_amounts_width() {
        let mut args = BTreeMap::new();
        args.insert("x".to_string(), smt::var(8));
        let mut unsigned = BTreeSet::new();
        unsigned.insert("x".to_string());

        let mut p = Parser::new("(x >> (1u8 + (2 << 7))) == 0", &args, None, &unsigned, false);
        let pred = p.parse_or().expect("`x >> (1u8 + (2 << 7))` is valid Rust and must read");
        assert!(smt::evaluate_pred(pred, |_| Some(0)).unwrap(), "0 >> 1 == 0");
        assert!(!smt::evaluate_pred(pred, |_| Some(2)).unwrap(), "2 >> 1 == 1 != 0");

        for text in [
            // No typed operand: the amount is `i32` `2 << 7` = `256`, an overflow.
            "x >> (2 << 7) == 0",
            // `1u16 + (2 << 7)` is `257` at `u16`, an overflow.
            "x >> (1u16 + (2 << 7)) == 0",
            // `1 + (2 << 7)` is `257` at `i32`, an overflow.
            "x >> (1 + (2 << 7)) == 0",
            // The `u8` suffix is in the *nested* shift's amount, so the outer amount
            // stays the `i32` `2 << 7u8` = `256`, an overflow.
            "x >> (2 << 7u8) == 0",
            // A typed operand outside the amount cannot narrow it: `300` stays `300`.
            "(x >> 300) == 2u8",
            "(x >> 300) == 2",
            // Two typed operands of different widths are a type error.
            "(x >> (1u8 + 1u16)) == 0",
            "(x >> (1u8 + 1i8)) == 0",
            // A cast fixes the amount's type and overrides what it casts:
            // `(1u8) as u16 + (2 << 7)` is `1u16 + 128u16` = `257u16`, an overflow.
            "x >> ((1u8) as u16 + (2 << 7)) == 0",
            "x >> (1u8 as u16 + (2 << 7)) == 0",
            // The width-dependent untyped folds were already refused and must stay so.
            "(!0 + 1) < 1u8",
            "(!0 + 2) == 1u8",
        ] {
            let mut p = Parser::new(text, &args, None, &unsigned, false);
            assert!(p.parse_or().is_err(), "`{text}` is a rustc error and must be refused");
        }
    }

    /// The provisional unsigned value of a fold that touched a complement must not
    /// be range-checked as if it were a written literal.
    ///
    /// `y == !(!1 + 1)` for an `i8` `y` is valid Rust: `!1 + 1` is `-1` at `i8`, and
    /// `!(-1)` is `0`, so the contract is `y == 0`. The reader evaluates the fold
    /// unsigned (`255`) because its type is not known until it meets the `i8`, and
    /// range-checking that *guess* refused the contract though no `255` is written.
    /// An `Opaque` fold now records only its operands' envelopes, so the guess is
    /// not checked -- while a genuine literal under the fold still is.
    #[test]
    fn an_opaque_folds_provisional_value_is_not_range_checked() {
        let mut args = BTreeMap::new();
        args.insert("y".to_string(), smt::var(8));
        let mut signed = BTreeSet::new();
        signed.insert("y".to_string());

        let mut p = Parser::new("y == !(!1 + 1)", &args, None, &signed, true);
        let pred = p.parse_or().expect("`y == !(!1 + 1)` is valid Rust and must read");
        assert!(smt::evaluate_pred(pred, |_| Some(0)).unwrap(), "y == 0 reads true at 0");
        assert!(!smt::evaluate_pred(pred, |_| Some(1)).unwrap(), "y == 0 reads false at 1");

        // A literal *under* the fold is still range-checked against the type the
        // complement meets: `!128` is an `i8` range error even though `!128` is
        // `127`, so `y == !128` must be refused.
        let mut p = Parser::new("y == !128", &args, None, &signed, true);
        assert!(p.parse_or().is_err(), "`!128` meets an `i8` and must be refused");
    }

    /// A deeply nested amount must not exhaust the stack, because the parser
    /// recurses once per level and calls `smt::evaluate` (via `const_value`) at
    /// every level.
    ///
    /// `evaluate` owns a 12 KiB [`EvalMemo`] as a stack local. When the optimiser
    /// inlined it into the recursive parser, every level cost 12 KiB of stack and a
    /// two-level amount already aborted on the 2 MiB a test thread gets. The fix is
    /// `#[inline(never)]` on `evaluate`; this test is the gate on it, because it runs
    /// on the *default* stack and reverting the attribute re-inflates the frames.
    ///
    /// The nesting is far deeper than the corpus needs (40 levels against the
    /// corpus's 2), so the test fails on a regression by a wide margin rather than
    /// by a hair -- a frame that is merely large should be caught here, not at the
    /// exact depth some other test happens to use. The amounts stay small enough to
    /// fit the operand so the *only* thing under test is the stack cost.
    #[test]
    fn a_deeply_nested_amount_does_not_exhaust_the_stack() {
        let mut args = BTreeMap::new();
        // A 64-bit operand, so the nested amount (which sums to 40) is below the
        // operand width and the *only* thing the test exercises is the stack cost.
        args.insert("x".to_string(), smt::var(64));
        let mut unsigned = BTreeSet::new();
        unsigned.insert("x".to_string());
        // `(1 + (1 + (1 + ... )))`, 40 deep, as a shift amount.
        let mut amount = String::from("1");
        for _ in 0..40 {
            amount = format!("(1 + {amount})");
        }
        let text = format!("(x >> {amount}) == 0");
        let mut p = Parser::new(&text, &args, None, &unsigned, false);
        assert!(
            p.parse_or().is_ok(),
            "a 40-level nested amount fits the operand and must read without exhausting the stack"
        );
    }

    /// Negating a signed constant at its own type is checked against the *value*,
    /// not the written magnitude, so `-(i8::MIN)` and `-(3 << 7)` are refused.
    ///
    /// `i8::MIN` is the bit pattern `128` and the value `-128`. The reader's
    /// magnitude check reads the bit pattern, which is the same `128` that the
    /// legal literal `128i8` has, so it passed and the negation was recorded as
    /// the in-range `-128` -- and the reader *decided* `y == -(i8::MIN)` on a
    /// program rustc rejects with `attempt to negate i8::MIN, which would
    /// overflow`. `3 << 7` at eight bits wraps to the same bit pattern, so
    /// `-(3 << 7)` was decided too. Only a pristine literal is exempt, because
    /// there the negation is what makes the magnitude legal (`-128i8` reads).
    #[test]
    fn negating_a_signed_constant_is_checked_as_its_value() {
        let mut args = BTreeMap::new();
        args.insert("y".to_string(), smt::var(8));
        let mut signed = BTreeSet::new();
        signed.insert("y".to_string());
        for text in [
            "y == -(i8::MIN)",
            "y == -(3 << 7)",
            "y == -(1 << 7)",
            "y <= (-(i8::MIN))",
            "y == -(-128i8)",
        ] {
            let mut p = Parser::new(text, &args, None, &signed, false);
            assert!(
                p.parse_or().is_err(),
                "`{text}` negates a constant out of range at its own type and must be refused"
            );
        }
        // A pristine literal, the bound's maximum, and a plain negation read.
        for text in ["y == -128i8", "y == -(128i8)", "y == i8::MIN", "y == -(i8::MAX)",
                     "y == -(127)"] {
            let mut p = Parser::new(text, &args, None, &signed, false);
            let r = p.parse_or();
            assert!(r.is_ok(), "`{text}` is legal and must read: {:?}", r.err().map(|e| format!("{e}")));
        }
    }

    /// A typed constant mask against a partner of its *own* signedness reads.
    #[test]

    fn a_typed_constant_mask_with_a_same_signedness_partner_reads() {
        let mut args = BTreeMap::new();
        args.insert("y".to_string(), smt::var(8));
        let mut signed = BTreeSet::new();
        signed.insert("y".to_string());
        let mut p = Parser::new("(-1i8 & 1) == y", &args, None, &signed, false);
        let pr = p.parse_or().expect("a signed mask vs a signed name reads");
        p.expect_end().expect("no trailing tokens");
        // `-1i8 & 1` is `1`, so the predicate holds only at `y == 1`.
        assert!(smt::evaluate_pred(pr, |_| Some(1)).expect("decides"), "`1 == 1`");
        assert!(!smt::evaluate_pred(pr, |_| Some(0)).expect("decides"), "`1 == 0` is false");
        // The unsigned direction reads against an unsigned name.
        let unsigned = BTreeSet::new();
        let mut p = Parser::new("(1u8 & 1) == y", &args, None, &unsigned, false);
        let pr = p.parse_or().expect("an unsigned mask vs an unsigned name reads");
        p.expect_end().expect("no trailing tokens");
        assert!(smt::evaluate_pred(pr, |_| Some(1)).expect("decides"), "`1 == 1`");
        assert!(!smt::evaluate_pred(pr, |_| Some(0)).expect("decides"), "`1 == 0` is false");
    }

    /// Unary `-` binds *tighter* than `as`, so `-x as u8` is `(-x) as u8` and its
    /// type is `u8` — unsigned — not the signed `-(x as u8)`.
    ///
    /// The values agree (negation and truncation commute), so the flag is what
    /// separates the readings, and the flag is what the operators and comparisons
    /// read. Getting it backwards made `-x as u8 > 127` unsatisfiable — an `i8` is
    /// never `> 127` — which reported a verifiable function as *vacuous*. Rust
    /// rejects `-x as u8` for an unsigned `x` with "cannot apply unary operator
    /// `-`", which is the language telling you the negation happens on `x` before
    /// the cast, not on the cast's result. So the operand here is a *signed* `x`
    /// (the only spelling rustc accepts for a negation), and the unsigned `x` case
    /// is asserted as a refusal below.
    #[test]
    fn a_negation_binds_tighter_than_a_cast() {
        let mut args = BTreeMap::new();
        args.insert("x".to_string(), smt::word(0, 8));
        let mut signed = BTreeSet::new();
        signed.insert("x".to_string());
        let parse = |text: &str| {
            let mut p = Parser::new(text, &args, None, &signed, false);
            let (v, sgn) = p.parse_expr().expect("parses");
            p.expect_end().expect("no trailing tokens");
            (v, sgn)
        };
        // `(-x) as u8` is unsigned; `-(x as u8)` would be signed.
        let (_, sgn) = parse("-x as u8");
        assert!(!sgn.eval(), "`-x as u8` is `(-x) as u8`, an unsigned type");
        // The cast target decides the width, whichever way the negation is read,
        // so the value of the negation is not where the two readings differ.
        let (v, _) = parse("-x as u8");
        assert_eq!(smt::bits(v), 8, "the cast target is the width");
        // A cast *after* a parenthesized negation is the same thing, and is what
        // the explicit spelling looks like.
        let (_, sgn) = parse("(-x) as u8");
        assert!(!sgn.eval(), "`(-x) as u8` is unsigned too");
        // A negation with no cast is still signed, or the fix above would have
        // undone the previous one.
        let (_, sgn) = parse("-x");
        assert!(sgn.eval(), "a negation with no cast is signed");
        // A negation of an *unsigned* name is a rustc error (`E0600`), so it is
        // refused rather than decided.
        let unsigned = BTreeSet::new();
        let mut p = Parser::new("-x", &args, None, &unsigned, false);
        assert!(p.parse_expr().is_err(), "`-x` for a `u8` does not compile");
    }

    /// Unary `!` on a value is *bitwise* NOT and binds *tighter* than `==`, so
    /// `!x == 5` is `(!x) == 5`, not `!(x == 5)`.
    ///
    /// The parser handled `!` only at the *predicate* level, so `!x == 5` was read
    /// as the predicate `!(x == 5)` — `x != 5` — where Rust means `x == 250` for a
    /// `u8`. That is a different predicate, so it is a *wrong verdict*, not a
    /// refusal, and a bare `!x` was not readable at all. The fix splits the two:
    /// `bang_is_predicate` decides which reading applies, a predicate `!` stays at
    /// `parse_cmp`, and a value `!` is a prefix at `parse_neg` (bitwise NOT, the
    /// same term `mir/exec.rs` builds for `UnOp::Not`).
    #[test]
    fn a_bang_on_a_value_is_bitwise_not_and_binds_tight() {
        let mut args = BTreeMap::new();
        // A real variable, so the assignment below is what `x` reads.
        args.insert("x".to_string(), smt::var(8));
        let unsigned = BTreeSet::new();
        let eval_const = |text: &str| {
            let mut p = Parser::new(text, &args, None, &unsigned, false);
            let (v, _) = p.parse_expr().expect("parses");
            p.expect_end().expect("no trailing tokens");
            smt::evaluate(v, |_| None).expect("a constant")
        };
        // The value of an expression under an assignment to `x`.
        let eval_at = |text: &str, x: u64| {
            let mut p = Parser::new(text, &args, None, &unsigned, false);
            let (v, _) = p.parse_expr().expect("parses");
            p.expect_end().expect("no trailing tokens");
            smt::evaluate(v, |_| Some(x)).expect("decides")
        };
        // The expression as a *predicate*, so a comparison is decided as a whole.
        let pred = |text: &str, x: u64| {
            let mut p = Parser::new(text, &args, None, &unsigned, false);
            let pr = p.parse_or().expect("parses as a predicate");
            p.expect_end().expect("no trailing tokens");
            smt::evaluate_pred(pr, |_| Some(x)).expect("decides")
        };
        // `!0` is `255` at 8 bits: bitwise NOT, not a boolean.
        assert_eq!(eval_const("!0"), 0xFF, "`!` on a value is bitwise NOT");
        // `!!0` is `0`: the complement of the complement.
        assert_eq!(eval_const("!!0"), 0, "a double `!` is the identity");
        // `!1 + 1` is `(!1) + 1` = `254 + 1` = `255`. Read at the predicate level
        // it would not even parse as arithmetic.
        assert_eq!(eval_const("!1 + 1"), 0xFF, "`!` binds tighter than `+`");
        // `0 & !1` is `0 & 254` = `0`; the prefix applies to the literal `1`.
        assert_eq!(eval_const("0 & !1"), 0, "`!` applies to the operand, not the `&`");
        assert_eq!(eval_at("!x", 0), 0xFF, "a bare `!x` reads, and is bitwise");
        assert_eq!(eval_at("!x", 250), 5, "`!250` is `5` at 8 bits");
        // `!x & 1` is `(!x) & 1`; at `x == 0` that is `255 & 1 == 1`. If `&` bound
        // first the value would be `!(0 & 1) == 254`, so this separates the two.
        assert_eq!(eval_at("!x & 1", 0), 1, "`!` binds tighter than `&`");

        // `!x == 5` is decided at the *predicate* level, so assert the predicate
        // itself: `(!x) == 5` holds at `x == 250` and not at `x == 5`, which is the
        // opposite of what `!(x == 5)` would say.
        assert!(pred("!x == 5", 250), "`!x == 5` is `(!x) == 5`: true at 250");
        assert!(!pred("!x == 5", 5), "`!x == 5` is `(!x) == 5`: false at 5");
        // `!(x == 5)` is the predicate reading, and must still negate: false at 5
        // (the comparison holds, so its negation does not), true at 250.
        assert!(!pred("!(x == 5)", 5), "`!(x == 5)` is `x != 5`: false at 5");
        assert!(pred("!(x == 5)", 250), "`!(x == 5)` is `x != 5`: true at 250");
        // `!(x + 1)` holds *arithmetic*, so `!` is the value form here even though a
        // `(` follows: `!` is bitwise NOT, and `!(x + 1) == 5` is `(!(x + 1)) == 5`,
        // which holds at `x == 249` and not at `x == 5`. This is the case that
        // separates `bang_is_predicate`'s lookahead from "a `(` follows".
        assert!(pred("!(x + 1) == 5", 249), "`!(x + 1)` is `(!(x + 1))`, a value");
        assert!(!pred("!(x + 1) == 5", 5), "`!(x + 1)` is not a predicate negation");
    }

    /// A shift amount or a divisor may be a *constant expression*, and the reader
    /// must fold it before asking whether it is constant or zero.
    ///
    /// `const_of` answers "is this node a literal", which is the wrong question for
    /// both: `x >> 1 + 1` folds to `x >> 2` (constant, so the shift is fine), and
    /// `x % (1 - 1)` folds to `x % 0` (zero, so it must be refused). Asking the
    /// literal question misclassified the first as symbolic -- a barrel shifter in
    /// the body, an undecided query -- and let the second past the zero guard, so
    /// the reader built `srem(x, 0)` and returned a *definite verdict* from an
    /// undefined operation. `const_value` folds instead, which is what both want.
    #[test]
    fn a_constant_expression_is_folded_before_it_is_classified() {
        let mut args = BTreeMap::new();
        args.insert("x".to_string(), smt::var(8));
        args.insert("y".to_string(), smt::var(8));
        let unsigned = BTreeSet::new();
        let parse = |text: &str| {
            let mut p = Parser::new(text, &args, None, &unsigned, false);
            let (v, _) = p.parse_expr().expect("parses");
            p.expect_end().expect("no trailing tokens");
            v
        };
        // A folded shift amount is a constant shift: `x >> 1 + 1` is `x >> 2`.
        let folded = parse("x >> 1 + 1");
        let literal = parse("x >> 2");
        assert_eq!(smt::evaluate(folded, |_| Some(8)), Some(2));
        assert_eq!(
            smt::evaluate(folded, |_| Some(8)),
            smt::evaluate(literal, |_| Some(8)),
            "`x >> 1 + 1` must read as `x >> 2`"
        );
        // A *symbolic* amount is still refused, not modelled as a barrel shifter.
        let mut p = Parser::new("x >> y", &args, None, &unsigned, false);
        assert!(p.parse_expr().is_err(), "a symbolic shift amount is refused");
        // A divisor of constant zero is refused however it is spelled.
        let mut p = Parser::new("x % (1 - 1)", &args, None, &unsigned, false);
        assert!(p.parse_expr().is_err(), "a folded zero divisor is refused");
        // A constant, non-zero divisor folds and reads: `4 / (1 + 1)` is `2`.
        assert_eq!(smt::evaluate(parse("x / (1 + 1)"), |_| Some(4)), Some(2));
    }

    /// A radix literal is read at its *radix*, and one that is not an exact
    /// integer is refused rather than truncated.
    ///
    /// Every literal used to be read as decimal: the digit run stopped at the `x`
    /// of `0xFF` and the rest was skipped as a type suffix, so the value was `0`.
    /// That is a wrong *value*, and a wrong value in a precondition is a false
    /// proof -- `requires: x == 0xFF` became `x == 0`, and `ensures: ret == 0` was
    /// "proved" for a function returning `255`. Reading at the radix fixes the
    /// value; refusing the malformed shapes (`0b12`, `0o9`, `0xg`, `0xFFg`, past
    /// `u64`) keeps the fix from trading one silent number for another.
    #[test]
    fn a_radix_literal_is_read_at_its_radix_or_refused() {
        let mut args = BTreeMap::new();
        args.insert("x".to_string(), smt::var(16));
        let unsigned = BTreeSet::new();
        let val = |text: &str| {
            let mut p = Parser::new(text, &args, None, &unsigned, false);
            let (v, _) = p.parse_expr().expect("parses");
            p.expect_end().expect("no trailing tokens");
            smt::evaluate(v, |_| None).expect("a constant")
        };
        let refuses = |text: &str| {
            let mut p = Parser::new(text, &args, None, &unsigned, false);
            p.parse_expr().is_err() || p.expect_end().is_err()
        };
        // Each radix reads at its own radix, not decimal.
        assert_eq!(val("0xFF"), 255, "`0xFF` is 255, not 0");
        assert_eq!(val("0x10"), 16, "`0x10` is 16, not 0");
        assert_eq!(val("0b1010"), 10, "`0b1010` is 10, not 0");
        assert_eq!(val("0o17"), 15, "`0o17` is 15, not 0");
        assert_eq!(val("0xFFFF"), 65535);
        // Underscores are separators in any radix, and a type suffix is dropped.
        assert_eq!(val("0xFF_FF"), 65535);
        assert_eq!(val("1_000"), 1000);
        assert_eq!(val("0xFFu8"), 255);
        assert_eq!(val("100_"), 100, "a trailing `_` is a separator");
        // A malformed literal is refused, never partially read.
        assert!(refuses("0b12"), "`0b12` has a non-binary digit");
        assert!(refuses("0o9"), "`0o9` has a non-octal digit");
        assert!(refuses("0xg"), "`0xg` has no hex digits");
        assert!(refuses("0xFFg"), "`0xFFg` has an unknown suffix");
        assert!(refuses("18446744073709551616"), "past `u64` is refused");
    }

    /// A literal that does not fit the operand's *signed* width is refused, even
    /// though its bit pattern does.
    ///
    /// `128` for an `i8` is `0x80`, which is exactly the bit pattern of `-128`, so
    /// a reader that only asks "does this fit in eight *unsigned* bits?" accepts it
    /// and reads `x <= 128` as `x <= -128`. rustc rejects `x <= 128` for an `i8`
    /// ("literal out of range for `i8`"), and the wrong reading is a false proof:
    /// `requires: x <= 128` with `ensures: x != 127` *held*. The `i8::MIN` bound
    /// shares the bit pattern and must still be accepted, which is why the fix
    /// distinguishes a non-negative literal from a signed constant rather than
    /// refusing every `0x80`.
    #[test]
    fn an_out_of_range_literal_is_refused_at_the_operand_width() {
        let mut args = BTreeMap::new();
        args.insert("x".to_string(), smt::var(8));
        let mut signed = BTreeSet::new();
        signed.insert("x".to_string());
        // A whole *predicate*, so the comparison and its width alignment run.
        let reads = |text: &str| {
            let mut p = Parser::new(text, &args, None, &signed, false);
            let pr = p.parse_or().expect("parses");
            p.expect_end().expect("no trailing tokens");
            smt::evaluate_pred(pr, |_| Some(0))
        };
        // `x <= 128` and `x >= -129` are both Rust errors for an `i8`, so they are
        // refused, not read as `x <= -128` / `x >= 127`.
        let mut p = Parser::new("x <= 128", &args, None, &signed, false);
        assert!(p.parse_or().is_err(), "`x <= 128` must be refused for an `i8`");
        let mut p = Parser::new("x >= -129", &args, None, &signed, false);
        assert!(p.parse_or().is_err(), "`x >= -129` must be refused for an `i8`");
        // The boundaries that *do* fit still read, and mean what they say.
        assert_eq!(reads("x <= 127"), Some(true), "127 is i8::MAX");
        assert_eq!(reads("x >= -128"), Some(true), "-128 is i8::MIN");
        let mut p = Parser::new("x == 128", &args, None, &signed, false);
        assert!(p.parse_or().is_err(), "`x == 128` is refused too");
        // Two *constants* have no typed name to take a width from, but the fit
        // check still runs: `128 <= i8::MAX` is a `literal out of range` error, and
        // reading `128` as `0x80` made it `-128 <= 127` -- always true. The in-range
        // counterpart and the named bound both still read.
        let mut p = Parser::new("128 <= i8::MAX", &args, None, &signed, false);
        assert!(
            p.parse_or().is_err(),
            "`128 <= i8::MAX` must be refused (literal out of range for `i8`)"
        );
        let mut p = Parser::new("127 <= i8::MAX", &args, None, &signed, false);
        assert!(p.parse_or().is_ok(), "`127 <= i8::MAX` is well-typed and must read");
        let mut p = Parser::new("i8::MIN <= i8::MAX", &args, None, &signed, false);
        assert!(p.parse_or().is_ok(), "`i8::MIN <= i8::MAX` must read");
    }

    /// A constant *arithmetic* expression is folded exactly, so one that overflows
    /// its operand width is refused rather than wrapping to a wrong value.
    ///
    /// `200u8 + 100u8` is a rustc const-eval error. Folding it mod 256 gave `44`,
    /// so `x <= 200 + 100` read as `x <= 44` -- a *stronger* precondition than the
    /// author wrote (`x <= 300`, which admits every `u8`) -- and `ensures: ret <= 44`
    /// was proved for a body that fails at `x == 100`. The check has to see the
    /// exact value, so the fold widens past the operand width instead of wrapping;
    /// the ordinary range check then refuses the shape when the operand it meets is
    /// too narrow, while a result that fits a wider operand still reads.
    #[test]
    fn an_overflowing_constant_expression_is_refused_not_wrapped() {
        let mut args = BTreeMap::new();
        args.insert("x".to_string(), smt::var(8));
        let signed: BTreeSet<String> = BTreeSet::new();
        // A whole predicate, so the comparison's width alignment runs too.
        let parses = |text: &str| {
            let mut p = Parser::new(text, &args, None, &signed, false);
            p.parse_or().is_ok()
        };
        // Overflowing sums, differences and products are all rustc errors, so
        // they are refused rather than folded to `44`, `255` and `1`.
        assert!(!parses("x <= 200 + 100"), "`200 + 100` overflows a `u8`");
        assert!(!parses("x >= 0 - 1"), "`0 - 1` underflows a `u8`");
        assert!(!parses("x == 255 + 1"), "`255 + 1` overflows a `u8`");
        assert!(!parses("x <= 200 * 2"), "`200 * 2` overflows a `u8`");
        // A sum that *does* fit reads as written, and a sum whose overflow is
        // legal because a wider operand types it still reads.
        assert!(parses("x <= 100 + 44"), "`100 + 44` fits a `u8` and must read");
        assert!(parses("x as u16 <= 200 + 100"), "`300` fits a `u16` and must read");
        assert!(parses("x <= 2 * 3 % 4"), "a fold that fits must still read");
        // The signed case is the trap: `i8::MAX + 1` is `128`, which fits an
        // unsigned byte but not a signed one. Widening at the *expression's*
        // signedness is what refuses it; an unsigned widening left it at eight bits
        // where it read as `-128` -- a new false proof in place of the old one.
        let mut sargs = BTreeMap::new();
        sargs.insert("y".to_string(), smt::var(8));
        let mut sset = BTreeSet::new();
        sset.insert("y".to_string());
        let sparses = |text: &str| {
            let mut p = Parser::new(text, &sargs, None, &sset, false);
            p.parse_or().is_ok()
        };
        assert!(!sparses("y <= i8::MAX + 1"), "`i8::MAX + 1` overflows an `i8`");
        assert!(!sparses("y <= 127 + 1"), "`127 + 1` overflows an `i8`");
        assert!(sparses("y <= i8::MAX"), "`i8::MAX` must read");
        assert!(sparses("y >= i8::MIN"), "`i8::MIN` must read");
    }

    /// A constant `/` or `%` that overflows the signed operand is refused.
    ///
    /// `i8::MIN / -1` is `128`, which does not fit an `i8`; rustc rejects it at
    /// compile time (and panics at runtime). The engine's divider wraps it to
    /// `MIN`, a wrong value, so the fold refuses the shape instead of handing the
    /// comparison a number the author never wrote.
    #[test]
    fn an_overflowing_constant_division_is_refused() {
        let mut args = BTreeMap::new();
        args.insert("x".to_string(), smt::var(8));
        let mut signed = BTreeSet::new();
        signed.insert("x".to_string());
        let parses = |text: &str| {
            let mut p = Parser::new(text, &args, None, &signed, false);
            p.parse_or().is_ok()
        };
        assert!(!parses("x == i8::MIN / -1"), "`i8::MIN / -1` overflows an `i8`");
        assert!(!parses("x == i8::MIN % -1"), "`i8::MIN % -1` overflows an `i8`");
        // In-range constant division still reads.
        assert!(parses("x == 100 / 2"), "`100 / 2` is `50` and must read");
        assert!(parses("x == -100 / 2"), "`-100 / 2` is `-50` and must read");
    }

    /// A signed constant compared with an unsigned operand is refused.
    ///
    /// Rust infers a literal's type from the operand it meets, so `x == -1` for a
    /// `u8` does not compile. The reader carries the negation as a bit pattern at
    /// the operand's width, which made `x == -1` read as `x == 255` -- a wrong
    /// value, and `ensures: ret == 255` was *proved* for a body returning `x`. The
    /// shape is refused rather than read, because the wrong reading is a proof and
    /// a proof cannot be a warning.
    ///
    /// The refusal is narrow on purpose: a bare literal is unsigned (`x <= 0xFF`
    /// for a `u8` is `255`, not a signed constant), and a signed *name* against an
    /// unsigned constant is not this shape.
    #[test]
    fn a_signed_constant_against_an_unsigned_operand_is_refused() {
        let mut args = BTreeMap::new();
        args.insert("x".to_string(), smt::var(8));
        args.insert("y".to_string(), smt::var(8));
        let mut signed = BTreeSet::new();
        signed.insert("y".to_string());
        let parses = |text: &str| {
            let mut p = Parser::new(text, &args, None, &signed, false);
            p.parse_or().is_ok()
        };
        // `x` is unsigned, the right-hand constant is signed: refused.
        assert!(!parses("x == -1"), "`-1` against a `u8` does not compile");
        assert!(!parses("x >= -1"), "`-1` against a `u8` does not compile");
        assert!(!parses("x <= -1"), "`-1` against a `u8` does not compile");
        // The same shape at the *arithmetic* levels, where it is equally a rustc
        // error and equally a false proof if read: `x + -1 >= 0` is trivially true
        // when `-1` is read as `255`.
        assert!(!parses("x + -1 >= 0"), "`x + -1` for a `u8` does not compile");
        assert!(!parses("x - -1 <= 0"), "`x - -1` for a `u8` does not compile");
        assert!(!parses("x % -1 == 0"), "`x % -1` for a `u8` does not compile");
        assert!(!parses("x * -1 == 255"), "`x * -1` for a `u8` does not compile");
        // And at the bitwise levels, where the same negation is the same rustc error.
        assert!(!parses("x & -1 == 255"), "`x & -1` for a `u8` does not compile");
        assert!(!parses("x | -1 == 0"), "`x | -1` for a `u8` does not compile");
        assert!(!parses("x ^ -1 == 0"), "`x ^ -1` for a `u8` does not compile");
        // The legal cases must still read.
        assert!(parses("x <= 0xFF"), "a bare literal is unsigned and must read");
        assert!(parses("x <= 255"), "a bare literal is unsigned and must read");
        assert!(parses("x + 255 >= 0"), "an unsigned constant still adds and reads");
        assert!(parses("x - 1 <= 255"), "an unsigned difference still reads");
        assert!(parses("x & 255 == x"), "an unsigned mask still reads");
        assert!(parses("x ^ 255 == 0"), "an unsigned xor still reads");
        assert!(parses("y <= -1"), "a signed name against a signed literal reads");
        assert!(parses("y >= i8::MIN"), "a signed bound against a signed name reads");
        assert!(parses("y + -1 <= 0"), "a signed name with a signed constant reads");
        assert!(parses("y ^ -1 == 0"), "a signed name with a signed mask reads");
        // Enumerate *every* operator, because the hole this test closes was found
        // one level at a time: a fix written at the comparison level left the
        // additive level reading `x + -1` as `x + 255`, and a fix written there
        // left the bitwise level reading `x ^ -1` as `x ^ 255`. The reader meets
        // two operands at all of these, so each is asserted rather than reasoned
        // safe. rustc rejects `x <op> -1` for a `u8` for all sixteen.
        //
        // A comparison *is* a predicate, so it stands alone; a value operator is
        // wrapped in `== 0` to make one. The wrap respects the crate's precedence
        // for every wrapped operator, so the inner term is parsed (and refused)
        // before the outer comparison runs.
        for op in ["==", "!=", "<", "<=", ">", ">="] {
            assert!(
                !parses(&format!("x {op} -1")),
                "`x {op} -1` for a `u8` does not compile and must be refused"
            );
            assert!(
                parses(&format!("x {op} 1")),
                "`x {op} 1` for a `u8` is legal and must still read"
            );
        }
        for op in ["+", "-", "*", "/", "%", "&", "|", "^", "<<", ">>"] {
            assert!(
                !parses(&format!("(x {op} -1) == 0")),
                "`x {op} -1` for a `u8` does not compile and must be refused"
            );
            assert!(
                parses(&format!("(x {op} 1) == 0")),
                "`x {op} 1` for a `u8` is legal and must still read"
            );
        }
    }

    /// A *suffixed* literal carries its type's signedness, so a mismatched
    /// constant pair is refused instead of silently read as signed.
    ///
    /// `0u8` is unsigned, so `-1 <= 0u8` is `E0277` (a `u8` cannot be negated).
    /// The tokenizer used to *drop* the suffix, leaving the reader no way to tell
    /// `0u8` from a bare `0`; the pair then had no unsigned side to see, the
    /// both-constant branch of `refuse_mixed_signedness` was not reached (it
    /// required exactly *one* constant), and the comparison was read as *signed*
    /// and silently decided -- `ensures: -1 <= 0u8` "verified" as `-1 <= 0`. The
    /// suffix is now kept, so the unsigned side is visible and the shape is refused.
    #[test]
    fn a_suffixed_literal_carries_its_type_signedness() {
        let args = BTreeMap::new();
        let signed = BTreeSet::new();
        let parses = |text: &str| {
            let mut p = Parser::new(text, &args, None, &signed, false);
            p.parse_or().is_ok()
        };
        // Two constants of different signedness: each is an error, not a decision.
        assert!(!parses("-1 == 0u8"), "`-1 == 0u8` is `E0277` and must be refused");
        assert!(!parses("-1 <= 0u8"), "`-1 <= 0u8` is `E0277` and must be refused");
        assert!(!parses("-1 < 0u8"), "`-1 < 0u8` is `E0277` and must be refused");
        assert!(!parses("0u8 > -1"), "`0u8 > -1` is `E0277` and must be refused");
        assert!(!parses("-1i8 == 0u8"), "`-1i8 == 0u8` is `E0308` and must be refused");
        assert!(!parses("-1i16 == 65535u16"), "`-1i16 == 65535u16` must be refused");
        // The valid pairs still read: two constants of the *same* signedness, a
        // bare literal (untyped) against either, and a signed pair.
        assert!(parses("-1 <= 0"), "`-1 <= 0` is legal and must read");
        assert!(parses("-1i8 <= 0i8"), "`-1i8 <= 0i8` is legal and must read");
        assert!(parses("0u8 <= 255u8"), "`0u8 <= 255u8` is legal and must read");
        assert!(parses("-1 <= 255"), "a bare literal adopts the signed side and reads");
        assert!(parses("255u8 == 255"), "a bare literal adopts the unsigned side");
    }

    /// A `!`-complement of a literal is refused where its sign would change the
    /// meaning.
    ///
    /// `!0 >> 1` is `127` read unsigned and `-1` read signed, and the reader's old
    /// default (a literal is unsigned) *discharged* `ensures: ret <= (!0 >> 1)`
    /// for an `i8` though Rust reads it `ret <= -1`. With no typed operand to fix
    /// the signedness the shape is refused, not guessed; a typed operand reads it
    /// exactly, and the operators where the two signs agree still read.
    #[test]
    fn a_bang_literal_is_refused_where_its_sign_would_change_the_meaning() {
        let mut args = BTreeMap::new();
        args.insert("x".to_string(), smt::var(8));
        let mut signed = BTreeSet::new();
        signed.insert("x".to_string());
        let parses = |text: &str| {
            let mut p = Parser::new(text, &args, None, &signed, false);
            p.parse_or().is_ok()
        };
        // A `!`-complement of a literal has no type of its own: refused at a
        // shift, a `/`/`%`, and an ordering comparison.
        assert!(!parses("(!0 >> 1) == 0"), "`!0 >> 1` has no typed operand");
        assert!(!parses("(!4 >> 2) == 0"), "`!4 >> 2` has no typed operand");
        assert!(!parses("(!4 / 2) == 0"), "`!4 / 2` has no typed operand");
        assert!(!parses("(!4 % 3) == 0"), "`!4 % 3` has no typed operand");
        assert!(!parses("(!0) < 0"), "`!0 < 0` has no typed operand");
        assert!(!parses("(!7) >= 0"), "`!7 >= 0` has no typed operand");
        // Equality too. `==`/`!=` were left readable at first ("they compare bit
        // patterns"), but the two readings of an untyped constant are different
        // *values*, not a different ordering of one: Rust types an untyped constant
        // as `i32`, so `!0` is `-1` and `!0 == 255` is `false`, while the reader
        // built `255u8 == 255` and *verified* `ensures: !0 == 255` -- a false
        // proof. So the ambiguous operand is refused at `==`/`!=` as well.
        assert!(!parses("(!0) == 255"), "`!0 == 255` is `false` in Rust, not provable");
        assert!(!parses("(!0) != 255"), "`!0 != 255` has no typed operand");
        assert!(!parses("(!4) == 251"), "`!4 == 251` is `false` in Rust, not provable");
        assert!(!parses("(!0) == (!0)"), "both operands untyped and ambiguous");
        // Two *bare* literals are unambiguous, so equality still reads.
        assert!(parses("2 == 2"), "two bare literals compare exactly");
        assert!(parses("x == 0"), "a typed operand fixes the reading");
        assert!(parses("x == !x"), "`!x` carries `x`'s type, so the pair is typed");
        // The refusal is narrow. A typed operand fixes the signedness, and a bare
        // literal is non-negative, so both still read.
        assert!(parses("x >> 1 < 0"), "a shift of a name is exact");
        assert!(parses("(!x >> 1) < 0"), "a shift of `!x` is exact");
        assert!(parses("x <= 5"), "a small literal is unambiguous");
        // (`x & !1` and `x == !4` are refused too, but for the unrelated reason
        // that `!1`/`!4` are large non-negative values that do not fit a signed
        // 8-bit operand -- a completeness gap, not a sign guess.)
    }

    #[test]
    fn two_names_of_different_signedness_are_refused() {
        let mut args = BTreeMap::new();
        args.insert("s".to_string(), smt::var(8));
        args.insert("u".to_string(), smt::var(8));
        let mut signed = BTreeSet::new();
        signed.insert("s".to_string());
        let parses = |text: &str| {
            let mut p = Parser::new(text, &args, None, &signed, false);
            p.parse_or().is_ok()
        };
        // Every operator where two operands meet, both orders. A comparison is a
        // predicate and stands alone; a value operator is wrapped to make one.
        for op in ["==", "!=", "<=", ">=", "<", ">"] {
            assert!(
                !parses(&format!("s {op} u")),
                "`s {op} u` for an `i8` and a `u8` does not compile and must be refused"
            );
            assert!(
                !parses(&format!("u {op} s")),
                "`u {op} s` is the same mismatched comparison and must be refused"
            );
        }
        for op in ["+", "-", "*", "/", "%", "&", "|", "^"] {
            assert!(
                !parses(&format!("(s {op} u) == 0")),
                "`s {op} u` for an `i8` and a `u8` does not compile and must be refused"
            );
            assert!(
                !parses(&format!("(u {op} s) == 0")),
                "`u {op} s` is the same mismatched operation and must be refused"
            );
        }
        // The legal cases must still read: two names of the *same* signedness, and
        // a name with a literal of either value.
        assert!(parses("s <= s"), "two signed names read");
        assert!(parses("u <= u"), "two unsigned names read");
        assert!(parses("s < 0"), "a signed name against a bare literal reads");
        assert!(parses("u < 255"), "an unsigned name against a bare literal reads");
        assert!(parses("s < 0 && u > 0"), "both halves legal, the conjunction reads");
        // A shift is exempt: Rust lets the amount have its own type, so `s << u`
        // is legal (the amount must be constant in a contract, but its
        // *signedness* is free).
        assert!(parses("(s >> 1) == 0"), "a signed shift by a constant reads");
    }

    /// An explicit discriminant sets the variant's value and the next continues
    /// from it, not from the variant's position.
    #[test]
    fn an_explicit_discriminant_renumbers_the_rest() {
        let d = def("pub enum E { A, B = 3, C }\n");
        assert_eq!(d.index_of("A"), Some(0));
        assert_eq!(d.index_of("B"), Some(3));
        assert_eq!(d.index_of("C"), Some(4));
        // The tag has to hold `4`, which needs three bits, not the two a count of
        // three would give.
        assert_eq!(d.tag_width(), 3);
    }

    /// A hex, binary or octal literal is read at its own radix.
    #[test]
    fn a_radix_prefixed_discriminant_is_read() {
        let d = def("pub enum E { A = 0x10, B = 0b101, C = 0o7, D }\n");
        assert_eq!(d.index_of("A"), Some(16));
        assert_eq!(d.index_of("B"), Some(5));
        assert_eq!(d.index_of("C"), Some(7));
        assert_eq!(d.index_of("D"), Some(8));
    }

    /// A non-literal discriminant refuses the whole layout, so a contract naming
    /// any variant of the enum is a refusal rather than a guess.
    #[test]
    fn an_unreadable_discriminant_refuses_the_whole_layout() {
        let specs = extract("pub enum E { A, B = 1 << 4, C }\n");
        assert!(!specs.enums.contains_key("E"), "the layout must not be recorded at all");
    }

    /// A struct variant still takes its discriminant, so a later variant's value
    /// is right.
    #[test]
    fn a_struct_variant_still_takes_a_discriminant() {
        let d = def("pub enum E {\n    A,\n    Pair { x: u8 },\n    C,\n}\n");
        assert_eq!(d.index_of("A"), Some(0));
        assert_eq!(d.index_of("Pair"), Some(1));
        assert_eq!(d.index_of("C"), Some(2));
    }

    /// The domain assumed for a tag is the set of discriminants, so a gap is not
    /// excluded.
    #[test]
    fn the_tag_domain_is_the_discriminants() {
        let d = def("pub enum E { A, B = 3, C }\n");
        assert_eq!(d.variants.iter().map(|(_, _, d)| *d).collect::<Vec<_>>(), vec![0, 3, 4]);
    }

    /// An unreadable discriminant on a *one-line* enum must not leave the enum
    /// cursor open.
    ///
    /// The one-line reader returns the variants when it can read them and, for an
    /// unreadable discriminant, used to answer "a multi-line body follows". That
    /// answer opened a cursor *after* the closing brace had already been seen, so
    /// every following line -- including `///` contracts and the `fn` items they
    /// belong to -- was consumed as enum contents. Those functions then had no
    /// contract at all, so they were neither verified nor reported as skipped:
    /// they silently left the check set.
    #[test]
    fn an_unreadable_one_line_enum_does_not_swallow_the_next_contract() {
        let src = "pub enum E { A, B = 1 << 4 }\n\n\
                   /// ensures: ret == 1\n\
                   pub fn f() -> u8 { 0 }\n";
        let specs = extract(src);
        assert!(!specs.enums.contains_key("E"), "the refused layout must not be recorded");
        assert!(
            specs.by_fn.contains_key("f"),
            "the contract after a refused enum must still be read, got: {:?}",
            specs.by_fn.keys().collect::<Vec<_>>()
        );
    }

    /// A `decreases:` line is read as a contract clause, and it is enough on its
    /// own to make a function "carry a claim".
    ///
    /// Both halves matter. If the extractor dropped `decreases:`, a recursive
    /// function would silently lose its induction principle and fall back to
    /// inlining, which reads as "incomplete" rather than as a parse bug. And if a
    /// bare `decreases:` did not count as a claim, the function would not be in
    /// `by_fn` at all, so it would neither be verified nor reported skipped.
    #[test]
    fn a_decreases_clause_is_read_and_counts_as_a_claim() {
        let src = "/// decreases: n\n\
                   pub fn f(n: u8) -> u8 { n }\n";
        let specs = extract(src);
        let c = specs.by_fn.get("f").expect("a `decreases:` alone is a claim");
        assert_eq!(c.decreases, vec!["n".to_string()], "the measure text must be kept");
        assert!(c.requires.is_empty() && c.ensures.is_empty());
    }

    /// The measure is evaluated against the arguments, and its signedness travels
    /// with the value. A signed argument must give a *signed* measure, because the
    /// decrease test is `slt` rather than `ult` for a signed one -- reading `i8`
    /// as unsigned would prove `n - 1 < n` for a measure that actually runs
    /// negative, which is exactly the well-foundedness the check exists to keep.
    #[test]
    fn a_measure_takes_its_sign_from_its_arguments() {
        let mut args = BTreeMap::new();
        args.insert("n".to_string(), smt::var_named(1, 8));
        let consts = BTreeMap::new();

        let unsigned = BTreeSet::new();
        let (_, u_signed) = eval_measure("n", &args, &unsigned, &consts).expect("`n` parses");
        assert!(!u_signed, "an unsigned argument gives an unsigned measure");

        let signed: BTreeSet<String> = ["n".to_string()].into_iter().collect();
        let (_, s_signed) = eval_measure("n", &args, &signed, &consts).expect("`n` parses");
        assert!(s_signed, "a signed argument gives a signed measure");

        // A compound measure keeps the argument's sign through the arithmetic.
        let (_, sum_signed) =
            eval_measure("n + 1", &args, &signed, &consts).expect("`n + 1` parses");
        assert!(sum_signed, "the sign must survive the addition");
    }

    /// A measure that does not parse is an error, not a silently absent measure.
    ///
    /// This is the same rule the other clauses follow: an unreadable clause must
    /// never become `true` (or here, `None`), because then a function would be
    /// verified against a contract the reader never understood.
    #[test]
    fn an_unreadable_measure_is_an_error() {
        let mut args = BTreeMap::new();
        args.insert("n".to_string(), smt::var_named(1, 8));
        let consts = BTreeMap::new();
        let signed = BTreeSet::new();
        assert!(eval_measure("n +", &args, &signed, &consts).is_err(), "a dangling `+`");
        assert!(eval_measure("nope", &args, &signed, &consts).is_err(), "an unknown name");
        assert!(eval_measure("", &args, &signed, &consts).is_err(), "an empty measure");
    }

    /// A one-line *struct* body must not swallow the functions after it either.
    ///
    /// `struct_head` accepted any line containing `{` and opened a multi-line field
    /// cursor, so `pub struct B { pub lo: u8 }` left the cursor open with the brace
    /// already closed: every following line -- the `///` contracts and the `fn`
    /// items -- was consumed as struct fields. Those functions then had no contract
    /// at all, so they were neither verified nor reported as skipped; they silently
    /// left the check set. The enum reader has distinguished an inline body from a
    /// multi-line one all along; the struct reader did not.
    #[test]
    fn a_one_line_struct_does_not_swallow_the_next_contract() {
        let src = "pub struct B { pub lo: u8 }\n\n\
                   /// ensures: ret == 1\n\
                   pub fn f() -> u8 { 0 }\n";
        let specs = extract(src);
        assert!(
            specs.structs.contains_key("B"),
            "a one-line struct body must still be recorded, got: {:?}",
            specs.structs.keys().collect::<Vec<_>>()
        );
        assert_eq!(
            specs.structs["B"].fields.iter().map(|(n, _)| n.as_str()).collect::<Vec<_>>(),
            vec!["lo"],
            "the one-line body's field must be read out of the head line"
        );
        assert!(
            specs.by_fn.contains_key("f"),
            "the contract after a one-line struct must still be read, got: {:?}",
            specs.by_fn.keys().collect::<Vec<_>>()
        );
    }

    /// The same for the multi-line path: the refusal must close the cursor at the
    /// brace, not at whatever `}` comes next.
    #[test]
    fn a_refused_multi_line_enum_does_not_swallow_the_next_contract() {
        let src = "pub enum E {\n    A,\n    B = 1 << 4,\n}\n\n\
                   /// ensures: ret == 1\n\
                   pub fn f() -> u8 { 0 }\n";
        let specs = extract(src);
        assert!(!specs.enums.contains_key("E"), "the refused layout must not be recorded");
        assert!(
            specs.by_fn.contains_key("f"),
            "the contract after a refused multi-line enum must still be read, got: {:?}",
            specs.by_fn.keys().collect::<Vec<_>>()
        );
    }

    /// A contract written above a struct must not attach to the next function.
    ///
    /// `struct_head` and `enum_head` matched their line and `continue`d without
    /// clearing the pending contract, so a doc comment above a struct -- which is
    /// the struct's documentation, not a function's contract -- carried over to
    /// the next `fn`. A leaked `requires` is a false proof when it is satisfiable:
    /// `requires: x == 0` above a struct makes `ensures: ret == 0` for a body
    /// returning `x` *verify*, because the check is only made for `x == 0`. The
    /// same contract with no struct above it is correctly refuted.
    #[test]
    fn a_contract_above_a_struct_does_not_attach_to_the_next_function() {
        let src = "/// requires: x == 0\n\
                   pub struct S { pub v: u8 }\n\
                   /// ensures: ret == 0\n\
                   pub fn f(x: u8) -> u8 { x }\n";
        let specs = extract(src);
        let c = specs.by_fn.get("f").expect("`f` must carry a contract");
        assert!(
            c.requires.is_empty(),
            "the struct's doc comment leaked into `f`: {:?}",
            c.requires
        );
        assert_eq!(c.ensures, vec!["ret == 0"], "the function's own `ensures` must survive");
    }

    /// The same leak through an enum head, which had the identical shape.
    #[test]
    fn a_contract_above_an_enum_does_not_attach_to_the_next_function() {
        let src = "/// requires: x == 0\n\
                   pub enum E { A, B }\n\
                   /// ensures: ret == 0\n\
                   pub fn f(x: u8) -> u8 { x }\n";
        let specs = extract(src);
        let c = specs.by_fn.get("f").expect("`f` must carry a contract");
        assert!(c.requires.is_empty(), "the enum's doc comment leaked into `f`: {:?}", c.requires);
        assert_eq!(c.ensures, vec!["ret == 0"]);
    }

    /// A trailing line comment on a variant line is not part of the variant.
    ///
    /// `B = 3, // special` puts the comma *before* the comment, so trimming a
    /// trailing comma off the raw line leaves `B = 3, // special` -- the comma is
    /// no longer last. The discriminant reader then rejected the whole line and
    /// the layout was dropped, taking every contract that named a variant with it.
    #[test]
    fn a_trailing_comment_on_a_variant_is_not_part_of_it() {
        let src = "pub enum E {\n    A,\n    B = 3, // special\n    C,\n}\n";
        let d = def(src);
        assert_eq!(d.index_of("A"), Some(0));
        assert_eq!(d.index_of("B"), Some(3));
        assert_eq!(d.index_of("C"), Some(4), "C follows B's explicit value, not its position");
    }

    /// A comment after an implicit variant must not change its numbering either.
    #[test]
    fn a_trailing_comment_on_an_implicit_variant_is_ignored() {
        let src = "pub enum E {\n    A, // first\n    B,\n}\n";
        let d = def(src);
        assert_eq!(d.index_of("A"), Some(0));
        assert_eq!(d.index_of("B"), Some(1));
    }

    fn field_env_with(consts: &[(&str, Const)]) -> FieldEnv {
        let mut e = FieldEnv::default();
        for (k, v) in consts {
            e.consts.insert((*k).to_string(), v.clone());
        }
        e
    }

    /// A contract resolves a named `const` to its literal value, at the item's own
    /// width and sign.
    #[test]
    fn a_contract_reads_a_const_name_as_its_value() {
        let args = BTreeMap::new();
        let env = field_env_with(&[
            ("LIMIT", Const::UInt(10, Some(Ty::U8))),
            ("NEG", Const::UInt(0xff, Some(Ty::I8))),
            ("B", Const::Bool(true)),
        ]);
        // `LIMIT` is `10`; a precondition demanding `<= 9` is refutable, and one
        // demanding `<= 10` holds. This pins the value, not just that it parsed.
        let p = eval_requires("LIMIT <= 10", &args, &BTreeSet::new(), &env).unwrap();
        assert_eq!(smt::prove(p), smt::Verdict::Valid);
        let p = eval_requires("LIMIT <= 9", &args, &BTreeSet::new(), &env).unwrap();
        assert_ne!(smt::prove(p), smt::Verdict::Valid, "LIMIT is 10, so `<= 9` must not hold");
        // A negative constant keeps its sign: `NEG <= -1` holds, `NEG >= 0` does not.
        let p = eval_requires("NEG <= -1", &args, &BTreeSet::new(), &env).unwrap();
        assert_eq!(smt::prove(p), smt::Verdict::Valid);
        let p = eval_requires("NEG >= 0", &args, &BTreeSet::new(), &env).unwrap();
        assert_ne!(smt::prove(p), smt::Verdict::Valid, "NEG is -1, so `>= 0` must not hold");
        // A boolean constant compared against a boolean literal.
        let p = eval_requires("B == true", &args, &BTreeSet::new(), &env).unwrap();
        assert_eq!(smt::prove(p), smt::Verdict::Valid);
    }

    /// An argument shadows a constant of the same name, so a contract naming an
    /// argument keeps resolving to it. Reading the constant there would bind the
    /// wrong value -- a false proof, not a refusal.
    #[test]
    fn an_argument_shadows_a_const_of_the_same_name() {
        let mut args = BTreeMap::new();
        args.insert("LIMIT".to_string(), smt::var_named(1, 8));
        let env = field_env_with(&[("LIMIT", Const::UInt(10, Some(Ty::U8)))]);
        // The argument is symbolic, so `LIMIT <= 10` cannot be proved even though
        // the constant would make it true -- proof that the argument won.
        let p = eval_requires("LIMIT <= 10", &args, &BTreeSet::new(), &env).unwrap();
        assert_ne!(smt::prove(p), smt::Verdict::Valid);
    }

    /// A name that is not a literal constant is refused, not guessed at.
    #[test]
    fn a_non_literal_const_name_is_refused() {
        let args = BTreeMap::new();
        let env = field_env_with(&[("EXPR", Const::Other("_".into()))]);
        assert!(eval_requires("EXPR <= 1", &args, &BTreeSet::new(), &env).is_err());
        // A misspelled name is still refused as an unknown name.
        assert!(eval_requires("LIMITT <= 1", &args, &BTreeSet::new(), &env).is_err());
    }

    /// The crate-level `const` scanner reads items at brace depth zero and only
    /// those.
    ///
    /// The dump cannot tell a crate-level `const` from a function-local one, so the
    /// source's brace depth is the second tell -- the one that catches a
    /// crate-level constant a contract names but no body uses. Reading too much
    /// would re-open the local-leak false proof, so the negative cases matter as
    /// much as the positive one: a local item, an associated constant in an `impl`,
    /// a `const` generic parameter, and a `const` inside a string or comment must
    /// all be left out.
    #[test]
    fn crate_level_consts_reads_only_module_scope_items() {
        let src = r#"
// const COMMENTED: u8 = 1;
const LIMIT: u8 = 10;
pub const PUB_LIMIT: u8 = 11;
const TYPO: u8 = 12;

/// const DOC: u8 = 13;
pub fn f() -> u8 {
    const LOCAL: u8 = 3;
    let s = "const IN_STRING: u8 = 4";
    let _ = s;
    LOCAL
}

impl Foo {
    const ASSOC: u8 = 5;
}

fn g<const N: usize>() -> usize { N }
"#;
        let names = crate_level_consts(src);
        assert!(names.contains("LIMIT"), "a crate-level const is read: {names:?}");
        assert!(names.contains("PUB_LIMIT"), "a `pub const` is read: {names:?}");
        assert!(names.contains("TYPO"), "a plain crate-level const is read: {names:?}");
        assert!(!names.contains("COMMENTED"), "a commented-out item is not read: {names:?}");
        assert!(!names.contains("DOC"), "a doc-comment line is not read: {names:?}");
        assert!(!names.contains("LOCAL"), "a function-local const is not read: {names:?}");
        assert!(!names.contains("IN_STRING"), "a const inside a string is not read: {names:?}");
        assert!(!names.contains("ASSOC"), "an associated const is not read: {names:?}");
    }
}
