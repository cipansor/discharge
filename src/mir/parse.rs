//! Parse the textual MIR dump that `rustc --emit=mir` prints.
//!
//! This is deliberately a parser for the *printed* form rather than a compiler
//! plugin. Reaching into `rustc`'s internals would mean pinning a nightly and
//! linking `rustc_driver`, which makes the tool unusable for most people; the
//! printed form is stable enough in practice and needs only a `rustc` on `PATH`.
//! The trade is explicit: when `rustc` changes the dump format, this parser has
//! to change with it, and an unrecognized line becomes [`Stmt::Unknown`] or
//! [`Term::Unknown`] — which the executor turns into `Unknown`, never into a
//! proof. A parse failure is a gap in coverage, not a silent assumption.

use std::collections::BTreeMap;

/// A local variable slot, `_0`, `_1`, …
pub type LocalIdx = u32;

/// A bit-vector (or boolean) type, as far as this frontend models it.
///
/// Anything not listed becomes [`Ty::Other`], and an operation on `Ty::Other`
/// makes the path unknown rather than being guessed at.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Ty {
    Bool,
    U8,
    U16,
    U32,
    U64,
    U128,
    Usize,
    I8,
    I16,
    I32,
    I64,
    I128,
    Isize,
    /// A tuple, e.g. `(u32, bool)` from an overflowing add.
    Tuple(Vec<Ty>),
    /// A fixed-size array, e.g. `[u32; 3]`.
    Array(Box<Ty>, u64),
    /// A slice, e.g. `[u32]` — the referent of a `&[u32]`. Its *length* is not
    /// part of the type (that is the whole point of a slice), so it is a symbolic
    /// input rather than a constant; see `FieldEnv::bind_indexed_len`. An array's
    /// length, by contrast, is in its type; see `FieldEnv::bind_array_len`.
    Slice(Box<Ty>),
    Unit,
    /// A shared or mutable reference. Modelled as its referent's width, because
    /// the frontend does not track aliasing (see the module docs on scope).
    Ref(Box<Ty>),
    /// Anything else: structs, enums, `!`, …
    Other(String),
}

/// The width `usize`/`isize` are modelled at, and so the width of a slice's
/// length and its indices. This tool's own host target is 64-bit; a slice length
/// is only ever compared against indices of the same width, so one constant keeps
/// the two in step.
pub const USIZE_WIDTH: u8 = 64;

impl Ty {
    /// Bit width, when the type is a bit-vector or boolean.
    pub fn width(&self) -> Option<u8> {
        Some(match self {
            Ty::Bool => 1,
            Ty::U8 => 8,
            Ty::U16 => 16,
            Ty::U32 => 32,
            Ty::U64 | Ty::Usize => USIZE_WIDTH,
            Ty::U128 => 128,
            Ty::I8 => 8,
            Ty::I16 => 16,
            Ty::I32 => 32,
            Ty::I64 | Ty::Isize => USIZE_WIDTH,
            Ty::I128 => 128,
            _ => return None,
        })
    }

    /// True when this type is, or contains, one the 64-bit engine cannot
    /// represent — today only `u128`/`i128`.
    ///
    /// Separate from `width()` on purpose. `width()` still reports 128, because
    /// the *constant reader* needs that number to compute `u128::MAX` and the
    /// two's-complement pattern of a negative literal; refusing the width there
    /// would turn a readable constant into `Other`. What must not happen is that a
    /// 128-bit *local* reaches a width-taking constructor, and this predicate is
    /// the one place that is decided. Descends into aggregates because a
    /// `[u128; 4]` argument is bound field by field, and it is the leaf that
    /// panics.
    pub fn has_unrepresentable_leaf(&self) -> bool {
        match self {
            Ty::U128 | Ty::I128 => true,
            Ty::Tuple(xs) => xs.iter().any(Ty::has_unrepresentable_leaf),
            Ty::Array(inner, _) | Ty::Slice(inner) | Ty::Ref(inner) => {
                inner.has_unrepresentable_leaf()
            }
            _ => false,
        }
    }

    /// True for the signed integers, whose comparisons differ from the unsigned ones.
    pub fn is_signed(&self) -> bool {
        matches!(
            self,
            Ty::I8 | Ty::I16 | Ty::I32 | Ty::I64 | Ty::I128 | Ty::Isize
        )
    }

    /// Parse a printed type. `usize`/`isize` are modelled at 64 bits, which is
    /// what this tool's own host target uses.
    pub fn parse(s: &str) -> Ty {
        let s = s.trim();
        match s {
            "bool" => return Ty::Bool,
            "u8" => return Ty::U8,
            "u16" => return Ty::U16,
            "u32" => return Ty::U32,
            "u64" => return Ty::U64,
            "u128" => return Ty::U128,
            "usize" => return Ty::Usize,
            "i8" => return Ty::I8,
            "i16" => return Ty::I16,
            "i32" => return Ty::I32,
            "i64" => return Ty::I64,
            "i128" => return Ty::I128,
            "isize" => return Ty::Isize,
            "()" => return Ty::Unit,
            _ => {}
        }
        if let Some(inner) = s.strip_prefix("&mut ") {
            return Ty::Ref(Box::new(Ty::parse(inner)));
        }
        if let Some(inner) = s.strip_prefix('&') {
            return Ty::Ref(Box::new(Ty::parse(inner)));
        }
        if s.starts_with('(') && s.ends_with(')') {
            let inner = &s[1..s.len() - 1];
            if inner.trim().is_empty() {
                return Ty::Unit;
            }
            return Ty::Tuple(split_top_level(inner, ',').iter().map(|t| Ty::parse(t)).collect());
        }
        if s.starts_with('[') && s.ends_with(']') {
            let inner = &s[1..s.len() - 1];
            let parts = split_top_level(inner, ';');
            if parts.len() == 2 {
                let n = parts[1].trim().parse::<u64>().unwrap_or(0);
                return Ty::Array(Box::new(Ty::parse(&parts[0])), n);
            }
            // `[T]` with no length is a slice, which is what a `&[u8]` argument
            // is a reference to. Distinguishing it from `Other("[u8]")` is what
            // lets `PtrMetadata` and `(*xs)[i]` be modelled at all.
            return Ty::Slice(Box::new(Ty::parse(inner)));
        }
        Ty::Other(s.to_string())
    }
}

/// A projection out of a place: `_3.1` is `Field(1)`, `_2[0]` is `Index(0)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Proj {
    Field(u32),
    Index(u64),
    /// `_2[_3]` — an index that is a local, not a literal.
    ///
    /// A slice read is `(*_1)[_2]` where `_2` came from a constant in the
    /// *body*, but the body is not the only place an index can come from: a
    /// contract may write `xs[i]` with `i` a parameter. Modelling only the
    /// literal form would make the body and the contract disagree about which
    /// element is named, so the variable form is carried too and resolved
    /// against the environment when the place is read.
    IndexVar(u32),
    /// An enum downcast, e.g. the `(_2 as Some)` in `((_2 as Some).0)`.
    ///
    /// The payload of a modelled `Option`-returning call lives here, under the
    /// variant's *discriminant* (`Some` is 1). Keeping it separate from `Field` is
    /// what stops a payload from colliding with a tuple field of the same enum
    /// local, and it is what lets a read be gated on the discriminant: reading `.0`
    /// on a path where the enum is `None` must not hand back a payload that does
    /// not exist.
    ///
    /// A discriminant, not a position: a variant after an explicit discriminant
    /// (`B = 3`) has a value that is not its index, and the arm constants and
    /// payload keys all have to agree on the same number.
    Downcast(u64),
    /// A pointer dereference, printed as `(*_1)`.
    ///
    /// This frontend does not track aliasing, so a dereference of a `&T` argument
    /// reads the same symbolic value the argument itself stands for — which is
    /// exactly what a *reference* means when there is only one owner. It is not a
    /// model of aliasing, and it is refused for a pointer the frontend did not
    /// introduce as an argument (see `Env::get`).
    Deref,
}

/// A place: a local plus a projection path.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Place {
    pub local: LocalIdx,
    pub proj: Vec<Proj>,
}

impl Place {
    pub fn new(local: LocalIdx) -> Place {
        Place { local, proj: Vec::new() }
    }
}

/// A compile-time constant appearing in the MIR.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Const {
    /// A numeric literal, with the type suffix the dump printed (`0_u32`).
    /// The suffix is not decoration: it is the only place the literal's width
    /// appears, and getting it wrong changes the formula.
    UInt(u128, Option<Ty>),
    Bool(bool),
    Unit,
    Other(String),
}

/// A value read by an operation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Operand {
    Copy(Place),
    Move(Place),
    Const(Const),
}

/// Binary operators, both the checked (overloading) and plain forms.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    BitXor,
    BitAnd,
    BitOr,
    Shl,
    Shr,
    Eq,
    Lt,
    Le,
    Ne,
    Ge,
    Gt,
}

impl BinOp {
    fn parse(s: &str) -> Option<BinOp> {
        Some(match s {
            "Add" => BinOp::Add,
            "Sub" => BinOp::Sub,
            "Mul" => BinOp::Mul,
            "Div" => BinOp::Div,
            "Rem" => BinOp::Rem,
            "BitXor" => BinOp::BitXor,
            "BitAnd" => BinOp::BitAnd,
            "BitOr" => BinOp::BitOr,
            "Shl" => BinOp::Shl,
            "Shr" => BinOp::Shr,
            "Eq" => BinOp::Eq,
            "Lt" => BinOp::Lt,
            "Le" => BinOp::Le,
            "Ne" => BinOp::Ne,
            "Ge" => BinOp::Ge,
            "Gt" => BinOp::Gt,
            _ => return None,
        })
    }
}

/// Unary operators.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UnOp {
    Not,
    Neg,
}

/// The right-hand side of an assignment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Rvalue {
    Use(Operand),
    /// `Add(a, b)` etc. — the plain, wrapping-by-MIR-semantics form. Panics are
    /// separate `assert`s, so this does not need to model overflow itself.
    Binary(BinOp, Operand, Operand),
    Unary(UnOp, Operand),
    /// `AddWithOverflow(a, b)` — yields a `(uN, bool)` tuple.
    CheckedBinary(BinOp, Operand, Operand),
    /// `x as T`, with the printed kind (`IntToInt`, `Transmute`, …).
    Cast(Operand, Ty),
    /// An array or tuple literal.
    Aggregate(Vec<Operand>),
    /// A struct literal: `Config { lo: const 7_u8, hi: const 9_u8 }`.
    ///
    /// Kept apart from [`Rvalue::Aggregate`] because the two write to different
    /// stores: a tuple component is read back as `_1.0` and a struct field as
    /// `_1.0`, but a struct's fields are a *declared layout* while a tuple's are
    /// positional, and the contract language can name one but not the other.
    /// The operands are in the order rustc printed them, which is declaration
    /// order -- the same order the `Field(N)` projections index.
    Struct(Vec<Operand>),
    /// `&place`
    Ref(Place),
    /// `Len(place)` — array length.
    Len(Place),
    /// `PtrMetadata(place)` — the metadata of a pointer: for a `&[T]` it is the
    /// slice's length, which is what the `assert` before an index reads. Modelled
    /// for slices only; `PtrMetadata` on any other pointer (a trait object, say)
    /// has metadata this frontend cannot express and stays `Unknown`.
    PtrMetadata(Place),
    /// `discriminant(place)` — the enum tag. Only modelled for the `Option`s
    /// this frontend synthesises for `checked_*`, where the tag is `0` for
    /// `None` and `1` for `Some`.
    Discriminant(Place),
    /// An enum variant construction with a payload: `Msg::Data(const 9_u8)`.
    ///
    /// Kept apart from [`Rvalue::Aggregate`] because the operands are the
    /// *payloads* of one variant, not the elements of a sequence: the tag is the
    /// variant's discriminant and the operands are written as the variant's
    /// fields. A model that stored them as elements would leave the match's
    /// downcast read looking in a store the construction never wrote.
    Variant(String, Vec<Operand>),
    /// Something this frontend does not model.
    Unknown(String),
}

/// A statement inside a basic block.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Stmt {
    Assign(Place, Rvalue),
    /// `StorageLive` / `StorageDead` / `Nop` — no semantic effect here.
    Nop,
    Unknown(String),
}

/// Where a call goes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Callee {
    /// A named function, possibly path-qualified (`core::num::<impl u32>::…`).
    Name(String),
    /// An indirect call through a value, which the frontend does not resolve.
    Indirect(Place),
}

/// A block terminator.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Term {
    Goto(usize),
    SwitchInt {
        discr: Operand,
        cases: Vec<(u128, usize)>,
        otherwise: usize,
    },
    Return,
    /// A call whose result lands in `dest` and then goes to `target`.
    Call {
        callee: Callee,
        args: Vec<Operand>,
        dest: Place,
        target: usize,
    },
    /// `assert(cond, "msg", args…)` — failure is a reachable panic.
    ///
    /// `negated` records a leading `!`, which rustc prints for the overflow,
    /// underflow and division-by-zero asserts (`assert(!(_3.1))`). Dropping it
    /// would invert every one of those checks, so it is carried rather than
    /// folded away.
    Assert {
        cond: Operand,
        negated: bool,
        msg: String,
        msg_args: Vec<Operand>,
        target: usize,
    },
    /// `unreachable`
    Unreachable,
    Unknown(String),
}

/// A basic block.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Block {
    pub id: usize,
    pub stmts: Vec<Stmt>,
    pub term: Term,
}

/// One function's MIR.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MirFn {
    pub name: String,
    /// Local `_0` is the return place; the arguments follow in order.
    pub arg_locals: Vec<LocalIdx>,
    pub ret_ty: Ty,
    pub locals: BTreeMap<LocalIdx, Ty>,
    /// `debug a => _1;` — local to source name, for readable counterexamples.
    ///
    /// First binding wins, so a scoped alias never renames the parameter it
    /// aliases. Every binding, including the ones this map drops, is kept in
    /// [`Self::debug_bindings`].
    pub local_names: BTreeMap<LocalIdx, String>,
    /// Every `debug` binding in the dump, in the order printed, with `None` for a
    /// binding whose target is not a local at all.
    ///
    /// A scoped binding is how `let k = i;` reaches the dump: `k` is not a local
    /// at all, it is another name for `_2`. `local_names` cannot hold it without
    /// renaming `i`, but the contract language still has to resolve `k`, so the
    /// pair is kept here and [`Self::alias_locals`] decides whether it is usable.
    ///
    /// The target is an `Option` because a name can also be bound to something
    /// that is not a local. `let k = i; let k = 0;` prints *two* bindings for `k`
    /// — `debug k => _2;` and, nested deeper, `debug k => const 0_usize;` — and
    /// only the second is what the body's `a[k]` reads. Recording the constant
    /// binding is what lets `alias_locals` see the shadowing and refuse the name;
    /// dropping it (as keeping only local targets would) leaves the stale `_2`
    /// binding looking like the only one, and a contract's `k` would then be
    /// checked against `i` while the body used the constant.
    pub debug_bindings: Vec<(String, Option<LocalIdx>)>,
    pub blocks: Vec<Block>,
    /// Every local the body *writes* — the destination of an assignment, or of a
    /// call.
    ///
    /// This is what makes a scoped `debug` name safe to resolve as an alias. A
    /// `debug k => _2;` means the compiler aliased `k` to local `_2` — which is
    /// usually an argument, because `let k = i;` of a `Copy` value lowers to no
    /// new local at all. Resolving `k` to the argument's variable is exactly
    /// right *provided* `_2` is never assigned: an assignment to a parameter
    /// (`i = 2`) is a write to `_2`, and the alias no longer holds after it.
    ///
    /// The conservative direction is the only safe one here. A local that is
    /// written anywhere makes the alias unusable, so `alias_locals` withholds it
    /// and the subscript stays a refusal. That loses a proof on a shape like
    /// `mut i` reassigned before the alias; it cannot produce a wrong one.
    pub written: std::collections::BTreeSet<LocalIdx>,
}

impl MirFn {
    pub fn ty_of(&self, local: LocalIdx) -> Option<&Ty> {
        self.locals.get(&local)
    }

    /// The first type in this function the bit-level engine cannot represent, if
    /// any.
    ///
    /// The engine is 64-bit; `u128`/`i128` are wider, and every constructor that
    /// takes a width (`smt::var`, `truncate`, …) asserts `1..=64`. A 128-bit type
    /// therefore cannot be modelled at all, and the honest answer is to refuse the
    /// whole function rather than model part of it. Refusing at this one place is
    /// what keeps the refusal *whole*: `arg_vars`, the argument seeding in `exec`
    /// and the loop havoc each consult a type's width, and a 128-bit local would
    /// otherwise be a panic in whichever of them ran first. A panic is not a
    /// refusal — it takes the run down and reports nothing — so the guard has to
    /// come before any of them.
    ///
    /// The check descends into aggregates, because a `[u128; 4]` or a `(u128, u8)`
    /// argument is bound field by field and each field's width is consulted
    /// separately — so the 128-bit leaf is what panics, not the aggregate.
    pub fn first_unrepresentable_type(&self) -> Option<&Ty> {
        if self.ret_ty.has_unrepresentable_leaf() {
            return Some(&self.ret_ty);
        }
        self.arg_locals
            .iter()
            .filter_map(|&l| self.ty_of(l))
            .chain(self.locals.values())
            .find(|t| t.has_unrepresentable_leaf())
    }

    /// Source name → the *argument* local it is a direct alias of.
    ///
    /// A contract may subscript with a name that is not an argument —
    /// `let k = i; a[k]` prints `debug k => _2;` inside a scope block, with no
    /// local of its own. The body's `a[k]` is `_1[_2]`, so the index really is
    /// the argument; only the *contract text* has `k`. Resolving `k` to `_2`
    /// therefore makes the contract name the same index the body reads, which is
    /// the whole point.
    ///
    /// Five conditions keep that sound, and all are checked here rather than left
    /// to the caller:
    ///
    /// * the name is bound exactly once in the dump. A name bound twice has been
    ///   shadowed, and the later binding is the live one — `let k = i; let k = 0;`
    ///   prints `debug k => _2;` and then `debug k => const 0_usize;`. Resolving
    ///   the name to the earlier `_2` would check a contract about the *constant*
    ///   against the argument, which is a wrong proof rather than a missing one.
    ///   Only the earliest binding is ever a parameter alias, and it is only the
    ///   live one when nothing shadows it, so a repeated name is refused outright.
    /// * the aliased local is an argument (never a temporary),
    /// * it is not in [`Self::written`], so nothing reassigns it between the alias
    ///   and its use,
    /// * the name is not already an argument's own name, so a shadowing `let k =
    ///   i;` cannot silently change what a parameter name means, and
    /// * the name does not alias two different arguments, which is a genuine
    ///   ambiguity and not something to guess at.
    ///
    /// A name that fails any test is simply absent from the map, and the
    /// subscript is refused as an unknown name — the same answer as before, with
    /// no wrong one available.
    pub fn alias_locals(&self) -> BTreeMap<String, LocalIdx> {
        let args: std::collections::BTreeSet<LocalIdx> = self.arg_locals.iter().copied().collect();
        let arg_names: std::collections::BTreeSet<String> =
            self.arg_locals.iter().map(|l| self.name_of(*l)).collect();
        // How many times each name is bound, and whether any of those bindings is
        // to a non-local. A name bound more than once is shadowed; a name bound
        // once to a non-local has no argument to resolve to at all.
        let mut bindings: BTreeMap<&str, usize> = BTreeMap::new();
        for (name, _) in &self.debug_bindings {
            *bindings.entry(name.as_str()).or_insert(0) += 1;
        }
        let mut out: BTreeMap<String, LocalIdx> = BTreeMap::new();
        for (name, local) in &self.debug_bindings {
            let Some(local) = local else { continue };
            // A shadowed name is refused: the earlier binding is not the live one,
            // and the later binding is not a local, so neither can be resolved.
            if bindings.get(name.as_str()).copied().unwrap_or(0) != 1 {
                continue;
            }
            if !args.contains(local) || self.written.contains(local) {
                continue;
            }
            // An argument's own name is already in `arg_vars`; letting an alias
            // reuse it would change what that name means.
            if arg_names.contains(name) {
                continue;
            }
            match out.get(name) {
                // Two different arguments under one name: no single value to
                // resolve to, so the name is dropped rather than picked.
                Some(prev) if prev != local => {
                    out.remove(name);
                    continue;
                }
                Some(_) => continue,
                None => {}
            }
            out.insert(name.clone(), *local);
        }
        out
    }

    pub fn block(&self, id: usize) -> Option<&Block> {
        self.blocks.iter().find(|b| b.id == id)
    }

    /// `a`, or `_1` when the local has no debug name.
    pub fn name_of(&self, local: LocalIdx) -> String {
        self.local_names
            .get(&local)
            .cloned()
            .unwrap_or_else(|| format!("_{local}"))
    }
}

/// Every function found in one MIR dump.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct MirProgram {
    pub fns: Vec<MirFn>,
    /// Enum layouts from the source, so a `(base as Variant)` downcast can be
    /// resolved to the discriminant the `switchInt` compares against. Empty when
    /// the caller had no source (the MIR-only entry points), in which case only
    /// the built-in `Option`/`Result` numbering resolves.
    pub enums: BTreeMap<String, EnumLayout>,
}

/// A variant's name and discriminant, for resolving a downcast.
///
/// Distinct from `spec::EnumDef` on purpose: the executor needs only
/// name → index, and the spec reader also carries payload *types* that are of no
/// use here. Keeping the executor's view narrow means the parser has no reason to
/// reach for the contract reader.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct EnumLayout {
    /// `(name, discriminant)` in declaration order. The discriminant is rustc's
    /// value, which is the position only when no variant gives an explicit one
    /// (`B = 3` makes every later variant's value differ from its position).
    pub variants: Vec<(String, u64)>,
}

impl EnumLayout {
    /// The discriminant for a variant name.
    pub fn index_of(&self, name: &str) -> Option<u64> {
        self.variants.iter().find(|(n, _)| n == name).map(|(_, d)| *d)
    }

    /// The width that can hold every discriminant, and no more.
    pub fn tag_width(&self) -> u8 {
        let max = self.variants.iter().map(|(_, d)| *d).max().unwrap_or(0);
        (64 - max.leading_zeros()).max(1) as u8
    }
}

impl MirProgram {
    pub fn get(&self, name: &str) -> Option<&MirFn> {
        // MIR prints bare names for same-crate items; match on the last path
        // segment so a call written `crate::m::f` still resolves.
        self.fns
            .iter()
            .find(|f| f.name == name || f.name.rsplit("::").next() == Some(name))
    }
}

// ---------------------------------------------------------------------------
// Text helpers
// ---------------------------------------------------------------------------

/// Split a struct-literal field `name: value` at the first top-level `:`, and
/// return `(name, value)`.
///
/// A `::` inside the value (a path in a constant, say) is not the separator, so
/// the scan skips a `:` that is immediately followed or preceded by another `:`.
/// Returns `None` when there is no separator at all, which is a shape the
/// printer does not produce for a struct literal.
fn split_field_name(field: &str) -> Option<(&str, &str)> {
    let bytes = field.as_bytes();
    let mut depth = 0i32;
    let mut i = 0;
    while i < bytes.len() {
        match bytes[i] {
            b'(' | b'[' | b'{' | b'<' => depth += 1,
            b')' | b']' | b'}' | b'>' => depth -= 1,
            b':' if depth == 0 => {
                let prev_is_colon = i > 0 && bytes[i - 1] == b':';
                let next_is_colon = bytes.get(i + 1) == Some(&b':');
                if !prev_is_colon && !next_is_colon {
                    return Some((&field[..i], &field[i + 1..]));
                }
            }
            _ => {}
        }
        i += 1;
    }
    None
}

/// Split `s` on `sep`, ignoring separators nested in `()`, `[]`, `{}`, `<…>` or
/// string literals.
pub fn split_top_level(s: &str, sep: char) -> Vec<String> {
    let mut out = Vec::new();
    let mut depth = 0i32;
    let mut cur = String::new();
    let mut in_str = false;
    let mut escaped = false;
    for ch in s.chars() {
        if in_str {
            cur.push(ch);
            if escaped {
                escaped = false;
            } else if ch == '\\' {
                escaped = true;
            } else if ch == '"' {
                in_str = false;
            }
            continue;
        }
        match ch {
            '"' => {
                in_str = true;
                cur.push(ch);
            }
            '(' | '[' | '{' | '<' => {
                depth += 1;
                cur.push(ch);
            }
            ')' | ']' | '}' | '>' => {
                depth -= 1;
                cur.push(ch);
            }
            c if c == sep && depth == 0 => {
                out.push(cur.trim().to_string());
                cur.clear();
            }
            _ => cur.push(ch),
        }
    }
    if !cur.trim().is_empty() || !out.is_empty() {
        out.push(cur.trim().to_string());
    }
    out.retain(|p| !p.is_empty());
    out
}

/// Drop a trailing `: Ty` annotation from `(place: ty)`.
fn strip_annot(s: &str) -> &str {
    let t = s.trim();
    if t.starts_with('(') && t.ends_with(')') {
        let inner = &t[1..t.len() - 1];
        if let Some(i) = find_top_level_colon(inner) {
            return inner[..i].trim();
        }
        // `(*_2)` is a bare dereference, not an annotated place. Stripping the
        // parentheses here would leave `*_2`, which no place parser reads -- the
        // deref arm matches the `(*` prefix and the parens are part of it -- so a
        // whole-place deref would parse as `None` and the read become unknown.
        // The parens are kept for that shape and stripped for every other, which
        // is what `parse_place` expects.
        if inner.trim_start().starts_with('*') {
            return t;
        }
        return inner.trim();
    }
    t
}

fn find_top_level_colon(s: &str) -> Option<usize> {
    let mut depth = 0i32;
    for (i, ch) in s.char_indices() {
        match ch {
            '(' | '[' | '{' => depth += 1,
            ')' | ']' | '}' => depth -= 1,
            ':' if depth == 0 => return Some(i),
            _ => {}
        }
    }
    None
}

/// Parse a local reference like `_3`, returning its index.
fn parse_local(s: &str) -> Option<LocalIdx> {
    let t = s.trim();
    let rest = t.strip_prefix('_')?;
    rest.parse::<LocalIdx>().ok()
}

/// Drop a leading `copy ` / `move ` from a place expression.
///
/// `Len(copy _1)` and `PtrMetadata(copy _1)` print the operand the same way any
/// other rvalue does, so the marker has to be removed before the place parses.
/// Only those two rvalues are routed through here; a plain `copy _1` is handled
/// by `parse_operand`, which keeps the marker as part of the operand.
fn strip_copy(s: &str) -> &str {
    let t = s.trim();
    t.strip_prefix("copy ").or_else(|| t.strip_prefix("move ")).unwrap_or(t)
}

/// The discriminant rustc gives a variant.
///
/// A *declared* layout always answers for a qualified name: `Mode::Idle` is
/// resolved against the layout keyed by `Mode`, so a user enum whose variants are
/// named `Some`/`None` is not mistaken for `Option`. `Option` and `Result` have a
/// fixed, well-known numbering that no source file declares, so an *unqualified*
/// `Some`/`None`/`Ok`/`Err` resolves without a layout. Anything else returns
/// `None` and the place stays unparsed -- which surfaces as an unmodelled read
/// rather than a wrong tag.
pub fn variant_index(name: &str, enums: &BTreeMap<String, EnumLayout>) -> Option<u64> {
    // Generic arguments are part of how a construction is *spelled*
    // (`Option::<u8>::Some`), not part of which variant it is. Dropping them
    // before splitting keeps the qualifier a plain path segment; without it the
    // `::` inside `::<u8>` would make `u8` look like the qualifier and the
    // variant would resolve to nothing.
    let stripped = strip_generics(name);
    let segs: Vec<&str> = stripped.split("::").filter(|s| !s.is_empty()).collect();
    let short = segs.last().copied().unwrap_or(name);
    // A qualified name prints the enum before the variant (`Mode::Idle`); the enum
    // is what the layout is keyed by. A *declared* layout always wins, even when
    // the variant is named `Some` or `None`: a user enum with those names is not
    // `Option`, and resolving it to `Option`'s numbering would take the wrong arm.
    if let Some(qual) = segs.len().checked_sub(2).map(|i| segs[i]) {
        if let Some(l) = enums.get(qual) {
            return l.index_of(short);
        }
        // A *standard* enum has a fixed, well-known numbering that no source file
        // declares, so a qualified spelling of it (`Option::<u8>::Some`) has to
        // resolve the same as the unqualified one. Only these two are recognised;
        // any other qualifier naming an enum this reader does not know is refused,
        // because searching other layouts by variant name would borrow an
        // unrelated enum's numbering.
        return match qual {
            "Option" => match short {
                "None" => Some(0),
                "Some" => Some(1),
                _ => None,
            },
            "Result" => match short {
                "Ok" => Some(0),
                "Err" => Some(1),
                _ => None,
            },
            _ => None,
        };
    }
    // `Option` and `Result` have a fixed, well-known numbering that no source file
    // declares, so an *unqualified* `Some`/`None`/`Ok`/`Err` resolves without a
    // layout. A declared layout with those variant names has already been given the
    // chance to answer above, so this default cannot shadow it.
    match short {
        "None" | "Ok" => return Some(0),
        "Some" | "Err" => return Some(1),
        _ => {}
    }
    // A bare variant name is looked up in every layout. Two layouts claiming the
    // same variant name is a genuine ambiguity, and refusing is the only answer
    // that cannot pick the wrong arm.
    let mut found = None;
    for l in enums.values() {
        if let Some(i) = l.index_of(short) {
            if found.is_some() {
                return None;
            }
            found = Some(i);
        }
    }
    found
}

/// Drop balanced `<…>` generic arguments from a path, so `Option::<u8>::Some`
/// reads as `Option::::Some` (empty segments are filtered by the caller).
fn strip_generics(s: &str) -> String {
    let mut out = String::new();
    let mut depth = 0i32;
    for c in s.chars() {
        match c {
            '<' => depth += 1,
            '>' => {
                if depth > 0 {
                    depth -= 1;
                } else {
                    out.push(c);
                }
            }
            _ if depth == 0 => out.push(c),
            _ => {}
        }
    }
    out
}

/// Parse a place like `_3.1` or `_2` or `_1.0[0]`.
fn parse_place(s: &str, enums: &BTreeMap<String, EnumLayout>) -> Option<Place> {
    let s = strip_annot(s).trim();
    // `(*_1)` — a pointer dereference. Like the downcast below it can appear as a
    // whole place or as a prefix (`(*_1).0`), so the inner place is parsed and the
    // `Deref` step is pushed before the tail projections.
    if let Some(rest) = s.strip_prefix("(*") {
        let close = rest.find(')')?;
        let mut place = parse_place(&rest[..close], enums)?;
        place.proj.push(Proj::Deref);
        return push_projs(place, rest.get(close + 1..)?, enums);
    }
    // `(base as Variant)` — an enum downcast. It can appear as a whole place or
    // as a prefix, so the inner place is parsed and the tail projection is
    // appended to it.
    if let Some(rest) = s.strip_prefix('(') {
        let close = rest.find(')')?;
        let inner = rest[..close].trim();
        let (base, variant) = inner.rsplit_once(" as ")?;
        let mut place = parse_place(base.trim(), enums)?;
        place.proj.push(Proj::Downcast(variant_index(variant.trim(), enums)?));
        return push_projs(place, rest.get(close + 1..)?, enums);
    }
    // A bare local.
    if let Some(idx) = parse_local(s) {
        return Some(Place::new(idx));
    }
    // Otherwise `_N` followed by projections.
    let bytes = s.as_bytes();
    if bytes.first() != Some(&b'_') {
        return None;
    }
    let mut i = 1;
    while i < bytes.len() && bytes[i].is_ascii_digit() {
        i += 1;
    }
    let local = s[1..i].parse::<LocalIdx>().ok()?;
    push_projs(Place::new(local), &s[i..], enums)
}

/// Append a run of `.N`, `[N]` and `(base as Variant)` projections to a place.
fn push_projs(
    mut place: Place,
    mut rest: &str,
    enums: &BTreeMap<String, EnumLayout>,
) -> Option<Place> {
    while !rest.is_empty() {
        if let Some(r) = rest.strip_prefix('.') {
            let n: String = r.chars().take_while(|c| c.is_ascii_digit()).collect();
            if n.is_empty() {
                return None;
            }
            place.proj.push(Proj::Field(n.parse().ok()?));
            rest = &r[n.len()..];
        } else if let Some(r) = rest.strip_prefix('(') {
            // `(_2 as Some)`, and then `.0` continues the loop. rustc prints the
            // downcast as a parenthesised step in the middle of a place, so it
            // has to be consumed here rather than at the front of the string.
            let close = r.find(')')?;
            let inner = r[..close].trim();
            let (_, variant) = inner.rsplit_once(" as ")?;
            place.proj.push(Proj::Downcast(variant_index(variant.trim(), enums)?));
            rest = r.get(close + 1..)?;
        } else {
            // `?` on `strip_prefix` is the same `None` the old `else { return
            // None }` produced, and it is what lets the index parse fail closed.
            let r = rest.strip_prefix('[')?;
            let close = r.find(']')?;
            let n = r[..close].trim();
            // A literal index (`_2[0]`) is the common case; a *local* index
            // (`(*_1)[_2]`) is what a slice read with a symbolic subscript lowers
            // to. Both are carried, because a contract may write `xs[i]` and the
            // two must name the same element.
            place.proj.push(match n.parse::<u64>() {
                Ok(k) => Proj::Index(k),
                Err(_) => Proj::IndexVar(parse_local(n)?),
            });
            rest = r.get(close + 1..)?;
        }
    }
    Some(place)
}

/// Parse a constant like `0_u32`, `true`, `255_u32`, `()`.
fn parse_const(s: &str) -> Const {
    let t = s.trim();
    if t == "true" {
        return Const::Bool(true);
    }
    if t == "false" {
        return Const::Bool(false);
    }
    if t == "()" {
        return Const::Unit;
    }
    // `<digits>_<ty>` — the suffix is the type, not part of the number.
    if let Some((num, ty)) = t.rsplit_once('_') {
        let ty = Ty::parse(ty);
        let digits = num.replace('_', "");
        if let Ok(v) = digits.parse::<u128>() {
            return Const::UInt(v, Some(ty));
        }
        // A *negative* literal, as in `const -1_i16`. The dump prints it with a
        // sign, which `u128` will not take, so it is read as a magnitude and
        // stored as the two's-complement bit pattern at the type's width. This is
        // the value the machine actually compares against; refusing it would leave
        // `b == -1` unknown and hide the `MIN / -1` overflow behind an
        // unmodelled condition.
        if let Some(mag) = digits.strip_prefix('-') {
            if let (Ok(mag), Some(w)) = (mag.parse::<u128>(), ty.width()) {
                if w < 128 {
                    let mask = (1u128 << w) - 1;
                    return Const::UInt((0u128.wrapping_sub(mag)) & mask, Some(ty));
                }
            }
        }
    }
    if let Ok(v) = t.parse::<u128>() {
        return Const::UInt(v, None);
    }
    // Associated constants. rustc prints these two ways: the long form
    // `core::num::<impl u16>::MAX`, and the short `i8::MIN` when the type is a
    // primitive. Both name an integer bound, and the value is recovered from the
    // type rather than guessed. Only the standard integer types are recognized;
    // anything else stays `Other` and becomes unknown downstream.
    if let Some((prefix, name)) = t.rsplit_once("::") {
        if name == "MAX" || name == "MIN" {
            let ty = type_in_impl_path(t).or_else(|| {
                let p = Ty::parse(prefix);
                if p.width().is_some() {
                    Some(p)
                } else {
                    None
                }
            });
            if let Some(ty) = ty {
                if let Some(w) = ty.width() {
                    // `MAX` is `2^(w-1) - 1` for a signed type and `2^w - 1` for
                    // an unsigned one. `MIN` is the *most negative* value for a
                    // signed type, whose bit pattern is the top bit alone, and
                    // zero for an unsigned one. Returning zero for both used to
                    // make `a != i8::MIN` mean `a != 0`, so the assert guarding a
                    // signed negation looked dischargeable and the negation was
                    // reported panic-free.
                    let v = match (name, ty.is_signed()) {
                        ("MAX", true) => (1u128 << (w - 1)) - 1,
                        ("MAX", false) => {
                            if w == 64 {
                                u128::from(u64::MAX)
                            } else {
                                (1u128 << w) - 1
                            }
                        }
                        ("MIN", true) => 1u128 << (w - 1),
                        _ => 0,
                    };
                    return Const::UInt(v, Some(ty));
                }
            }
        }
    }
    Const::Other(t.to_string())
}

/// Pull the type out of `core::num::<impl u16>::MAX`, returning `u16`.
fn type_in_impl_path(s: &str) -> Option<Ty> {
    let start = s.find("<impl ")? + "<impl ".len();
    let rest = &s[start..];
    let end = rest.find('>')?;
    Some(Ty::parse(rest[..end].trim()))
}

/// Parse an operand: `copy _1`, `move _2.0`, `const 3_u32`, or a bare place.
fn parse_operand(s: &str, enums: &BTreeMap<String, EnumLayout>) -> Operand {
    let t = s.trim();
    if let Some(r) = t.strip_prefix("copy ") {
        return Operand::Copy(parse_place(r, enums).unwrap_or(Place::new(u32::MAX)));
    }
    if let Some(r) = t.strip_prefix("move ") {
        return Operand::Move(parse_place(r, enums).unwrap_or(Place::new(u32::MAX)));
    }
    if let Some(r) = t.strip_prefix("const ") {
        return Operand::Const(parse_const(r));
    }
    // A bare place, e.g. inside `switchInt(_1)`.
    match parse_place(t, enums) {
        Some(p) => Operand::Copy(p),
        None => Operand::Const(Const::Other(t.to_string())),
    }
}

// ---------------------------------------------------------------------------
// Function header
// ---------------------------------------------------------------------------

type FnHeader = (String, Vec<(LocalIdx, Ty)>, Ty);

fn parse_fn_header(line: &str) -> Option<FnHeader> {
    let t = line.trim();
    let rest = t.strip_prefix("fn ")?;
    let open = rest.find('(')?;
    let name = rest[..open].trim().to_string();
    let close = matching_paren(rest, open)?;
    let args_text = &rest[open + 1..close];
    let after = rest[close + 1..].trim();
    let ret_ty = match after.strip_prefix("->") {
        Some(r) => Ty::parse(r.trim().trim_end_matches('{').trim()),
        None => Ty::Unit,
    };
    let mut args = Vec::new();
    for a in split_top_level(args_text, ',') {
        // `_1: u32` or `mut _1: u32`
        let a = a.trim().trim_start_matches("mut ").trim();
        if let Some(i) = find_top_level_colon(a) {
            if let Some(idx) = parse_local(&a[..i]) {
                args.push((idx, Ty::parse(&a[i + 1..])));
            }
        }
    }
    Some((name, args, ret_ty))
}

/// Given text positioned *after* an opening `(`, return `(inner, rest)` where
/// `inner` ends at the matching `)` and `rest` is everything after it. Nested
/// brackets are tracked, so a message containing `(…)` does not end the scan.
fn take_until_close(s: &str) -> Option<(&str, &str)> {
    let mut depth = 0i32;
    for (i, ch) in s.char_indices() {
        match ch {
            '(' | '[' | '{' => depth += 1,
            ')' => {
                if depth == 0 {
                    return Some((&s[..i], &s[i + 1..]));
                }
                depth -= 1;
            }
            ']' | '}' => depth -= 1,
            _ => {}
        }
    }
    None
}

fn matching_paren(s: &str, open: usize) -> Option<usize> {
    let mut depth = 0i32;
    for (i, ch) in s.char_indices().skip(open) {
        match ch {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return Some(i);
                }
            }
            _ => {}
        }
    }
    None
}

// ---------------------------------------------------------------------------
// Statement / terminator parsing
// ---------------------------------------------------------------------------

/// Parse the body of an `assert(...)` terminator, given everything after
/// `assert(`.
fn parse_assert(
    rest: &str,
    enums: &BTreeMap<String, EnumLayout>,
) -> Option<(Operand, bool, String, Vec<Operand>, usize)> {
    let (inner, after) = take_until_close(rest)?;
    let parts = split_top_level(inner, ',');
    if parts.is_empty() {
        return None;
    }
    let raw_cond = parts[0].trim();
    let (negated, cond) = match raw_cond.strip_prefix('!') {
        Some(r) => (true, parse_operand(r, enums)),
        None => (false, parse_operand(raw_cond, enums)),
    };
    let mut msg = String::new();
    let mut args = Vec::new();
    if parts.len() > 1 {
        let raw = parts[1].trim();
        msg = unquote(raw);
        for p in &parts[2..] {
            args.push(parse_operand(p, enums));
        }
    }
    let target = parse_success_target(after)?;
    Some((cond, negated, msg, args, target))
}

fn unquote(s: &str) -> String {
    let t = s.trim();
    let inner = t.strip_prefix('"').and_then(|x| x.strip_suffix('"')).unwrap_or(t);
    inner.replace("\\\"", "\"").replace("\\n", "\n")
}

/// Find the `success: bbN` target in `-> [success: bb1, unwind continue]`.
fn parse_success_target(s: &str) -> Option<usize> {
    let i = s.find("success:")?;
    let rest = s[i + "success:".len()..].trim();
    let tok: String = rest.chars().take_while(|c| c.is_alphanumeric() || *c == '_').collect();
    tok.strip_prefix("bb")?.parse().ok()
}

/// `[return: bb1, unwind continue]`
fn parse_return_target(s: &str) -> Option<usize> {
    let i = s.find("return:")?;
    let rest = s[i + "return:".len()..].trim();
    let tok: String = rest.chars().take_while(|c| c.is_alphanumeric() || *c == '_').collect();
    tok.strip_prefix("bb")?.parse().ok()
}

fn parse_bb_ref(s: &str) -> Option<usize> {
    let t = s.trim();
    t.strip_prefix("bb")?.trim().parse().ok()
}

/// Parse an rvalue appearing after `place = `.
fn parse_rvalue(s: &str, enums: &BTreeMap<String, EnumLayout>) -> Rvalue {
    let t = s.trim();
    // A call is handled by the caller (it is a terminator).
    //
    // `copy`/`move` of a place is tried *before* the cast check, because a
    // downcast place contains the word `as`: `copy ((_2 as Some).0: u8)` has an
    // ` as ` inside its parentheses, and matching the cast first would read it as
    // a cast of `copy ((_2` and throw the payload away. A real cast does not
    // parse as a place -- `_1 as u32 (IntToInt)` fails at the ` as ` -- so the
    // place attempt is the discriminator, and the cast check below is the
    // fallback for exactly the strings that fail it.
    if t.starts_with("copy ") || t.starts_with("move ") {
        if let Some(rest) = t.split_once(' ').map(|(_, r)| r) {
            if parse_place(rest, enums).is_some() {
                return Rvalue::Use(parse_operand(t, enums));
            }
        }
    }
    // The cast check has to come *before* the `const ` check, because rustc prints
    // a cast constant as `const 3_i32 as u32 (IntToInt)`. Matching `const ` first
    // hands the whole string to `parse_const`, which reads `i32 as u32 (IntToInt)`
    // as a type name and produces a constant with no width -- an `Unknown` that
    // then makes every guard written against it unmodelled.
    if let Some(i) = t.find(" as ") {
        let (src, dst) = (t[..i].trim(), t[i + 4..].trim());
        let ty_text = dst.split_whitespace().next().unwrap_or(dst);
        return Rvalue::Cast(parse_operand(src, enums), Ty::parse(ty_text));
    }
    if let Some(rest) = t.strip_prefix("const ") {
        return Rvalue::Use(Operand::Const(parse_const(rest)));
    }
    if t.starts_with("copy ") || t.starts_with("move ") {
        return Rvalue::Use(parse_operand(t, enums));
    }
    // `&_1`, `&mut _1`, `&raw const _1`, `&raw mut _1`
    //
    // The raw forms appear for a `&mut [T]` argument's bounds check: rustc
    // materialises the metadata through a raw borrow, `_3 = &raw const (fake)
    // (*_1); _4 = PtrMetadata(move _3)`, where the immutable `&[T]` reads
    // `PtrMetadata(copy _1)` directly. Both name the same place, so both are a
    // `Ref`.
    let raw = t.strip_prefix("&raw const ").or_else(|| t.strip_prefix("&raw mut "));
    if let Some(r) = raw.or_else(|| t.strip_prefix("&mut ")).or_else(|| t.strip_prefix('&')) {
        // `(fake)` is the marker rustc prints on the *place* of a `&mut [T]`
        // argument's metadata borrow; it names the same place as its operand.
        // It is stripped here rather than in `parse_place`, because `strip_annot`
        // would otherwise read the whole `(fake) (*_1)` as an annotated place and
        // strip the outer parentheses, leaving `fake) (*_1`.
        let r = r.strip_prefix("(fake)").map(str::trim_start).unwrap_or(r);
        if let Some(p) = parse_place(r, enums) {
            return Rvalue::Ref(p);
        }
    }
    if let Some(rest) = t.strip_prefix("Len(") {
        if let Some(p) = parse_place(strip_copy(rest.trim_end_matches(')')), enums) {
            return Rvalue::Len(p);
        }
    }
    if let Some(rest) = t.strip_prefix("PtrMetadata(") {
        if let Some(p) = parse_place(strip_copy(rest.trim_end_matches(')')), enums) {
            return Rvalue::PtrMetadata(p);
        }
    }
    if let Some(rest) = t.strip_prefix("discriminant(") {
        if let Some(p) = parse_place(rest.trim_end_matches(')'), enums) {
            return Rvalue::Discriminant(p);
        }
    }
    // A struct literal: `Config { lo: const 7_u8, hi: const 9_u8 }`.
    //
    // This arm is *before* the `Name(args)` arm and guarded on a closing brace,
    // because a struct literal's fields are operands and an operand is a place
    // or a constant -- never a call -- so a `(` inside one would be a shape this
    // frontend does not produce. Matching on the brace keeps the two apart.
    //
    // The fields are printed in declaration order, so their printed *position* is
    // the `Field(N)` index the reads use: `_1.0` is the first operand here. That
    // is what makes a positional store sound -- the order is not a convention
    // this parser is inventing, it is the same order the index projections count
    // in. (rustc does not reorder the fields for layout here; the field indices
    // are declaration indices even when the layout does reorder the bytes.)
    if t.ends_with('}') {
        if let Some(open) = t.find('{') {
            let inner = &t[open + 1..t.len() - 1];
            let mut args = Vec::new();
            for field in split_top_level(inner, ',') {
                let field = field.trim();
                if field.is_empty() {
                    continue;
                }
                // `lo: const 7_u8` -> `const 7_u8`. The name is an identifier,
                // so the first top-level `:` separates it from the value; a `::`
                // inside the value is not that separator.
                let Some((_, val)) = split_field_name(field) else {
                    return Rvalue::Unknown(t.to_string());
                };
                args.push(parse_operand(val, enums));
            }
            return Rvalue::Struct(args);
        }
    }
    // An operator call: `Name(args)`.
    if let Some(open) = t.find('(') {
        if t.ends_with(')') {
            let name = t[..open].trim();
            let inner = &t[open + 1..t.len() - 1];
            let args: Vec<Operand> = split_top_level(inner, ',').iter().map(|a| parse_operand(a, enums)).collect();
            // A tuple/array literal, printed as a bare list.
            if name.is_empty() {
                return Rvalue::Aggregate(args);
            }
            if let Some(op) = BinOp::parse(name) {
                if args.len() == 2 {
                    return Rvalue::Binary(op, args[0].clone(), args[1].clone());
                }
            }
            if let Some(op) = name.strip_prefix('!').and_then(BinOp::parse) {
                if args.len() == 2 {
                    return Rvalue::Binary(op, args[0].clone(), args[1].clone());
                }
            }
            if let Some(base) = name.strip_suffix("WithOverflow") {
                if let Some(op) = BinOp::parse(base) {
                    if args.len() == 2 {
                        return Rvalue::CheckedBinary(op, args[0].clone(), args[1].clone());
                    }
                }
            }
            if name == "Not" && args.len() == 1 {
                return Rvalue::Unary(UnOp::Not, args[0].clone());
            }
            if name == "Neg" && args.len() == 1 {
                return Rvalue::Unary(UnOp::Neg, args[0].clone());
            }
            // An enum variant construction with a payload. The `::` is what
            // separates it from a plain call; the executor resolves the variant
            // against the program's enum layouts, which is the only place the
            // declaration order is known.
            if name.contains("::") && !name.contains(' ') {
                return Rvalue::Variant(name.to_string(), args);
            }
        }
    }
    // An array literal: `[const 1_u32, const 2_u32]`
    if t.starts_with('[') && t.ends_with(']') {
        let inner = &t[1..t.len() - 1];
        let args: Vec<Operand> = split_top_level(inner, ',').iter().map(|a| parse_operand(a, enums)).collect();
        return Rvalue::Aggregate(args);
    }
    // A tuple literal: `(move _5, move _4)`
    if t.starts_with('(') && t.ends_with(')') {
        let inner = &t[1..t.len() - 1];
        if !inner.trim().is_empty() {
            let args: Vec<Operand> =
                split_top_level(inner, ',').iter().map(|a| parse_operand(a, enums)).collect();
            if args.len() > 1 {
                return Rvalue::Aggregate(args);
            }
        }
    }
    // An enum variant *construction*, printed as a bare path: `_1 = Mode::Idle;`.
    // Unlike an integer constant it carries no `const ` prefix, so without this
    // arm it fell through to `Rvalue::Unknown` and the local's tag was never
    // written -- which is why `let m = Mode::Idle; match m` stayed unmodelled
    // even once a tag read from an argument worked. A `::` with no spaces or
    // parens is the shape; the discriminant is resolved by the executor, which
    // is the only place the enum's layout is known.
    if t.contains("::") && !t.contains(' ') && !t.contains('(') {
        return Rvalue::Use(Operand::Const(Const::Other(t.to_string())));
    }
    Rvalue::Unknown(t.to_string())
}
/// Parse one statement or terminator line.
fn parse_stmt_or_term(line: &str, enums: &BTreeMap<String, EnumLayout>) -> Result<Stmt, Term> {
    let t = line.trim().trim_end_matches(';').trim();
    if t.is_empty() || t == "nop" {
        return Ok(Stmt::Nop);
    }
    if let Some(rest) = t.strip_prefix("StorageLive(").or_else(|| t.strip_prefix("StorageDead(")) {
        let _ = rest;
        return Ok(Stmt::Nop);
    }
    // Terminators ----------------------------------------------------------
    if let Some(r) = t.strip_prefix("goto ->") {
        return Err(match parse_bb_ref(r) {
            Some(b) => Term::Goto(b),
            None => Term::Unknown(t.to_string()),
        });
    }
    if t == "return" {
        return Err(Term::Return);
    }
    if t == "unreachable" {
        return Err(Term::Unreachable);
    }
    if let Some(r) = t.strip_prefix("switchInt(") {
        let Some((inner, after)) = take_until_close(r) else {
            return Err(Term::Unknown(t.to_string()));
        };
        let discr = parse_operand(inner, enums);
        let lb = match after.find('[') {
            Some(i) => i,
            None => return Err(Term::Unknown(t.to_string())),
        };
        let rb = match after.rfind(']') {
            Some(i) => i,
            None => return Err(Term::Unknown(t.to_string())),
        };
        let mut cases = Vec::new();
        let mut otherwise = usize::MAX;
        for part in split_top_level(&after[lb + 1..rb], ',') {
            if let Some(v) = part.trim().strip_prefix("otherwise:") {
                otherwise = parse_bb_ref(v).unwrap_or(usize::MAX);
            } else if let Some(i) = find_top_level_colon(&part) {
                if let Ok(k) = part[..i].trim().parse::<u128>() {
                    if let Some(b) = parse_bb_ref(&part[i + 1..]) {
                        cases.push((k, b));
                    }
                }
            }
        }
        if otherwise == usize::MAX {
            return Err(Term::Unknown(t.to_string()));
        }
        return Err(Term::SwitchInt { discr, cases, otherwise });
    }
    if let Some(r) = t.strip_prefix("assert(") {
        return Err(match parse_assert(r, enums) {
            Some((cond, negated, msg, msg_args, target)) => {
                Term::Assert { cond, negated, msg, msg_args, target }
            }
            None => Term::Unknown(t.to_string()),
        });
    }
    // A call terminator: `dest = callee(args) -> [return: bbN, …]`
    if let Some(i) = t.find(" -> [return:") {
        let lhs = t[..i].trim();
        let target = parse_return_target(&t[i..]).unwrap_or(usize::MAX);
        if let Some(eq) = lhs.find(" = ") {
            let dest_text = lhs[..eq].trim();
            let call = lhs[eq + 3..].trim();
            let dest = parse_place(dest_text, enums).unwrap_or(Place::new(u32::MAX));
            if let Some(open) = call.find('(') {
                if call.ends_with(')') {
                    let name = call[..open].trim();
                    let inner = &call[open + 1..call.len() - 1];
                    let args: Vec<Operand> =
                        split_top_level(inner, ',').iter().map(|a| parse_operand(a, enums)).collect();
                    let callee = if name.is_empty() {
                        Callee::Indirect(dest.clone())
                    } else {
                        Callee::Name(name.to_string())
                    };
                    return Err(Term::Call { callee, args, dest, target });
                }
            }
        }
        return Err(Term::Unknown(t.to_string()));
    }
    if let Some(r) = t.strip_prefix("drop(") {
        let _ = r;
        let target = parse_return_target(t).unwrap_or(usize::MAX);
        return Err(Term::Goto(target));
    }
    // A plain assignment ----------------------------------------------------
    if let Some(eq) = find_assign_eq(t) {
        let dest_text = t[..eq].trim();
        let rhs = t[eq + 1..].trim();
        if let Some(place) = parse_place(dest_text, enums) {
            return Ok(Stmt::Assign(place, parse_rvalue(rhs, enums)));
        }
    }
    Ok(Stmt::Unknown(t.to_string()))
}

/// Find the ` = ` that separates destination from rvalue, skipping `==`.
fn find_assign_eq(s: &str) -> Option<usize> {
    let bytes = s.as_bytes();
    let mut depth = 0i32;
    let mut i = 0;
    while i < bytes.len() {
        match bytes[i] {
            b'(' | b'[' => depth += 1,
            b')' | b']' => depth -= 1,
            b'=' if depth == 0 => {
                let prev = if i == 0 { b' ' } else { bytes[i - 1] };
                let next = *bytes.get(i + 1).unwrap_or(&b' ');
                if prev != b'=' && prev != b'!' && prev != b'<' && prev != b'>' && next != b'=' {
                    return Some(i);
                }
            }
            _ => {}
        }
        i += 1;
    }
    None
}

// ---------------------------------------------------------------------------
// Program parsing
// ---------------------------------------------------------------------------

/// Parse a whole MIR dump.
pub fn parse_program(text: &str) -> MirProgram {
    parse_program_with(text, &BTreeMap::new())
}

/// [`parse_program`] with the enum layouts from the source.
///
/// A `match` lowers to `(base as Variant)` downcasts whose *variant names* the
/// MIR dump prints and whose *discriminants* it does not. Resolving a name to its
/// index needs the declaration order, which lives in the source rather than the
/// dump, so it is passed in. An empty map is the old behaviour: `Option`/`Result`
/// resolve from their built-in numbering and every other enum refuses a downcast.
pub fn parse_program_with(text: &str, enums: &BTreeMap<String, EnumLayout>) -> MirProgram {
    let lines: Vec<&str> = text.lines().collect();
    let mut prog = MirProgram { enums: enums.clone(), ..MirProgram::default() };
    let mut i = 0;
    while i < lines.len() {
        let line = lines[i];
        // rustc prints a second, `// MIR FOR CTFE`-marked body for an item it
        // const-evaluates -- a tuple-variant constructor called in a `let`, for
        // one. It is a *copy* of an item already printed above it, and the typed
        // MIR has one body per item, so parsing it as well would count the
        // function twice and leave `MirProgram::get` with two candidates for one
        // name. The marker names the copy, so it is skipped together with its
        // body.
        if line.trim() == "// MIR FOR CTFE" {
            let mut k = i + 1;
            while k < lines.len() && lines[k].trim().is_empty() {
                k += 1;
            }
            if k < lines.len() && parse_fn_header(lines[k]).is_some() {
                let mut m = k + 1;
                while m < lines.len() && !lines[m].starts_with('}') {
                    m += 1;
                }
                i = m + 1;
                continue;
            }
        }
        if let Some((name, args, ret_ty)) = parse_fn_header(line) {
            let mut f = MirFn {
                name,
                arg_locals: args.iter().map(|(l, _)| *l).collect(),
                ret_ty: ret_ty.clone(),
                locals: BTreeMap::new(),
                local_names: BTreeMap::new(),
                debug_bindings: Vec::new(),
                blocks: Vec::new(),
                written: std::collections::BTreeSet::new(),
            };
            // Local `_0` is the return place, so it carries the return type.
            f.locals.insert(0, ret_ty);
            for (l, t) in &args {
                f.locals.insert(*l, t.clone());
            }
            // Body runs until the closing brace in column 0.
            let mut j = i + 1;
            let mut cur_block: Option<Block> = None;
            while j < lines.len() {
                let l = lines[j];
                if l.starts_with('}') {
                    if let Some(b) = cur_block.take() {
                        f.blocks.push(b);
                    }
                    break;
                }
                let t = l.trim();
                // Locals and debug names, wherever they appear (scope blocks too).
                if let Some(rest) = t.strip_prefix("let ") {
                    let rest = rest.trim_start_matches("mut ").trim();
                    if let Some(c) = find_top_level_colon(rest) {
                        if let Some(idx) = parse_local(&rest[..c]) {
                            f.locals.insert(idx, Ty::parse(rest[c + 1..].trim().trim_end_matches(';')));
                        }
                    }
                    j += 1;
                    continue;
                }
                if let Some(rest) = t.strip_prefix("debug ") {
                    if let Some((n, p)) = rest.split_once("=>") {
                        let name = n.trim().to_string();
                        let target = p.trim().trim_end_matches(';');
                        // Recorded before the local check, so a binding to a
                        // constant is visible as a shadowing. `let k = i; let k =
                        // 0;` prints `debug k => _2;` then `debug k => const
                        // 0_usize;`, and dropping the second (as keeping only
                        // local targets would) leaves the stale `_2` looking like
                        // the only binding, so a contract's `k` would be checked
                        // against `i` while the body used the constant.
                        f.debug_bindings.push((name.clone(), parse_local(target)));
                        if let Some(idx) = parse_local(target) {
                            // First binding wins, and it must. A `debug` line at
                            // function level names the *parameter*; a later one
                            // inside a `scope` block names whatever value has
                            // since moved into that local (`let s = a;` prints
                            // `debug s => _1;` inside `scope 1`). Overwriting
                            // with the scoped alias renames the parameter, so a
                            // contract that says `requires: a <= 127` would look
                            // up `a`, find only `s`, and be skipped as unreadable
                            // -- the function would go unverified because a
                            // local borrowed the parameter's slot.
                            f.local_names.entry(idx).or_insert_with(|| name.clone());
                        }
                    }
                    j += 1;
                    continue;
                }
                if t.starts_with("scope ") || t == "{" {
                    j += 1;
                    continue;
                }
                // A block header: `bbN: {`
                if let Some(rest) = t.strip_prefix("bb") {
                    if let Some(colon) = rest.find(':') {
                        if let Ok(id) = rest[..colon].trim().parse::<usize>() {
                            if let Some(b) = cur_block.take() {
                                f.blocks.push(b);
                            }
                            cur_block = Some(Block { id, stmts: Vec::new(), term: Term::Unknown("missing".into()) });
                            j += 1;
                            continue;
                        }
                    }
                }
                if t == "}" {
                    if let Some(b) = cur_block.take() {
                        f.blocks.push(b);
                    }
                    j += 1;
                    continue;
                }
                if t.is_empty() || t.starts_with("//") {
                    j += 1;
                    continue;
                }
                // A statement or terminator.
                if let Some(b) = cur_block.as_mut() {
                    match parse_stmt_or_term(t, enums) {
                        Ok(s) => b.stmts.push(s),
                        Err(term) => {
                            b.term = term;
                            let done = b.clone();
                            f.blocks.push(done);
                            cur_block = None;
                        }
                    }
                }
                j += 1;
            }
            // Keep the locals map from losing the return slot's real type.
            //
            // Every local the body assigns is recorded, so `alias_locals` can
            // refuse to alias an argument that is reassigned. A `let mut i = …`
            // argument that the body writes is exactly the case where a scoped
            // `debug k => _2;` stops being an alias, so this is collected from the
            // parsed blocks rather than from the text: the parser is the only
            // thing that knows which lines were statements.
            for b in &f.blocks {
                for s in &b.stmts {
                    if let Stmt::Assign(p, _) = s {
                        f.written.insert(p.local);
                    }
                }
                if let Term::Call { dest, .. } = &b.term {
                    f.written.insert(dest.local);
                }
            }
            prog.fns.push(f);
            i = j + 1;
            continue;
        }
        i += 1;
    }
    prog
}

#[cfg(test)]
mod tests {
    use super::*;

    const DUMP: &str = r#"
fn add(_1: u32, _2: u32) -> u32 {
    debug a => _1;
    debug b => _2;
    let mut _0: u32;
    let mut _3: (u32, bool);

    bb0: {
        _3 = AddWithOverflow(copy _1, copy _2);
        assert(!move (_3.1: bool), "attempt to compute `{} + {}`, which would overflow", copy _1, copy _2) -> [success: bb1, unwind continue];
    }

    bb1: {
        _0 = move (_3.0: u32);
        return;
    }
}
"#;

    #[test]
    fn parses_a_function() {
        let prog = parse_program(DUMP);
        assert_eq!(prog.fns.len(), 1);
        let f = &prog.fns[0];
        assert_eq!(f.name, "add");
        assert_eq!(f.arg_locals, vec![1, 2]);
        assert_eq!(f.ret_ty, Ty::U32);
        assert_eq!(f.name_of(1), "a");
        assert_eq!(f.blocks.len(), 2);
    }

    /// A `// MIR FOR CTFE` body is a copy, and must not be parsed as a second
    /// function.
    ///
    /// rustc prints one for an item it const-evaluates -- a tuple-variant
    /// constructor called in a `let`, for one. The typed MIR has one body per
    /// item, so counting the copy makes the text side disagree with the oracle
    /// over a function that is really there once.
    #[test]
    fn a_ctfe_copy_is_not_a_second_function() {
        let dump = format!(
            "{DUMP}
// MIR FOR CTFE
{DUMP}"
        );
        let prog = parse_program(&dump);
        assert_eq!(prog.fns.len(), 1, "the CTFE copy is the same function, not a second one");
    }

    #[test]
    fn keeps_the_negation_on_an_assert() {
        // rustc prints overflow checks as `assert(!bit)`. Losing the `!` would
        // invert every overflow check in the tool.
        let prog = parse_program(DUMP);
        let t = &prog.fns[0].blocks[0].term;
        match t {
            Term::Assert { negated, msg, .. } => {
                assert!(*negated, "the `!` must survive parsing");
                assert!(msg.contains("overflow"), "message was `{msg}`");
            }
            other => panic!("expected an assert, got {other:?}"),
        }
    }

    #[test]
    fn parses_a_checked_binary_into_its_tuple() {
        let prog = parse_program(DUMP);
        let stmts = &prog.fns[0].blocks[0].stmts;
        match stmts.first() {
            Some(Stmt::Assign(place, Rvalue::CheckedBinary(BinOp::Add, _, _))) => {
                assert_eq!(place.local, 3);
            }
            other => panic!("expected a checked add, got {other:?}"),
        }
    }

    #[test]
    fn parses_an_associated_constant() {
        let dump = "fn f(_1: u16) -> u16 {\n    debug a => _1;\n    let mut _0: u16;\n\n    bb0: {\n        _0 = const core::num::<impl u16>::MAX;\n        return;\n    }\n}\n";
        let prog = parse_program(dump);
        let stmts = &prog.fns[0].blocks[0].stmts;
        match stmts.first() {
            Some(Stmt::Assign(_, Rvalue::Use(Operand::Const(Const::UInt(v, Some(Ty::U16)))))) => {
                assert_eq!(*v, 65535);
            }
            other => panic!("expected u16::MAX as a typed constant, got {other:?}"),
        }
    }

    #[test]
    fn parses_a_switch_and_its_otherwise_arm() {
        let dump = "fn f(_1: u32) -> u32 {\n    debug x => _1;\n    let mut _0: u32;\n\n    bb0: {\n        switchInt(copy _1) -> [0: bb2, 1: bb1, otherwise: bb3];\n    }\n\n    bb1: {\n        _0 = const 1_u32;\n        return;\n    }\n\n    bb2: {\n        _0 = const 0_u32;\n        return;\n    }\n\n    bb3: {\n        _0 = copy _1;\n        return;\n    }\n}\n";
        let prog = parse_program(dump);
        match &prog.fns[0].blocks[0].term {
            Term::SwitchInt { cases, otherwise, .. } => {
                assert_eq!(cases.len(), 2);
                assert_eq!(*otherwise, 3);
            }
            other => panic!("expected a switchInt, got {other:?}"),
        }
    }

    #[test]
    fn parses_a_call_with_its_target() {
        let dump = "fn f(_1: u32) -> u32 {\n    debug a => _1;\n    let mut _0: u32;\n\n    bb0: {\n        _0 = double(copy _1) -> [return: bb1, unwind continue];\n    }\n\n    bb1: {\n        return;\n    }\n}\n";
        let prog = parse_program(dump);
        match &prog.fns[0].blocks[0].term {
            Term::Call { callee, args, dest, target } => {
                assert_eq!(*callee, Callee::Name("double".to_string()));
                assert_eq!(args.len(), 1);
                assert_eq!(dest.local, 0);
                assert_eq!(*target, 1);
            }
            other => panic!("expected a call, got {other:?}"),
        }
    }

    #[test]
    fn an_unrecognized_line_becomes_unknown_not_a_guess() {
        // The parser must fail closed. A line it does not understand is
        // `Unknown`, which the executor turns into "path not modelled", never
        // into a proof.
        let dump = "fn f(_1: u32) -> u32 {\n    debug a => _1;\n    let mut _0: u32;\n\n    bb0: {\n        _0 = SomeFutureRvalue(copy _1);\n        return;\n    }\n}\n";
        let prog = parse_program(dump);
        match &prog.fns[0].blocks[0].stmts.first() {
            Some(Stmt::Assign(_, Rvalue::Unknown(_))) => {}
            other => panic!("expected an unknown rvalue, got {other:?}"),
        }
    }

    /// A scoped `debug` alias of an unwritten argument is resolvable by name.
    ///
    /// This is the whole `let k = i; a[k]` case, and it is a parser-level rule:
    /// the alias has to be collected even though `local_names` refuses to keep it
    /// (keeping it would rename `i`), and it must be withheld the moment the body
    /// writes the argument it aliases.
    #[test]
    fn a_scoped_debug_name_aliases_an_unwritten_argument() {
        let dump = "fn f(_1: [u8; 4], _2: usize) -> u8 {\n    debug a => _1;\n    debug i => _2;\n    let mut _0: u8;\n    let mut _3: bool;\n    scope 1 {\n        debug k => _2;\n    }\n\n    bb0: {\n        _3 = Lt(copy _2, const 4_usize);\n        assert(move _3, \"index out of bounds\", const 4_usize, copy _2) -> [success: bb1, unwind continue];\n    }\n\n    bb1: {\n        _0 = copy _1[_2];\n        return;\n    }\n}\n";
        let prog = parse_program(dump);
        let f = &prog.fns[0];
        // `i` is still the argument's name; the alias did not take it over.
        assert_eq!(f.name_of(2), "i");
        let aliases = f.alias_locals();
        assert_eq!(aliases.get("k"), Some(&2), "`k` must alias the argument `_2`");
        assert_eq!(aliases.get("i"), None, "an argument's own name is not an alias");
        assert!(!f.written.contains(&2), "`_2` is never assigned in this body");
    }

    /// The alias is withheld when the argument it names is written.
    ///
    /// `debug k => _2;` with a later `_2 = …` means `k` and `_2` diverge, so the
    /// name must not resolve. This is the soundness gate, asserted directly so a
    /// refactor cannot drop the `written` check unnoticed.
    #[test]
    fn an_alias_of_a_written_argument_is_withheld() {
        let dump = "fn f(_1: [u8; 4], _2: usize) -> u8 {\n    debug a => _1;\n    debug i => _2;\n    let mut _0: u8;\n    let _3: usize;\n    let mut _4: bool;\n    scope 1 {\n        debug k => _3;\n    }\n\n    bb0: {\n        _3 = copy _2;\n        _2 = const 2_usize;\n        _4 = Lt(copy _3, const 4_usize);\n        assert(move _4, \"index out of bounds\", const 4_usize, copy _3) -> [success: bb1, unwind continue];\n    }\n\n    bb1: {\n        _0 = copy _1[_3];\n        return;\n    }\n}\n";
        let prog = parse_program(dump);
        let f = &prog.fns[0];
        // `_3` is not an argument, so `k` is not an argument alias at all.
        assert_eq!(f.alias_locals().get("k"), None);
        assert!(f.written.contains(&2), "`_2` is assigned, and that is what matters");
    }

    /// A scoped `debug` name that points straight at a *written* argument is
    /// withheld too.
    ///
    /// rustc does not print this shape — it materialises a local for the copy —
    /// but the rule has to hold on the dump alone, not on the assumption that
    /// rustc will keep printing what it prints today. `debug k => _2;` beside a
    /// `_2 = …` is exactly the case where resolving `k` to the argument would
    /// follow a reassignment, so the name must not resolve.
    #[test]
    fn an_alias_of_a_written_argument_is_withheld_even_when_it_names_the_argument() {
        let dump = "fn f(_1: [u8; 4], _2: usize) -> u8 {\n    debug a => _1;\n    debug i => _2;\n    let mut _0: u8;\n    let mut _3: bool;\n    scope 1 {\n        debug k => _2;\n    }\n\n    bb0: {\n        _2 = const 2_usize;\n        _3 = Lt(copy _2, const 4_usize);\n        assert(move _3, \"index out of bounds\", const 4_usize, copy _2) -> [success: bb1, unwind continue];\n    }\n\n    bb1: {\n        _0 = copy _1[_2];\n        return;\n    }\n}\n";
        let prog = parse_program(dump);
        let f = &prog.fns[0];
        assert!(f.written.contains(&2));
        assert_eq!(
            f.alias_locals().get("k"),
            None,
            "`k` aliases `_2`, which the body writes, so it must not resolve"
        );
    }

    fn layout(variants: &[(&str, u64)]) -> BTreeMap<String, EnumLayout> {
        let mut m = BTreeMap::new();
        m.insert(
            "E".to_string(),
            EnumLayout { variants: variants.iter().map(|(n, d)| (n.to_string(), *d)).collect() },
        );
        m
    }

    /// An explicit discriminant is the variant's tag, not its position.
    #[test]
    fn a_variant_after_an_explicit_discriminant_keeps_its_value() {
        let enums = layout(&[("A", 0), ("B", 3), ("C", 4)]);
        assert_eq!(variant_index("E::C", &enums), Some(4));
        assert_eq!(variant_index("E::B", &enums), Some(3));
        assert_eq!(variant_index("E::A", &enums), Some(0));
    }

    /// A declared layout wins over the built-in `Option`/`Result` numbering.
    ///
    /// A user enum with a variant named `None` or `Some` is not `Option`; taking
    /// the built-in tag for a qualified name would select the wrong arm.
    #[test]
    fn a_declared_variant_shadows_the_option_default() {
        let enums = layout(&[("None", 0), ("Some", 5)]);
        assert_eq!(variant_index("E::Some", &enums), Some(5));
        // An *unqualified* `Some` still resolves to the built-in numbering, since
        // it names no enum.
        assert_eq!(variant_index("Some", &enums), Some(1));
    }

    /// A qualified name whose enum is unknown is refused, not answered by another
    /// layout that happens to share the variant name.
    #[test]
    fn an_unknown_qualifier_is_refused() {
        let enums = layout(&[("A", 0), ("B", 3), ("C", 4)]);
        assert_eq!(variant_index("Other::C", &enums), None);
    }

    /// The `&raw const (fake) (*_1)` reborrow a `&mut [T]` bounds check lowers to
    /// is a `Ref` on the place it names, not an unknown.
    ///
    /// The immutable `&[T]` form reads `PtrMetadata(copy _1)` directly, so the
    /// raw form only ever appears for a `&mut` slice argument. The `(fake)` marker
    /// is not a projection -- it names the same place as its operand -- so the
    /// parsed place must be the deref of `_1` and nothing else. Before this arm
    /// the whole rvalue was `Unknown`, which made the slice's length unknown and
    /// left the bounds check unmodelled.
    #[test]
    fn a_raw_fake_reborrow_parses_as_a_reference() {
        let enums = BTreeMap::new();
        let rv = parse_rvalue("&raw const (fake) (*_1)", &enums);
        let Rvalue::Ref(place) = rv else { panic!("expected a Ref, got {rv:?}") };
        assert_eq!(place, Place { local: 1, proj: vec![Proj::Deref] });
        // The `&raw mut` spelling is the same shape.
        let rv = parse_rvalue("&raw mut (fake) (*_2)", &enums);
        let Rvalue::Ref(place) = rv else { panic!("expected a Ref, got {rv:?}") };
        assert_eq!(place, Place { local: 2, proj: vec![Proj::Deref] });
    }

    /// A *qualified* spelling of `Option`/`Result` resolves to the same numbering
    /// as the unqualified one.
    ///
    /// rustc prints a standard construction with its generic arguments:
    /// `Option::<u8>::Some(9)` is `_1 = Option::<u8>::Some(const 9_u8)`, and the
    /// match's `switchInt` compares the tag against `Option`'s numbering. No
    /// source file declares a layout for `Option`, so before this the qualifier
    /// branch found no layout and refused the construction -- losing the tag and
    /// the payload of a shape the unqualified form handles. The `::<u8>` is part
    /// of the spelling, not the variant, so it is dropped before splitting.
    #[test]
    fn a_qualified_standard_variant_resolves() {
        let enums = layout(&[("A", 0), ("B", 3), ("C", 4)]);
        assert_eq!(variant_index("Option::<u8>::Some", &enums), Some(1));
        assert_eq!(variant_index("Option::<u8>::None", &enums), Some(0));
        assert_eq!(variant_index("Result::<u8, u8>::Ok", &enums), Some(0));
        assert_eq!(variant_index("Result::<u8, u8>::Err", &enums), Some(1));
        // The unqualified spellings still resolve to the same values.
        assert_eq!(variant_index("Some", &enums), Some(1));
        assert_eq!(variant_index("Ok", &enums), Some(0));
    }

    /// A *declared* enum still wins over the standard numbering when the spelling
    /// carries generics, so the qualifier branch cannot mistake a user enum for
    /// `Option`.
    #[test]
    fn a_declared_enum_still_wins_over_the_standard_numbering() {
        let enums = layout(&[("Some", 0), ("None", 5)]);
        assert_eq!(variant_index("E::Some", &enums), Some(0));
    }

    /// A 128-bit type is, or contains, one the engine cannot model, and the guard
    /// must see it through an aggregate: `[u128; 4]` is bound field by field, so
    /// the 128-bit *leaf* is what would reach a width assertion, not the array.
    #[test]
    fn an_unrepresentable_leaf_is_seen_through_an_aggregate() {
        let wide = |t: &Ty| t.has_unrepresentable_leaf();
        assert!(wide(&Ty::U128));
        assert!(wide(&Ty::I128));
        assert!(wide(&Ty::Array(Box::new(Ty::U128), 4)));
        assert!(wide(&Ty::Tuple(vec![Ty::U8, Ty::I128])));
        assert!(wide(&Ty::Ref(Box::new(Ty::U128))));
        assert!(wide(&Ty::Slice(Box::new(Ty::U128))));
        // The ordinary widths are modelled and must *not* trip the guard, or
        // every function would be refused.
        for t in [Ty::Bool, Ty::U8, Ty::U16, Ty::U32, Ty::U64, Ty::Usize, Ty::I64, Ty::Isize] {
            assert!(!wide(&t), "{t:?} is modelled");
        }
        assert!(!wide(&Ty::Array(Box::new(Ty::U64), 8)));
        assert!(!wide(&Ty::Tuple(vec![Ty::U8, Ty::I32])));
        assert!(!wide(&Ty::Other("MyStruct".into())));
    }

    /// The front end is total: no input, however mangled, may panic.
    ///
    /// The parser reads text the crate did not write -- rustc's `-Zunpretty=mir`
    /// output, or anything a caller hands [`parse_program`] directly -- so a panic
    /// on a shape it did not expect is a crash in the caller's process, not a
    /// refusal. The property is "returns, always", and the way to test it is to
    /// feed it inputs that are *nearly* valid: a random token soup reaches few
    /// parser states, but a valid dump with a few characters mutated reaches the
    /// boundary between the states. Deterministic and seeded, so a failure is
    /// reproducible, and cheap enough to sit in the ordinary unit suite.
    ///
    /// It also asserts the reader is a *function*: the same text parses to the same
    /// structure twice. That is what makes the survival above evidence rather than
    /// a coincidence of allocation -- and it keeps the test from passing trivially
    /// if `parse_program` were ever changed to return an empty program for
    /// everything.
    #[test]
    fn no_input_panics_the_reader() {
        let seeds: [&str; 2] = [
            DUMP,
            "fn f(_1: u8, _2: u8) -> u8 {\n    debug a => _1;\n    let mut _0: u8;\n    \
             bb0: {\n        _0 = copy _1;\n        return;\n    }\n}\n",
        ];
        // Characters the reader reacts to, so a mutation lands on a real boundary
        // rather than in a comment.
        let pool: Vec<char> = "fn(){ }_0123456789:b->u8usizelet mutgoto returncopy move \
                               constdebugx=>;scopeSwitchIntotherwise[],requires:ensures:ret==&&<\
                               truefalseifelseu32.a\n \"'%!|^&/\\*+-"
            .chars()
            .collect();

        // The LCG the rest of the suite uses, so the inputs are reproducible.
        let mut state = 0x1234_5678_9ABC_DEF0u64;
        let mut next = move || {
            state = state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            state
        };

        let mut saw_a_function = false;
        for _ in 0..20_000 {
            let mut b: Vec<char> = seeds[(next() % seeds.len() as u64) as usize].chars().collect();
            for _ in 0..1 + (next() % 12) {
                if b.is_empty() {
                    break;
                }
                let i = (next() as usize) % b.len();
                match next() % 3 {
                    0 => {
                        b.remove(i);
                    }
                    1 => b[i] = pool[(next() as usize) % pool.len()],
                    _ => b.insert(i, pool[(next() as usize) % pool.len()]),
                }
            }
            let text: String = b.into_iter().collect();

            // The claim under test. A panic here is the failure, and the text is in
            // the message so the seed can be recovered.
            let first = std::panic::catch_unwind(|| parse_program(&text))
                .unwrap_or_else(|_| panic!("parse_program panicked on: {text:?}"));
            let second = parse_program(&text);
            assert_eq!(first, second, "parse_program is not a function on: {text:?}");

            // The contract reader reads the same text, so it gets the same
            // treatment. Only the panic property is asserted here; its own unit
            // tests pin what it parses.
            let _ = std::panic::catch_unwind(|| crate::mir::spec::extract(&text))
                .unwrap_or_else(|_| panic!("spec::extract panicked on: {text:?}"));

            saw_a_function |= !first.fns.is_empty();
        }
        // The corpus is meant to produce *some* real programs, not only refusals.
        // Without this the test could pass while the reader stopped recognising
        // anything at all.
        assert!(saw_a_function, "no mutation produced a parsed function");
    }
}

