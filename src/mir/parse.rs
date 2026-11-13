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

use std::collections::{BTreeMap, BTreeSet};

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
    /// A string literal, as the dump prints it (`"zero"`). The contents are
    /// already unescaped, so a message can be reported verbatim. It is a `String`
    /// rather than a `&'static str` because a `no_std` parser may see any dump.
    Str(String),
    /// A *byte*-string literal (`b"\x05zero \xc0\x00"`), as the dump prints it.
    ///
    /// Edition 2024 passes a `panic!` message's `format_args!` template as a byte
    /// string, so the raw bytes are kept and decoded later by
    /// [`decode_format_template`]. Bytes, not a `String`: the template is not text.
    Bytes(Vec<u8>),
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
        /// The call has no normal successor: it returns `!` and always diverges.
        ///
        /// rustc prints such a call as `_3 = core::panicking::panic(...) -> unwind
        /// continue`, with no `[return: bbN]` arm and therefore no `target`. That is
        /// how `panic!`, `assert!`, `unwrap` and an out-of-bounds index lower: the
        /// call is the only way the path ends. It is a *reachable failure*, not a
        /// line the parser failed to understand, and reading it as one dropped the
        /// whole path -- so a function whose safety rested on an `assert!` came back
        /// `Incomplete` and the assert itself was never checked. The executor turns
        /// it into a panic obligation instead.
        diverges: bool,
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
    /// True for a `bbN (cleanup)` block: one that only runs drops and ends in
    /// `resume`. It is not reachable by ordinary control flow; a call reaches it
    /// only through its `unwind`/cleanup edge.
    ///
    /// This is what tells the *cleanup* form of a diverging call apart from an
    /// ordinary call. A diverging call in a function with a live `Drop` local is
    /// printed with its cleanup block as the single successor (`_4 =
    /// core::panicking::panic(…) -> bb4`, with `bb4 (cleanup)`), not with the
    /// `-> unwind continue` arm the parser first recognised -- so without this
    /// marker an `assert!` in any function with a live RAII local was still a
    /// dropped path.
    pub cleanup: bool,
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
    /// The `(line, column)` of the `impl` keyword when this function is a method,
    /// read from its definition name `<impl at FILE:L:C: L:C>::m`. `None` for a
    /// free function. The owner type is not in the dump; it is looked up from
    /// [`MirProgram::impl_owners`] by this location.
    pub impl_loc: Option<(usize, usize)>,
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
    /// Named `const` items, name → the constant the dump printed for them.
    ///
    /// rustc evaluates a `const` item at compile time and prints its *body*
    /// separately (`const K: u8 = const 5_u8;`) while referring to it by name at
    /// the use site (`_0 = const K;`). Inlining the definition here is what lets
    /// the use site fold to a value instead of staying an unreadable
    /// `Const::Other`, which is the difference between a decided contract and a
    /// lost proof. Only constants whose printed body is a *literal* are kept: a
    /// constant built by an expression has its own body with its own locals, and
    /// re-deriving that value is the interpreter's job, not a table lookup.
    pub consts: BTreeMap<String, Const>,
    /// The owner type of each `impl` block, keyed by the 1-based `(line, column)`
    /// of its `impl` keyword -- the same location a method's definition name
    /// `<impl at FILE:L:C: L:C>::m` carries. Empty when the caller had no source
    /// (the MIR-only entry points), in which case a method call whose name is not
    /// an exact match is refused rather than answered from a guessed owner.
    pub impl_owners: BTreeMap<(usize, usize), String>,
    /// The *trait* each `impl` block implements, keyed as [`Self::impl_owners`]
    /// and holding the trait's path as written. Absent for an inherent `impl`.
    ///
    /// The owner alone cannot separate a local `impl From<u8> for u16` from the
    /// standard library's: both have owner `u16` and both answer the same method
    /// tail. The trait path separates them, because the compiler qualifies the
    /// library trait in the call it resolved (`<u16 as std::convert::From<u8>>::from`)
    /// and the local impl's bare `From` is not a suffix of that. See
    /// executor's `resolve_callee`.
    pub impl_traits: BTreeMap<(usize, usize), String>,
    /// The *trait arguments* each `impl` block instantiates, keyed as
    /// [`Self::impl_traits`] and holding them as written (`u8` for
    /// `impl From<u8> for u16`). Absent for an inherent `impl` or a trait with no
    /// arguments.
    ///
    /// The trait path and the owner cannot separate the library's `From<u8> for u16`
    /// from a local `From<Local> for u16`: both have owner `u16` and both answer the
    /// method tail `from`. The instantiation separates them, so a call to one is not
    /// answered from the other's body. See the executor's `resolve_callee`.
    pub impl_trait_args: BTreeMap<(usize, usize), String>,
    /// The traits the crate itself declares, as module-qualified paths (`From` for
    /// a crate-root trait, `m::Trait` for one inside `mod m`). Empty when the
    /// caller had no source.
    ///
    /// rustc prints a trait in a call as its *shortest crate-unique* path, so a
    /// bare `Trait` in a dump names the crate-root trait only when the crate
    /// declares no other trait of that name. Without this set a bare call name
    /// cannot be told apart from an unrelated same-named trait in another module,
    /// and a suffix match would let the wrong `impl` answer -- a false proof. See
    /// the executor's `trait_candidate_admits`.
    pub declared_traits: std::collections::BTreeSet<String>,
    /// The string pieces of each `promoted` constant, keyed by the name a use
    /// site spells (`lit::promoted[0]`).
    ///
    /// Edition 2024 lowers `panic!("literal")` and `panic!("a{}", x)` through
    /// `Arguments::new_const`/`new_v1`, whose first argument is a *promoted*
    /// constant holding an array of `&str` pieces. That body prints as its own
    /// `const NAME::promoted[0]: &[&str; N] = { … }` item, outside any function,
    /// so the executor cannot see it by walking the function's blocks: without
    /// this table the format pieces are unknown and the panic's message cannot be
    /// recovered. Only the literal pieces are kept -- the `&_1` that borrows them
    /// is not a value the message needs.
    pub promoted_strs: BTreeMap<String, Vec<String>>,
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

/// Drop the single closing paren that ends an rvalue's argument list.
///
/// `trim_end_matches(')')` is the wrong tool here: it strips *every* trailing
/// paren, so `Len((*_1))` -- how a compiler before 1.99 prints a slice's length --
/// loses both and leaves the unparseable `(*_1`, which makes the length `Unknown`
/// and the bounds check above `a[i]` unmodelled. One `strip_suffix` keeps the
/// place's own parens, so `(*_1)` survives to `parse_place`.
fn close_paren(s: &str) -> &str {
    s.trim().strip_suffix(')').unwrap_or(s.trim())
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
    let stripped = strip_annot(s).trim();
    // A *nested* place carries its type annotations in the middle:
    // `(((*_1).0: Inner).0: u8)`. `strip_annot` only drops a whole-place `: Ty`, so
    // the inner ones would stop the walk at the first `:`. They are dropped here,
    // keeping the `)` that closes the group they annotate -- dropping that paren
    // too would unbalance the string and lose the rest of the walk.
    let cleaned = strip_mid_annotations(stripped);
    let s = cleaned.trim();
    // `(*_1)` — a pointer dereference. Like the downcast below it can appear as a
    // whole place or as a prefix (`(*_1).0`), so the inner place is parsed and the
    // `Deref` step is pushed before the tail projections. The close paren is the
    // *matching* one, not the first: a nested place nests its parens, so the first
    // `)` may close an inner group rather than this one.
    if s.starts_with("(*") {
        let close = matching_paren(s, 0)?;
        let mut place = parse_place(s.get(2..close)?, enums)?;
        place.proj.push(Proj::Deref);
        return push_projs(place, s.get(close + 1..)?, enums);
    }
    // A parenthesised group: either an enum downcast `(base as Variant)` or a plain
    // grouping of a nested place `((*_1).0)`. Both are a sub-place followed by a
    // tail, so both parse the inner text and append the tail projections. The
    // downcast is distinguished by the ` as ` it must contain.
    if s.starts_with('(') {
        let close = matching_paren(s, 0)?;
        let inner = s.get(1..close)?.trim();
        let mut place = match inner.rsplit_once(" as ") {
            Some((base, variant)) => {
                let mut p = parse_place(base.trim(), enums)?;
                p.proj.push(Proj::Downcast(variant_index(variant.trim(), enums)?));
                p
            }
            None => parse_place(inner, enums)?,
        };
        let _ = &mut place;
        return push_projs(place, s.get(close + 1..)?, enums);
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

/// Drop the *inner* `: Ty` annotations a nested place carries.
///
/// rustc annotates each projection step: `(((*_1).0: Inner).0: u8)`. Only the
/// outermost annotation is a whole-place `: Ty` for `strip_annot`; the inner ones
/// sit *inside* the string and would stop the walk at the first `:`. Each is
/// dropped up to the `)` closing the group it annotates -- and that `)` is kept,
/// because it belongs to the grouping, not to the annotation.
fn strip_mid_annotations(s: &str) -> String {
    let chars: Vec<char> = s.chars().collect();
    let mut out = String::with_capacity(s.len());
    let mut i = 0;
    while i < chars.len() {
        // `::` is a path separator, not an annotation.
        if chars[i] == ':' && chars.get(i + 1) != Some(&':') {
            i += 1;
            let mut depth = 0i32;
            while i < chars.len() {
                match chars[i] {
                    '(' | '[' | '<' => depth += 1,
                    ')' if depth == 0 => break,
                    ')' | ']' | '>' => depth -= 1,
                    _ => {}
                }
                i += 1;
            }
            continue;
        }
        out.push(chars[i]);
        i += 1;
    }
    out
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

/// The `const` names a dump mentions, split by shape and by role.
///
/// rustc prints a crate-level `const`'s use site by its bare name (`const
/// LIMIT`) and a function-local item's by a qualified path (`const f::L`), but it
/// prints both *definitions* the same way (`const LIMIT: u8 = const 10_u8;`), so
/// the definition alone cannot say whether the item is in scope in any given
/// function. The use sites can: a name never written bare anywhere is never in
/// scope bare anywhere, so a bare definition for it is a function-local item (or
/// an unused one) and must not become a program-wide key. Without this a
/// function-local `const L` handed every *other* function a bare `L` to name, and
/// a contract `requires: L == 3` was proved against a name the function could not
/// have written -- the name resolved to another function's local.
///
/// A definition starts the line with the keyword (`const NAME: TYPE`); every other
/// occurrence (`const NAME;`, `const NAME,`, `const NAME)`) is a use. The
/// qualified sets answer a second question the source cannot: a function-local item
/// whose crate-level twin the compiler removed (a `#[cfg]`-disabled `const`) prints
/// its *definition* bare but keeps its *use* qualified (`const owner::K`), so a
/// qualified use with no qualified definition of the same path is that local. A
/// bare definition under such a name must not become a program-wide key, or an
/// unrelated contract could name it and be proved against another function's local
/// -- a false proof.
///
/// Only the *operand* text is scanned. A string literal or a constant-data block
/// can contain the letters `const L` without that being a use -- a
/// `debug s => const "const L";` binding or the `alloc` block that backs the
/// string `"const L"` would otherwise make `L` look bare-used, which hands a
/// function-local `L` a program-wide key and turns a contract that names it into
/// a false proof.
#[derive(Default)]
struct ConstMentions {
    /// Names used bare (`const L`), the tell of a crate-level item's definition.
    bare_uses: std::collections::BTreeSet<String>,
    /// Qualified paths a `const` is *defined* under (`const owner::K: …`).
    qualified_defs: std::collections::BTreeSet<String>,
    /// Qualified paths a `const` is *used* under (`const owner::K;`).
    qualified_uses: std::collections::BTreeSet<String>,
    /// The last `::` segment of every function's name (`owner`, `inner`,
    /// `local_in_method`, `{closure#0}`). A qualified `const` use whose path
    /// prefix is one of these names a function-local item; any other prefix
    /// names a module or an associated item. See [`claimed_bare_const_uses`].
    fn_names: std::collections::BTreeSet<String>,
}

/// The bare names a qualified `const` use claims for a function-local item.
///
/// A function-local `const`'s definition can print *bare* (`const K: u8 = const
/// 3_u8;`) while its use stays qualified (`const owner::K`), which is how a
/// local whose crate-level twin the compiler removed (a `#[cfg]`-disabled item)
/// would take the crate key. But a *qualified* use is not proof of a local: an
/// associated constant uses `Foo::K` while defining `<impl at …>::K`, and a
/// module constant uses `a::K`. Only a use whose path *prefix* is a function --
/// `owner::K`, `Foo::local_in_method::L`, `outer::inner::M` -- names a
/// function-local item. So a qualified use with no qualified definition of the
/// same path claims its bare tail only when that prefix is a function name.
fn claimed_bare_const_uses(mentions: &ConstMentions) -> std::collections::BTreeSet<String> {
    claimed_bare_paths(mentions).into_keys().collect()
}

/// The same as [`claimed_bare_const_uses`], but keeping the full qualified path
/// each bare tail was claimed by.
///
/// A bare definition claimed this way is a function-local item whose definition
/// rustc printed *bare* only because no other local shares its name. Its use site
/// prints the qualified path (`const owner::K`), so the definition is recorded
/// under that path rather than dropped: a contract on the owning function then
/// reads the value, and no *other* function can name it (the bare key is still
/// withheld). Dropping it instead is what left such a contract undecided.
///
/// Two different owners cannot share a tail here: the claim requires a qualified
/// use with no qualified definition, and a local's use is always qualified while
/// a crate-level item's is bare, so the tail names one local.
fn claimed_bare_paths(mentions: &ConstMentions) -> std::collections::BTreeMap<String, String> {
    let mut out = std::collections::BTreeMap::new();
    for path in mentions.qualified_uses.difference(&mentions.qualified_defs) {
        let prefix = path.rsplit_once("::").map_or("", |(p, _)| p);
        let owner = prefix.rsplit("::").next().unwrap_or("");
        if !mentions.fn_names.contains(owner) {
            continue;
        }
        if let Some(tail) = path.rsplit("::").next() {
            out.insert(tail.to_string(), path.clone());
        }
    }
    out
}

fn const_mentions(text: &str) -> ConstMentions {
    const KW: &str = "const ";
    let mut out = ConstMentions::default();
    // An `allocN (…) {` block holds the bytes of a string literal (and other
    // constant data), printed with a gutter and a right-hand column that spells
    // the bytes out as text. Nothing in it is a use site, and it can contain the
    // word `const`, so it is skipped whole.
    let mut in_alloc = false;
    for line in text.lines() {
        if line.trim_start().starts_with("//") {
            continue;
        }
        if in_alloc {
            if line.trim() == "}" {
                in_alloc = false;
            }
            continue;
        }
        if line.trim_start().starts_with("alloc")
            && line.trim_start()["alloc".len()..].starts_with(|c: char| c.is_ascii_digit())
            && line.contains('(')
            && line.trim_end().ends_with('{')
        {
            in_alloc = true;
            continue;
        }
        // A definition starts the line with the keyword (`const K: u8 = …`); a
        // use sits in an operand (`_0 = const K;`). Only the role of a qualified
        // mention depends on this; the bare-use set reads uses only.
        let is_def = line.trim_start().starts_with(KW);
        // Every function prints its header at the left margin: `fn owner(…)`,
        // `fn <impl at …>::method(…)`, `fn outer::inner(…)`,
        // `fn local_in_closure::{closure#0}(…)`. The last `::` segment is the
        // item's own name, which is the prefix a function-local `const` use
        // carries. The header of a non-function item never begins `fn `, and an
        // operand never sits at the left margin, so this reads only headers.
        if let Some(rest) = line.strip_prefix("fn ") {
            if let Some(head) = rest.split_once('(').map(|(h, _)| h) {
                let name = head.rsplit("::").next().unwrap_or("").trim();
                if !name.is_empty() {
                    out.fn_names.insert(name.to_string());
                }
            }
        }
        // Drop string literals before scanning, so a `const` inside one is not
        // read as a use. A `"` toggles in/out of a literal; a `\` escapes the next
        // character, so `\"` does not close it.
        let mut operand = String::with_capacity(line.len());
        let mut in_str = false;
        let mut escaped = false;
        for c in line.chars() {
            if in_str {
                if escaped {
                    escaped = false;
                } else if c == '\\' {
                    escaped = true;
                } else if c == '"' {
                    in_str = false;
                }
                continue;
            }
            if c == '"' {
                in_str = true;
                continue;
            }
            operand.push(c);
        }
        let mut rest = operand.as_str();
        while let Some(i) = rest.find(KW) {
            let after = &rest[i + KW.len()..];
            // The name is a `::`-separated path; the raw run stops at the first
            // character that cannot be part of one. A trailing `:` is the
            // name/type separator of a definition, not part of the name.
            let raw: String = after
                .chars()
                .take_while(|c| c.is_ascii_alphanumeric() || *c == '_' || *c == ':')
                .collect();
            let name = raw.trim_end_matches(':');
            let plain = name.chars().next().is_some_and(|c| c.is_ascii_alphabetic() || c == '_');
            if plain {
                if name.contains("::") {
                    if is_def {
                        out.qualified_defs.insert(name.to_string());
                    } else {
                        out.qualified_uses.insert(name.to_string());
                    }
                } else if raw == name {
                    // No `:` after the name: a use, not a definition.
                    out.bare_uses.insert(name.to_string());
                }
            }
            rest = after;
        }
    }
    out
}

/// Read the value of a `const` whose body rustc printed as a CTFE brace-block.
///
/// On rustc 1.85 (the MSRV floor) a constant that folds to a literal is printed
/// with its const-evaluated body rather than the inline literal the current
/// stable prints:
///
/// ```text
/// const K: u8 = {
///     let mut _0: u8;
///
///     bb0: {
///         _0 = const 7_u8;
///         return;
///     }
/// }
/// ```
///
/// `lines` is the block's body (everything after the `const … = {` line). The
/// value is the assignment to the return place `_0`, and it is returned only when
/// that assignment is itself a `const` literal -- a block that computes its value
/// (an `AddWithOverflow`, say) has no single literal to fold, and the caller
/// drops the item exactly as before.
///
/// **The block must be a single straight-line basic block.** A `const` whose value
/// is chosen by a branch is printed with one `_0` assignment per arm, and the first
/// one in textual order is *not* the value the constant has:
///
/// ```text
/// const K: u8 = if false { 7 } else { 8 };   // K is 8
/// // bb1: { _0 = const 7_u8; goto -> bb3; }
/// // bb2: { _0 = const 8_u8; goto -> bb3; }
/// ```
///
/// Reading the first arm would store `K = 7` and certify `ensures: ret == 7` for a
/// function that returns `8` -- a false proof. So folding is refused unless the
/// body has exactly one `_0` assignment, that assignment is a literal, the body
/// contains no branch (`switchInt`, `goto`, call-with-target, `unwind`, …), and the
/// literal is followed by `return`. Anything else is left unmodelled, which makes a
/// contract that names the constant *unreadable* -- a skip, never a false proof.
fn block_const_value<'a>(lines: &[&'a str]) -> Option<&'a str> {
    let mut body: Vec<&str> = Vec::new();
    for line in lines {
        if line.starts_with('}') {
            break;
        }
        body.push(line);
    }
    // Exactly one assignment to the return place, and it must be a literal: a
    // second assignment is a second arm, and the first is not the value.
    let mut assignments = body.iter().enumerate().filter(|(_, l)| l.trim().starts_with("_0 ="));
    let (assign_at, assign) = assignments.next()?;
    if assignments.next().is_some() {
        return None;
    }
    let literal = assign.trim().strip_prefix("_0 = const ")?;
    // No branch anywhere in the body, or an arm other than this one could return.
    for l in &body {
        let t = l.trim();
        if t.contains("switchInt(")
            || t.contains("goto ->")
            || t.contains("-> [")
            || t.contains("unwind")
            || t.contains("resume")
            || t.contains("abort")
        {
            return None;
        }
    }
    // The literal's block must return, so the value is the one that leaves. The
    // only lines allowed between are storage bookkeeping.
    let ret = body[assign_at + 1..].iter().find(|l| {
        let t = l.trim();
        !t.is_empty() && !t.starts_with("StorageLive(") && !t.starts_with("StorageDead(")
    })?;
    if ret.trim() != "return;" {
        return None;
    }
    Some(literal.trim_end_matches(';'))
}

/// Split a `const` item's definition line into its name, optional declared type,
/// and body text.
///
/// The line is `const NAME: TYPE = BODY;` or `const NAME = BODY;`. The
/// name/type split is at the `": "` separator, not any colon -- a qualified name
/// (`ARR::{constant#0}`) contains `::` -- and the name/body split is at the first
/// `" = "`. The associated-constant form is dropped: its `{constant#0}` name is
/// not an identifier path, nothing refers to it by that name, and the array
/// length it carries is already in the array's type. `None` is returned for a
/// non-item line or a name that is not a plain `::`-path of identifiers.
fn parse_const_item(line: &str) -> Option<(String, Option<Ty>, &str)> {
    let rest = line.trim_end().strip_prefix("const ")?;
    if rest.starts_with('{') {
        return None;
    }
    let (name, body) = rest.split_once(" = ")?;
    let (name, ty_text) = match name.split_once(": ") {
        Some((n, t)) => (n, Some(t)),
        None => (name, None),
    };
    let name = name.trim();
    let plain = !name.is_empty()
        && !name.contains('{')
        && name
            .split("::")
            .all(|seg| !seg.is_empty() && seg.chars().all(|c| c.is_ascii_alphanumeric() || c == '_'));
    if !plain {
        return None;
    }
    let ret_ty = ty_text.map(|t| Ty::parse(t.trim()));
    Some((name.to_string(), ret_ty, body.trim().trim_end_matches(';')))
}

/// The `prog.consts` key a `const` definition is recorded under, or `None` when
/// its names are not in scope for any contract.
///
/// A bare key is recorded when the name is used bare somewhere (a crate-level
/// item), or when the source says the item is module-scoped (a crate-level
/// constant that only a contract names has no use site to go by). A
/// function-local item's definition prints the same way but its uses are
/// qualified (`const f::L`), so a bare key for it would let an unrelated
/// function's contract resolve a name its own source could not. Such a bare
/// definition is instead recorded under the qualified path the use site spells,
/// so the owning function's contract reads the value while no other function can
/// name the bare key. A qualified definition keeps its qualified key, which is
/// what a contract that spells the path resolves.
fn const_key(
    name: &str,
    claimed_bare: &std::collections::BTreeSet<String>,
    claimed_paths: &BTreeMap<String, String>,
    bare_uses: &std::collections::BTreeSet<String>,
    crate_consts: &std::collections::BTreeSet<String>,
) -> Option<String> {
    if name.contains("::") {
        return Some(name.to_string());
    }
    if claimed_bare.contains(name) {
        return claimed_paths.get(name).cloned();
    }
    if bare_uses.contains(name) || crate_consts.contains(name) {
        return Some(name.to_string());
    }
    None
}

/// A concrete value read by [`fold_const_block`].
///
/// Deliberately *not* the symbolic `Val`: a `const` item's body is const-evaluated
/// by rustc, so every operand is a literal and the whole block is a concrete
/// computation. Folding it with the symbolic engine would be circular -- the
/// symbolic engine's `const` table is what this feeds -- so it is a small,
/// separate interpreter over the parsed blocks. A width and a signedness travel
/// with a word because a cast and a comparison both need them, and a value that
/// forgot its sign would read `-1i8` as `255`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CVal {
    /// A bit-vector: the value, its width, and whether its type is signed.
    Word(u64, u8, bool),
    Bool(bool),
}

impl CVal {
    fn width(self) -> u8 {
        match self {
            CVal::Word(_, w, _) => w,
            CVal::Bool(_) => 1,
        }
    }

    fn word(self) -> Option<u64> {
        match self {
            CVal::Word(v, _, _) => Some(v),
            CVal::Bool(b) => Some(b as u64),
        }
    }

    fn signed(self) -> bool {
        matches!(self, CVal::Word(_, _, true))
    }

    /// A condition's truth: a `bool` is itself, a bit-vector is non-zero -- the
    /// same reading the executor gives an assert condition.
    fn as_bool(self) -> Option<bool> {
        match self {
            CVal::Bool(b) => Some(b),
            CVal::Word(v, _, _) => Some(v != 0),
        }
    }
}

/// The all-ones mask for a width.
fn c_mask(w: u8) -> u64 {
    if w >= 64 { u64::MAX } else { (1u64 << w) - 1 }
}

/// Whether a width is one the folder's 64-bit `CVal` can hold.
///
/// A 128-bit literal (`const HUGE: i128 = 1 + 2`) reaches the folder as an
/// `AddWithOverflow` whose width is 128, and the exact overflow test negates
/// `1i128 << 127`, i.e. `i128::MIN` -- a panic in a debug build, at *parse* time
/// and for an item no selected function even names. The 64-bit word cannot carry
/// such a value, so the folder refuses it: the item stays unmodelled and a
/// contract that named it is a skip, never a crash and never a wrong fold.
fn c_width_ok(w: u8) -> bool {
    w <= 64
}

/// The signed reading of a `w`-bit pattern, sign-extended to `i128`.
fn c_signed(v: u64, w: u8) -> i128 {
    if w >= 64 {
        v as i64 as i128
    } else {
        let sh = 64 - w;
        (((v << sh) as i64) >> sh) as i128
    }
}

/// The value of a `Const` at a known width, when it is a literal or a path to an
/// item already folded.
///
/// A const body refers to another item by path (`const LIMIT` in `LIMIT + 1`),
/// and that item is printed *before* this one, so it is already in `consts`. A
/// path that is not there -- a `const` this pass has not folded, an associated
/// constant, an enum variant construction -- is refused, which leaves the item
/// unmodelled.
fn cval_of_const(c: &Const, want: Option<u8>, consts: &BTreeMap<String, Const>) -> Option<CVal> {
    match c {
        Const::Bool(b) => Some(CVal::Bool(*b)),
        Const::UInt(v, ty) => {
            let w = ty.as_ref().and_then(|t| t.width()).or(want)?;
            // A 128-bit literal is wider than the folder's word; see
            // [`c_width_ok`].
            if !c_width_ok(w) {
                return None;
            }
            let signed = ty.as_ref().is_some_and(|t| t.is_signed());
            if w == 1 {
                return Some(CVal::Bool(*v != 0));
            }
            Some(CVal::Word((*v as u64) & c_mask(w), w, signed))
        }
        Const::Other(name) => cval_of_const(consts.get(name)?, want, consts),
        // `()` is not a literal this folder can take, and a string has no word.
        Const::Unit | Const::Str(_) | Const::Bytes(_) => None,
    }
}

/// The field-index chain of a place, when every projection is a tuple/struct
/// field. A deref, a subscript or a downcast has no key in the folder's store, so
/// it is refused rather than read from the wrong slot.
fn c_field_chain(proj: &[Proj]) -> Option<Vec<u32>> {
    let mut out = Vec::with_capacity(proj.len());
    for p in proj {
        match p {
            Proj::Field(k) => out.push(*k),
            _ => return None,
        }
    }
    Some(out)
}

/// A tuple component's type, for the `(T, bool)` a checked op yields.
fn c_component_ty(ty: &Ty, field: u32) -> Option<Ty> {
    match ty {
        Ty::Tuple(ts) => ts.get(field as usize).cloned(),
        _ => None,
    }
}

/// The type of a place, walking its projections from the local's declared type.
fn c_place_ty(f: &MirFn, p: &Place) -> Option<Ty> {
    let mut ty = f.ty_of(p.local)?.clone();
    for pr in &p.proj {
        ty = match pr {
            Proj::Field(k) => c_component_ty(&ty, *k)?,
            Proj::Index(_) => match &ty {
                Ty::Array(e, _) => (**e).clone(),
                _ => return None,
            },
            _ => return None,
        };
    }
    Some(ty)
}

/// Read an operand from the folder's store.
fn c_operand(
    env: &BTreeMap<(u32, Vec<u32>), CVal>,
    consts: &BTreeMap<String, Const>,
    o: &Operand,
    want: Option<u8>,
) -> Option<CVal> {
    match o {
        Operand::Const(c) => cval_of_const(c, want, consts),
        Operand::Copy(p) | Operand::Move(p) => {
            let chain = c_field_chain(&p.proj)?;
            env.get(&(p.local, chain)).copied()
        }
    }
}

/// A binary op on two concrete values, at `w` bits with the given signedness.
fn c_binop(op: BinOp, a: CVal, b: CVal, w: u8, signed: bool) -> Option<CVal> {
    use core::cmp::Ordering;
    if !c_width_ok(w) {
        return None;
    }
    let m = c_mask(w);
    match op {
        BinOp::Eq => Some(CVal::Bool(a.word()? == b.word()?)),
        BinOp::Ne => Some(CVal::Bool(a.word()? != b.word()?)),
        BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
            let (x, y) = (a.word()?, b.word()?);
            let ord = if signed { c_signed(x, w).cmp(&c_signed(y, w)) } else { x.cmp(&y) };
            Some(CVal::Bool(match op {
                BinOp::Lt => ord == Ordering::Less,
                BinOp::Le => ord != Ordering::Greater,
                BinOp::Gt => ord == Ordering::Greater,
                BinOp::Ge => ord != Ordering::Less,
                _ => return None,
            }))
        }
        BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor => {
            let (x, y) = (a.word()?, b.word()?);
            let r = match op {
                BinOp::Add => x.wrapping_add(y),
                BinOp::Sub => x.wrapping_sub(y),
                BinOp::Mul => x.wrapping_mul(y),
                BinOp::BitAnd => x & y,
                BinOp::BitOr => x | y,
                BinOp::BitXor => x ^ y,
                _ => return None,
            };
            Some(CVal::Word(r & m, w, signed))
        }
        BinOp::Div | BinOp::Rem => {
            let (x, y) = (a.word()?, b.word()?);
            // A zero divisor would have panicked; rustc would not have emitted a
            // const that divides by zero, so refusing is the safe direction.
            if y == 0 {
                return None;
            }
            let r = if signed {
                let (sx, sy) = (c_signed(x, w), c_signed(y, w));
                // `MIN / -1` overflows; refuse rather than wrap into a value the
                // const never had.
                if sx == -(1i128 << (w - 1)) && sy == -1 {
                    return None;
                }
                if op == BinOp::Div { sx / sy } else { sx % sy }
            } else if op == BinOp::Div {
                (x / y) as i128
            } else {
                (x % y) as i128
            };
            Some(CVal::Word((r as u64) & m, w, signed))
        }
        BinOp::Shl | BinOp::Shr => {
            let (x, y) = (a.word()?, b.word()?);
            // A shift at or past the width would have panicked; refuse.
            if y >= w as u64 {
                return None;
            }
            let r = if op == BinOp::Shl {
                (x << y) & m
            } else if signed {
                (c_signed(x, w) >> y) as u64 & m
            } else {
                x >> y
            };
            Some(CVal::Word(r & m, w, signed))
        }
    }
}

/// Whether a binary op yields a `bool` whose operands keep their own type.
///
/// Such an op's width and signedness come from the operands, never from the
/// `bool` destination; see [`c_assign`].
fn is_comparison(op: BinOp) -> bool {
    matches!(
        op,
        BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge
    )
}

/// The width and signedness a comparison's two operands agree on.
///
/// A comparison compares like-typed operands, so a mismatch means they were not
/// read at a common width; comparing them would be meaningless, so it is refused
/// rather than guessed.
fn c_operand_shape(x: CVal, y: CVal) -> Option<(u8, bool)> {
    match (x, y) {
        (CVal::Word(_, wx, sx), CVal::Word(_, wy, sy)) if wx == wy && sx == sy => Some((wx, sx)),
        (CVal::Bool(_), CVal::Bool(_)) => Some((1, false)),
        _ => None,
    }
}

/// A unary op on a concrete value.
fn c_unop(op: UnOp, x: CVal, w: u8, signed: bool) -> Option<CVal> {
    if !c_width_ok(w) {
        return None;
    }
    match op {
        UnOp::Not => match x {
            CVal::Bool(b) => Some(CVal::Bool(!b)),
            CVal::Word(v, _, s) => Some(CVal::Word(!v & c_mask(w), w, s)),
        },
        UnOp::Neg => {
            let v = x.word()?;
            Some(CVal::Word(v.wrapping_neg() & c_mask(w), w, signed))
        }
    }
}

/// A checked binary op: the wrapped value *and* whether it overflowed.
///
/// The overflow flag is computed exactly, in a wider integer, rather than from a
/// bit test: the const body's own `assert(!flag)` is what decides whether the
/// constant is valid, and a wrong flag would either refuse a good constant or
/// fold a value the const never had.
fn c_checked(op: BinOp, a: CVal, b: CVal, w: u8, signed: bool) -> Option<(u64, bool)> {
    if !c_width_ok(w) {
        return None;
    }
    let (x, y) = (a.word()?, b.word()?);
    let m = c_mask(w);
    match op {
        BinOp::Add | BinOp::Sub | BinOp::Mul => {
            if signed {
                let (sx, sy) = (c_signed(x, w), c_signed(y, w));
                let full = match op {
                    BinOp::Add => sx + sy,
                    BinOp::Sub => sx - sy,
                    BinOp::Mul => sx * sy,
                    _ => return None,
                };
                let lo = -(1i128 << (w - 1));
                let hi = (1i128 << (w - 1)) - 1;
                Some(((full as u64) & m, full < lo || full > hi))
            } else {
                let (ux, uy) = (x as u128, y as u128);
                let full = match op {
                    BinOp::Add => ux + uy,
                    // `wrapping_sub` in `u128` is huge when `x < y`, which is
                    // exactly the underflow the `> m` test must catch.
                    BinOp::Sub => ux.wrapping_sub(uy),
                    BinOp::Mul => ux * uy,
                    _ => return None,
                };
                Some(((full as u64) & m, full > m as u128))
            }
        }
        _ => None,
    }
}

/// A cast to a concrete type at `dw` bits.
fn c_cast(x: CVal, ty: &Ty, dw: u8) -> Option<CVal> {
    if !c_width_ok(dw) {
        return None;
    }
    let v = x.word()?;
    let sw = x.width();
    let m = c_mask(dw);
    let r = if dw > sw && x.signed() {
        // A widening of a signed value sign-extends, so `-1i8 as i16` is `-1`.
        (c_signed(v, sw) as u64) & m
    } else {
        v & m
    };
    Some(CVal::Word(r & m, dw, ty.is_signed()))
}

/// Execute one assignment into the folder's store.
fn c_assign(
    f: &MirFn,
    env: &mut BTreeMap<(u32, Vec<u32>), CVal>,
    consts: &BTreeMap<String, Const>,
    dest: &Place,
    rv: &Rvalue,
) -> Option<()> {
    let dty = c_place_ty(f, dest)?;
    let chain = c_field_chain(&dest.proj)?;
    // A scalar destination's width, read per arm: a `CheckedBinary` writes a
    // *tuple*, whose width is not a single number, so forcing it up front would
    // refuse every checked op -- the shape every arithmetic const body has.
    let dw = dty.width();
    // Narrow a computed value to the destination's width, then store it. Reading
    // the operands happens first so the immutable and mutable borrows of `env`
    // never overlap.
    let narrow = |v: CVal| match (v, dw) {
        (CVal::Word(x, _, s), Some(w)) => CVal::Word(x & c_mask(w), w, s),
        (v, _) => v,
    };
    match rv {
        Rvalue::Use(o) => {
            let v = c_operand(env, consts, o, dw)?;
            env.insert((dest.local, chain), narrow(v));
        }
        Rvalue::Binary(op, a, b) => {
            if is_comparison(*op) {
                // The destination is a `bool`, but the operands keep their own
                // type (`_0 = Lt(const -1_i8, const 0_i8)` writes a `bool` local
                // from `i8` operands). Reading the width and sign off the `bool`
                // destination would compare the `-1i8` pattern, 255, as unsigned
                // and fold `-1i8 < 0i8` to *false* -- a false proof of a contract
                // that claims it. Take them from the operands instead.
                let x = c_operand(env, consts, a, None)?;
                let y = c_operand(env, consts, b, None)?;
                let (w, signed) = c_operand_shape(x, y)?;
                let v = c_binop(*op, x, y, w, signed)?;
                env.insert((dest.local, chain), narrow(v));
            } else {
                let w = dw?;
                let x = c_operand(env, consts, a, Some(w))?;
                let y = c_operand(env, consts, b, Some(w))?;
                let v = c_binop(*op, x, y, w, dty.is_signed())?;
                env.insert((dest.local, chain), narrow(v));
            }
        }
        Rvalue::Unary(op, a) => {
            let w = dw?;
            let x = c_operand(env, consts, a, Some(w))?;
            let v = c_unop(*op, x, w, dty.is_signed())?;
            env.insert((dest.local, chain), narrow(v));
        }
        Rvalue::CheckedBinary(op, a, b) => {
            let rty = c_component_ty(&dty, 0)?;
            let rw = rty.width()?;
            let x = c_operand(env, consts, a, Some(rw))?;
            let y = c_operand(env, consts, b, Some(rw))?;
            let (val, ovf) = c_checked(*op, x, y, rw, rty.is_signed())?;
            let mut c0 = chain.clone();
            c0.push(0);
            env.insert((dest.local, c0), CVal::Word(val, rw, rty.is_signed()));
            let mut c1 = chain;
            c1.push(1);
            env.insert((dest.local, c1), CVal::Bool(ovf));
        }
        Rvalue::Cast(o, ty) => {
            let w = dw?;
            let x = c_operand(env, consts, o, None)?;
            let v = c_cast(x, ty, w)?;
            env.insert((dest.local, chain), narrow(v));
        }
        // An aggregate, a reference, a length, a discriminant: nothing a
        // literal-folded `const` needs, and each refused rather than guessed.
        _ => return None,
    }
    Some(())
}

/// Fold a `const` item whose body is an expression, by interpreting it.
///
/// rustc prints a `const` that folds to a literal inline (`const K: u8 = const
/// 7_u8;`) but prints one built by an expression as its const-evaluated *body*,
/// with its own locals and basic blocks:
///
/// ```text
/// const NEXT: u8 = {
///     let mut _0: u8;
///     let mut _1: (u8, bool);
///     bb0: { _1 = AddWithOverflow(const 7_u8, const 4_u8); assert(!(_1.1), …); }
///     bb1: { _0 = move (_1.0); return; }
/// }
/// ```
///
/// The use site is still `_0 = const NEXT`, so without reading the body the item
/// stays an unreadable `Const::Other` and a contract that names it is skipped --
/// a lost proof. The body is parsed with [`parse_fn_body`], the same reader a
/// function uses, and then walked as a concrete computation: every operand is a
/// literal, so a branch is resolved by its actual value and an `assert` is
/// *checked* rather than assumed.
///
/// **It refuses more than it accepts, and each refusal is the safe direction.**
/// A call, a loop, an operand that is not a literal, a failed `assert`, a shift or
/// divide that would panic, a place with a non-field projection: each returns
/// `None`, which leaves the item unmodelled and the contract that named it
/// *unreadable* -- a skip, never a false proof. The walk is bounded by the block
/// count so a cyclic body cannot spin.
///
/// `start` is the line after the `const … = {` header, and `ret_ty` is the
/// declared type, which is the width and signedness the folded literal must carry
/// so the use site folds the way an inline literal would.
fn fold_const_block(
    lines: &[&str],
    start: usize,
    ret_ty: Ty,
    enums: &BTreeMap<String, EnumLayout>,
    consts: &BTreeMap<String, Const>,
) -> Option<Const> {
    // A `const` declared wider than the folder's word (`i128`/`u128`) is refused
    // before its body is interpreted: the width-taking helpers would each have to
    // refuse it, and the exact overflow test would panic on `i128::MIN` first. See
    // [`c_width_ok`].
    if !ret_ty.width().is_some_and(c_width_ok) {
        return None;
    }
    let mut f = MirFn {
        name: String::new(),
        arg_locals: Vec::new(),
        ret_ty: ret_ty.clone(),
        locals: BTreeMap::new(),
        local_names: BTreeMap::new(),
        debug_bindings: Vec::new(),
        blocks: Vec::new(),
        written: std::collections::BTreeSet::new(),
        impl_loc: None,
    };
    f.locals.insert(0, ret_ty.clone());
    parse_fn_body(lines, start, &mut f, enums);

    let mut env: BTreeMap<(u32, Vec<u32>), CVal> = BTreeMap::new();
    let mut block = f.blocks.first()?.id;
    // A `const` body cannot loop (const eval requires termination), but the walk
    // is bounded anyway so a malformed body cannot spin the front end.
    let mut steps = 0usize;
    let limit = f.blocks.len() + 4;
    loop {
        steps += 1;
        if steps > limit {
            return None;
        }
        let b = f.blocks.iter().find(|b| b.id == block)?.clone();
        for s in &b.stmts {
            match s {
                Stmt::Nop => {}
                Stmt::Unknown(_) => return None,
                Stmt::Assign(dest, rv) => c_assign(&f, &mut env, consts, dest, rv)?,
            }
        }
        match &b.term {
            Term::Goto(t) => block = *t,
            Term::Return => {
                let v = env.get(&(0, Vec::new()))?;
                return c_const_of(*v, &ret_ty);
            }
            Term::Assert { cond, negated, target, .. } => {
                // The const body's own overflow and shift checks. rustc would not
                // have emitted a const whose check fails, so a failure here means
                // the body is not the shape this folder understands: refuse rather
                // than fold a value the const never had.
                let c = c_operand(&env, consts, cond, None)?.as_bool()?;
                let ok = if *negated { !c } else { c };
                if !ok {
                    return None;
                }
                block = *target;
            }
            Term::SwitchInt { discr, cases, otherwise } => {
                // A branch is resolved by its *value*, which is what makes the
                // "read the first arm" hazard the literal folder warns about
                // impossible here: only the taken edge is followed.
                let d = c_operand(&env, consts, discr, None)?.word()?;
                let mut next = *otherwise;
                for (k, t) in cases {
                    if *k as u64 == d {
                        next = *t;
                        break;
                    }
                }
                if next == usize::MAX {
                    return None;
                }
                block = next;
            }
            // A call, an `unreachable`, or an unmodelled terminator.
            _ => return None,
        }
    }
}

/// Turn a folded concrete value into the `Const` a use site folds.
///
/// The value carries `ret_ty` so the literal has the width and signedness the
/// item was declared with -- exactly the type suffix an inline literal prints --
/// which is what the use site reads the width and sign from.
fn c_const_of(v: CVal, ret_ty: &Ty) -> Option<Const> {
    match v {
        CVal::Bool(b) => Some(Const::Bool(b)),
        CVal::Word(x, w, _) => {
            if w == 1 {
                return Some(Const::Bool(x != 0));
            }
            Some(Const::UInt(x as u128, Some(ret_ty.clone())))
        }
    }
}

/// Parse a Rust string literal exactly as `rustc --emit=mir` prints it.
///
/// The dump writes a `str` constant with double quotes and Rust's own escapes
/// (`"a\"b"`, `"\u{1f600}"`), so the raw text between the quotes is not the value.
/// Only a string that *starts* with a quote is a literal: a path constant
/// (`core::num::MAX`) and an enum construction (`Mode::Idle`) are not, and reading
/// one as a string would invent a message. The escapes decoded here are the ones
/// the pretty-printer emits: `\n \r \t \\ \" \0`, `\xNN`, and `\u{…}`.
pub fn parse_str_literal(s: &str) -> Option<String> {
    let t = s.trim();
    let inner = t.strip_prefix('"')?.strip_suffix('"')?;
    let mut out = String::new();
    let mut chars = inner.chars();
    while let Some(c) = chars.next() {
        if c != '\\' {
            out.push(c);
            continue;
        }
        match chars.next()? {
            'n' => out.push('\n'),
            'r' => out.push('\r'),
            't' => out.push('\t'),
            '\\' => out.push('\\'),
            '"' => out.push('"'),
            '\'' => out.push('\''),
            '0' => out.push('\0'),
            'x' => {
                let hi = chars.next()?.to_digit(16)?;
                let lo = chars.next()?.to_digit(16)?;
                out.push(char::from((hi * 16 + lo) as u8));
            }
            'u' => {
                // `\u{1f600}`: the braces are part of the escape.
                if chars.next()? != '{' {
                    return None;
                }
                let mut hex = String::new();
                for c in chars.by_ref() {
                    if c == '}' {
                        break;
                    }
                    hex.push(c);
                }
                out.push(char::from_u32(u32::from_str_radix(&hex, 16).ok()?)?);
            }
            // An escape the printer does not emit is not silently dropped: a
            // literal this reader does not understand must not become a wrong
            // message, so the whole literal is refused.
            _ => return None,
        }
    }
    Some(out)
}

/// Parse a Rust *byte*-string literal as `rustc --emit=mir` prints it (`b"…"`).
///
/// The dump escapes a byte string byte by byte, so a non-ASCII byte appears as
/// `\xNN` rather than as a `char`; the escapes are decoded to raw bytes, not to
/// UTF-8. Returns `None` for anything that is not a byte-string literal, so a
/// caller can tell "not this shape" from "an empty byte string".
pub fn parse_byte_str_literal(s: &str) -> Option<Vec<u8>> {
    let t = s.trim();
    let inner = t.strip_prefix("b\"")?.strip_suffix('"')?;
    let mut out = Vec::new();
    let mut chars = inner.chars();
    while let Some(c) = chars.next() {
        if c != '\\' {
            // A literal character is UTF-8 encoded, matching how rustc writes a
            // printable non-ASCII byte in a byte string.
            let mut buf = [0u8; 4];
            out.extend_from_slice(c.encode_utf8(&mut buf).as_bytes());
            continue;
        }
        match chars.next()? {
            'n' => out.push(b'\n'),
            'r' => out.push(b'\r'),
            't' => out.push(b'\t'),
            '\\' => out.push(b'\\'),
            '"' => out.push(b'"'),
            '\'' => out.push(b'\''),
            '0' => out.push(0),
            'x' => {
                let hi = chars.next()?.to_digit(16)?;
                let lo = chars.next()?.to_digit(16)?;
                out.push((hi * 16 + lo) as u8);
            }
            _ => return None,
        }
    }
    Some(out)
}

/// Render the pieces of a `format_args!` message into the message a reader wants.
///
/// Edition 2024 does not put a literal `panic!("a{}b", x)` in the MIR; it puts the
/// *pieces* (`["a", "b"]`) and, separately, the arguments. The number of arguments
/// is `P` (the piece count) or `P - 1`: `format_args!` interleaves each argument
/// with a piece, and the two shapes are "an argument in every gap" (`P - 1` of
/// them, `{}` between each adjacent pair) and "one more argument after the last
/// piece" (`P`, the extra one appended). `new_const` has no arguments at all, so
/// its pieces are concatenated as they stand.
///
/// This matters for the message, not for the count: a `panic!("{} tail", x)`
/// prints `["", " tail"]` with *one* argument, so joining every gap would claim
/// two placeholders and the report would say `{} tail{}` for a message that has
/// one. A `Count` argument (dynamic width/precision) is not produced by a panic
/// message, so it cannot appear here.
pub fn join_format_pieces(pieces: &[String], args: usize) -> String {
    if pieces.is_empty() {
        return String::new();
    }
    let gaps = (pieces.len() - 1).min(args);
    let mut out = String::new();
    for (i, p) in pieces.iter().enumerate() {
        if i > 0 {
            out.push_str("{}");
        }
        out.push_str(p);
    }
    for _ in gaps..args {
        out.push_str("{}");
    }
    out
}

/// Decode the `b"…"` template of `Arguments::new::<LEN, N>(const b"…", …)`.
///
/// The encoding is `core`'s own (see `core::fmt::rt` and the comment on
/// `fmt::Arguments`): `0x00` ends the template, a byte `< 0x80` introduces that
/// many literal bytes, `0x80` introduces a `u16` little-endian length followed by
/// that many literal bytes, `0xC0` is a placeholder for the next argument with
/// default options, and any other byte `> 0xC0` is a placeholder with custom
/// options whose low bits say which option words follow. Only the *literal* pieces
/// are needed for a message, so the option words are skipped by their fixed sizes
/// and a `{}` is emitted for each placeholder -- the same rendering
/// [`join_format_pieces`] gives the `new_v1` shape. A malformed template is
/// refused rather than guessed at, so a printer change surfaces as an unmodelled
/// panic rather than as a wrong message.
pub fn decode_format_template(bytes: &[u8]) -> Option<Vec<String>> {
    let mut pieces = Vec::new();
    let mut lit = String::new();
    let mut i = 0usize;
    let read_u16 = |i: &mut usize| -> Option<u16> {
        let v = u16::from_le_bytes([*bytes.get(*i)?, *bytes.get(*i + 1)?]);
        *i += 2;
        Some(v)
    };
    while i < bytes.len() {
        let n = bytes[i];
        i += 1;
        if n == 0 {
            pieces.push(lit);
            return Some(pieces);
        } else if n < 0x80 {
            let end = i + n as usize;
            let s = bytes.get(i..end)?;
            lit.push_str(std::str::from_utf8(s).ok()?);
            i = end;
        } else if n == 0x80 {
            let len = read_u16(&mut i)? as usize;
            let end = i + len;
            lit.push_str(std::str::from_utf8(bytes.get(i..end)?).ok()?);
            i = end;
        } else if n == 0xC0 {
            pieces.push(std::mem::take(&mut lit));
        } else {
            // Custom options: the low bits say which words follow, in order.
            if n & 1 != 0 {
                i += 4;
            }
            if n & 2 != 0 {
                i += 2;
            }
            if n & 4 != 0 {
                i += 2;
            }
            if n & 8 != 0 {
                i += 2;
            }
            if i > bytes.len() {
                return None;
            }
            pieces.push(std::mem::take(&mut lit));
        }
    }
    None
}

/// Parse a constant like `0_u32`, `true`, `255_u32`, `()`.
fn parse_const(s: &str) -> Const {
    let t = s.trim();
    if let Some(bytes) = parse_byte_str_literal(t) {
        return Const::Bytes(bytes);
    }
    if let Some(text) = parse_str_literal(t) {
        return Const::Str(text);
    }
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
/// Parse the `dest = callee(args)` head of a call terminator, up to the ` -> `.
///
/// Shared by the two call shapes: the ordinary one with a `[return: bbN]` arm and
/// the diverging one without. Only the arrow and what follows it differ between
/// them, so the head is read once here rather than twice.
fn parse_call_head(
    head: &str,
    enums: &BTreeMap<String, EnumLayout>,
) -> Option<(Callee, Vec<Operand>, Place)> {
    let lhs = head.trim();
    let eq = lhs.find(" = ")?;
    let dest_text = lhs[..eq].trim();
    let call = lhs[eq + 3..].trim();
    let dest = parse_place(dest_text, enums).unwrap_or(Place::new(u32::MAX));
    let open = call.find('(')?;
    if !call.ends_with(')') {
        return None;
    }
    let name = call[..open].trim();
    let inner = &call[open + 1..call.len() - 1];
    let args: Vec<Operand> =
        split_top_level(inner, ',').iter().map(|a| parse_operand(a, enums)).collect();
    let callee = if name.is_empty() {
        Callee::Indirect(dest.clone())
    } else {
        Callee::Name(name.to_string())
    };
    Some((callee, args, dest))
}

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
    // A copy of a reference *through* another reference is printed with a retag
    // marker: `_4 = no_retag copy (*_3)` on 1.99+, and `_4 = deref_copy (*_3)` on
    // 1.85 (the MSRV). Leaving either prefix on made the whole rvalue unparseable,
    // and that is not a harmless loss: `_4` then became `Rvalue::Unknown`, got no
    // address, and `(*_4) = 5` was dropped -- so `requires: x == 0` / `ensures: ret
    // == 0` was **proved** against a body that returns 5, while the true `ret == 5`
    // was refuted. Both markers are peeled to a plain copy of the inner place.
    //
    // Only the `copy`/`move` forms are peeled. Stripping the marker from *every*
    // rvalue also rewrote `no_retag &mut _1` and `no_retag (*_1)` in method receiver
    // lowering, which changed where a `&mut self` receiver pointed and lost the
    // callee's write -- 114 corpus verdicts moved, most of them to the wrong answer.
    // The retag-copy is the one form that was broken; the rest keep the meaning they
    // had.
    for prefix in ["no_retag ", "deref_copy "] {
        if let Some(rest) = t.strip_prefix(prefix).map(str::trim) {
            let as_copy = if rest.starts_with("copy ") || rest.starts_with("move ") {
                rest.to_string()
            } else {
                format!("copy {rest}")
            };
            return parse_rvalue(&as_copy, enums);
        }
    }
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
    // `&_1`, `&mut _1`, `&raw const _1`, `&raw mut _1`
    //
    // The raw forms appear for a `&mut [T]` argument's bounds check: rustc
    // materialises the metadata through a raw borrow, `_3 = &raw const (fake)
    // (*_1); _4 = PtrMetadata(move _3)`, where the immutable `&[T]` reads
    // `PtrMetadata(copy _1)` directly. Both name the same place, so both are a
    // `Ref`.
    //
    // The reference check comes *before* the cast check, because a borrow of an
    // enum payload contains ` as `: `_4 = &((_1 as Run).0: u8)` is the address of
    // a downcast place, and the cast arm's `find(" as ")` would split it into a
    // cast of the string `&((_1` -- which parses as neither a place nor an operand,
    // so the rvalue became a cast of `Unknown`, `_4` got no address, and the
    // `copy (*_4)` that reads the guard read `Unknown`. That made every `match`
    // with a `Variant(n) if guard` arm report "unmodelled switch discriminant" --
    // the guard's own payload read was the thing that failed, not the switch. The
    // cast arm cannot mis-take a reference, because `&…` is not a place, so trying
    // the reference form first is safe for a real cast.
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
    if let Some(rest) = t.strip_prefix("Len(") {
        if let Some(p) = parse_place(strip_copy(close_paren(rest)), enums) {
            return Rvalue::Len(p);
        }
    }
    if let Some(rest) = t.strip_prefix("PtrMetadata(") {
        if let Some(p) = parse_place(strip_copy(close_paren(rest)), enums) {
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
        let target = parse_return_target(&t[i..]).unwrap_or(usize::MAX);
        if let Some((callee, args, dest)) = parse_call_head(&t[..i], enums) {
            return Err(Term::Call { callee, args, dest, diverges: false, target });
        }
        return Err(Term::Unknown(t.to_string()));
    }
    // A *diverging* call: `_3 = core::panicking::panic(…) -> unwind continue`, with
    // no `[return: bbN]` arm because the call never returns. `panic!`, `assert!`,
    // `unwrap` and an out-of-bounds index all lower this way, and it is the only
    // shape where a call has no normal successor. The guard is the absence of
    // `[return:` before the arrow: a call with both arms is the ordinary kind above.
    if let Some(i) = t.find(" -> unwind") {
        if !t[..i].contains("[return:") {
            if let Some((callee, args, dest)) = parse_call_head(&t[..i], enums) {
                return Err(Term::Call { callee, args, dest, diverges: true, target: usize::MAX });
            }
        }
    }
    // The *cleanup* form of a diverging call: `_4 = core::panicking::panic(…) -> bb4;`
    // with `bb4 (cleanup)`. With a live `Drop` local, rustc prints the call's single
    // successor as its cleanup edge (`-> bbN`), not the `-> unwind continue` arm
    // above -- the call still never returns, but the shape differs. The bare
    // `-> bbN` (no `[`) is what tells it apart: an ordinary call always prints
    // `-> [return: bbN, unwind …]`. The head is parsed here; the block is marked
    // diverging *after* the body is read, because the `!`-typed destination and the
    // `(cleanup)` marker are only both known then. See the fix-up in `parse_fn_body`.
    if let Some(i) = t.find(" -> bb") {
        let after = t[i + 4..].trim();
        if !t[..i].contains("[return:") && !after.starts_with('[') {
            if let Some(target) = parse_bb_ref(after.trim_end_matches(';')) {
                if let Some((callee, args, dest)) = parse_call_head(&t[..i], enums) {
                    return Err(Term::Call { callee, args, dest, diverges: false, target });
                }
            }
        }
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

/// [`parse_program_with`] with the crate-level `const` names the source declared.
///
/// The dump prints a crate-level `const` and a function-local one identically, so
/// the bare-use test in [`const_mentions`] is the only in-dump tell -- and it is
/// silent for a crate-level constant that only a *contract* names. This variant
/// takes the names the source says are module-scoped, so those definitions are
/// kept as well. See [`crate::mir::spec::crate_level_consts`].
#[allow(clippy::too_many_arguments)]
pub fn parse_program_scoped(
    text: &str,
    enums: &BTreeMap<String, EnumLayout>,
    crate_consts: &std::collections::BTreeSet<String>,
    const_generics: &std::collections::BTreeSet<String>,
    impl_owners: &BTreeMap<(usize, usize), String>,
    impl_traits: &BTreeMap<(usize, usize), String>,
    impl_trait_args: &BTreeMap<(usize, usize), String>,
    declared_traits: &std::collections::BTreeSet<String>,
) -> MirProgram {
    parse_program_impl(
        text,
        enums,
        crate_consts,
        const_generics,
        impl_owners,
        impl_traits,
        impl_trait_args,
        declared_traits,
    )
}

/// [`parse_program`] with the enum layouts from the source.
///
/// A `match` lowers to `(base as Variant)` downcasts whose *variant names* the
/// MIR dump prints and whose *discriminants* it does not. Resolving a name to its
/// index needs the declaration order, which lives in the source rather than the
/// dump, so it is passed in. An empty map is the old behaviour: `Option`/`Result`
/// resolve from their built-in numbering and every other enum refuses a downcast.
pub fn parse_program_with(text: &str, enums: &BTreeMap<String, EnumLayout>) -> MirProgram {
    parse_program_impl(
        text,
        enums,
        &std::collections::BTreeSet::new(),
        &std::collections::BTreeSet::new(),
        &BTreeMap::new(),
        &BTreeMap::new(),
        &BTreeMap::new(),
        &std::collections::BTreeSet::new(),
    )
}

#[allow(clippy::too_many_arguments)]
fn parse_program_impl(
    text: &str,
    enums: &BTreeMap<String, EnumLayout>,
    crate_consts: &std::collections::BTreeSet<String>,
    const_generics: &std::collections::BTreeSet<String>,
    impl_owners: &BTreeMap<(usize, usize), String>,
    impl_traits: &BTreeMap<(usize, usize), String>,
    impl_trait_args: &BTreeMap<(usize, usize), String>,
    declared_traits: &std::collections::BTreeSet<String>,
) -> MirProgram {
    let lines: Vec<&str> = text.lines().collect();
    let mut prog = MirProgram {
        enums: enums.clone(),
        impl_owners: impl_owners.clone(),
        impl_traits: impl_traits.clone(),
        impl_trait_args: impl_trait_args.clone(),
        declared_traits: declared_traits.clone(),
        ..MirProgram::default()
    };
    // Which bare names are ever used as a `const` at a use site, so a definition
    // can be told a crate-level item from a function-local one. See
    // [`const_mentions`]. A `const` generic parameter's uses print bare too but
    // are not items at all, so its names are removed: otherwise a function-local
    // `const N` in some other function would keep a bare program-wide key. See
    // [`crate::mir::spec::const_generic_params`].
    let mentions = const_mentions(text);
    let mut bare_uses = mentions.bare_uses.clone();
    for name in const_generics {
        bare_uses.remove(name);
    }
    // A function-local `const` whose crate-level twin the compiler removed -- a
    // `#[cfg]`-disabled item -- prints its definition bare (`const K: u8 = const
    // 3_u8;`) but keeps its *use* qualified (`const owner::K`), and there is no
    // qualified definition of that path to match. The source set still names `K`
    // (the scanner reads the `#[cfg]`-disabled item), so without this the bare
    // definition would take the crate key and a contract on another function could
    // name it -- a false proof. Only a qualified use whose path names a *function*
    // is such a local; an associated constant (`Foo::K`, defined `<impl at …>::K`)
    // and a module constant (`a::K`, defined and used qualified) are not, so a
    // compiled crate constant those paths name keeps its bare key. See
    // [`claimed_bare_const_uses`].
    let claimed_bare = claimed_bare_const_uses(&mentions);
    let claimed_paths = claimed_bare_paths(&mentions);

    // --- `const` items -----------------------------------------------------
    // Collected *before* the function loop, and in two stages, so an expression
    // body can name a constant the dump prints *after* it. rustc keeps source
    // declaration order in the dump, and Rust lets a constant refer to a later
    // one (`const NEXT: u8 = LIMIT + 1;` above `const LIMIT: u8 = 10;`), so a
    // single in-order pass would leave `NEXT` unresolved -- an unmodelled item
    // and a lost proof. Stage 1 reads every literal (and every CTFE block that
    // folds to one) into the table; stage 2 folds the expression bodies to a
    // fixpoint, each round seeing the constants the previous one resolved. A
    // cycle resolves nothing and stops the loop, leaving those items unmodelled
    // as before.
    //
    // The scan mirrors the function loop's skip of a `// MIR FOR CTFE` copy, so a
    // duplicate body is not read a second time.
    let mut pending: Vec<(String, usize, Ty)> = Vec::new();
    let mut idx = 0;
    while idx < lines.len() {
        let line = lines[idx];
        if line.trim() == "// MIR FOR CTFE" {
            let mut k = idx + 1;
            while k < lines.len() && lines[k].trim().is_empty() {
                k += 1;
            }
            if k < lines.len() && parse_fn_header(lines[k]).is_some() {
                let mut m = k + 1;
                while m < lines.len() && !lines[m].starts_with('}') {
                    m += 1;
                }
                idx = m + 1;
                continue;
            }
        }
        if let Some((name, ret_ty, body)) = parse_const_item(line) {
            if let Some(key) = const_key(&name, &claimed_bare, &claimed_paths, &bare_uses, crate_consts)
            {
                if let Some(rest) = body.strip_prefix("const ") {
                    prog.consts.insert(key, parse_const(rest));
                } else if body.starts_with('{') {
                    match block_const_value(&lines[idx + 1..]) {
                        Some(lit) => {
                            prog.consts.insert(key, parse_const(lit));
                        }
                        None => {
                            if let Some(rt) = ret_ty {
                                pending.push((key, idx + 1, rt));
                            }
                        }
                    }
                }
            }
        }
        idx += 1;
    }
    loop {
        let mut progressed = false;
        pending.retain(|(key, start, ty)| {
            let folded = fold_const_block(&lines, *start, ty.clone(), enums, &prog.consts);
            match folded {
                Some(c) => {
                    prog.consts.insert(key.clone(), c);
                    progressed = true;
                    false
                }
                None => true,
            }
        });
        if !progressed {
            break;
        }
    }
    // --- promoted `&[&str]` pieces -----------------------------------------
    // A `panic!`/`assert!` message on edition 2024 is a *promoted* constant: the
    // format pieces are an array of `&str` in a `const NAME::promoted[0]` item, and
    // the call passes a reference to it. The item prints outside any function, so
    // the executor cannot reach it by walking a body -- it is collected here, next
    // to the other `const` items, so the `Arguments` model can read the pieces back.
    for (li, line) in lines.iter().enumerate() {
        let Some(rest) = line.trim_end().strip_prefix("const ") else { continue };
        let Some((name, body)) = rest.split_once(" = ") else { continue };
        let Some(name) = name.split_once(": ").map(|(n, _)| n) else { continue };
        if !name.ends_with(']') || body.trim() != "{" {
            continue;
        }
        // The array literal is the `_1 = [const "a", const "b"];` statement of the
        // body; `_0 = &_1;` is the borrow and carries no string.
        let mut strs = Vec::new();
        for l in lines[li + 1..].iter().take_while(|l| !l.starts_with('}')) {
            let t = l.trim();
            if let Some(rest) = t.strip_prefix("_1 = [") {
                let inner = rest.strip_suffix("];").unwrap_or(rest);
                for piece in split_top_level(inner, ',') {
                    if let Some(s) = piece.trim().strip_prefix("const ") {
                        if let Some(text) = parse_str_literal(s) {
                            strs.push(text);
                        }
                    }
                }
            }
        }
        prog.promoted_strs.insert(name.to_string(), strs);
    }
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
            let impl_loc = crate::mir::spec::impl_location(&name);
            let mut f = MirFn {
                name,
                arg_locals: args.iter().map(|(l, _)| *l).collect(),
                ret_ty: ret_ty.clone(),
                locals: BTreeMap::new(),
                local_names: BTreeMap::new(),
                debug_bindings: Vec::new(),
                blocks: Vec::new(),
                written: std::collections::BTreeSet::new(),
                impl_loc,
            };
            // Local `_0` is the return place, so it carries the return type.
            f.locals.insert(0, ret_ty);
            for (l, t) in &args {
                f.locals.insert(*l, t.clone());
            }
            let j = parse_fn_body(&lines, i + 1, &mut f, enums);
            prog.fns.push(f);
            i = j + 1;
            continue;
        }
        i += 1;
    }
    prog
}

/// Parse a body of basic blocks into `f`, from the line after a header.
///
/// `lines` is the whole dump and `start` is the first body line; the returned
/// index is the line that closes the body, so the caller resumes after it. A
/// function body and a `const` item's const-evaluated body print in the same
/// shape, so both go through here rather than through two copies of the reader.
/// See [`fold_const_block`].
fn parse_fn_body(
    lines: &[&str],
    start: usize,
    f: &mut MirFn,
    enums: &BTreeMap<String, EnumLayout>,
) -> usize {
    // Body runs until the closing brace in column 0.
    let mut j = start;
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
        // A block header: `bbN: {` (or `bbN (cleanup): {`)
        if let Some(rest) = t.strip_prefix("bb") {
            if let Some(colon) = rest.find(':') {
                let header = &rest[..colon];
                if let Ok(id) = header.split_whitespace().next().unwrap_or("").parse::<usize>()
                {
                    if let Some(b) = cur_block.take() {
                        f.blocks.push(b);
                    }
                    cur_block = Some(Block {
                        id,
                        stmts: Vec::new(),
                        term: Term::Unknown("missing".into()),
                        cleanup: header.contains("cleanup"),
                    });
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
    // A call whose destination is a never-typed local (`let mut _4: !;`) and whose
    // only successor is a `(cleanup)` block is the *cleanup* form of a diverging
    // call: the callee returns `!`, so the edge into the cleanup block is its
    // unwind path, and the path ends there. The parser cannot tell this at the
    // line, because the destination's type is declared above and the target's
    // `(cleanup)` marker is below, so the two facts are combined here, once both
    // are known.
    //
    // The guard is deliberately narrow. The destination must be declared `!`, and
    // the target must be a cleanup block -- an ordinary call, which always prints
    // `-> [return: bbN, unwind …]`, has neither and is untouched. A `!`-typed
    // destination is the *only* thing a diverging call writes, so this cannot
    // reclassify a returning call.
    let cleanup_blocks: BTreeMap<usize, bool> =
        f.blocks.iter().map(|b| (b.id, b.cleanup)).collect();
    let never_locals: BTreeSet<LocalIdx> = f
        .locals
        .iter()
        .filter(|(_, ty)| matches!(ty, Ty::Other(s) if s == "!"))
        .map(|(&l, _)| l)
        .collect();
    for b in &mut f.blocks {
        let Term::Call { dest, diverges, target, .. } = &mut b.term else { continue };
        if *diverges || *target == usize::MAX {
            continue;
        }
        if never_locals.contains(&dest.local)
            && cleanup_blocks.get(target).copied().unwrap_or(false)
        {
            *diverges = true;
            *target = usize::MAX;
        }
    }
    j
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
            Term::Call { callee, args, dest, diverges, target } => {
                assert_eq!(*callee, Callee::Name("double".to_string()));
                assert_eq!(args.len(), 1);
                assert_eq!(dest.local, 0);
                assert!(!diverges, "a call with a `[return: bbN]` arm does not diverge");
                assert_eq!(*target, 1);
            }
            other => panic!("expected a call, got {other:?}"),
        }
    }

    /// A call with no `[return: bbN]` arm is a diverging one, not an unknown line.
    ///
    /// This is how `panic!`, `assert!` and `unwrap` lower, and the parser used to
    /// leave the terminator as `Unknown("missing")` because it looked only for the
    /// `[return:` shape. The path was then dropped as unmodelled and the assert was
    /// never checked. Both halves are pinned: the terminator is a `Call`, and it is
    /// marked as diverging.
    #[test]
    fn parses_a_diverging_call_without_a_return_arm() {
        let dump = "fn f(_1: u8) -> u8 {\n    debug x => _1;\n    let mut _0: u8;\n    let mut _2: bool;\n    let mut _3: !;\n\n    bb0: {\n        _2 = Le(copy _1, const 200_u8);\n        switchInt(move _2) -> [0: bb2, otherwise: bb1];\n    }\n\n    bb1: {\n        _0 = const 1_u8;\n        return;\n    }\n\n    bb2: {\n        _3 = core::panicking::panic(const \"assertion failed: x <= 200\") -> unwind continue;\n    }\n}\n";
        let prog = parse_program(dump);
        match &prog.fns[0].blocks[2].term {
            Term::Call { callee, diverges, .. } => {
                assert_eq!(*callee, Callee::Name("core::panicking::panic".to_string()));
                assert!(*diverges, "a call with no return arm diverges");
            }
            other => panic!("expected a diverging call, got {other:?}"),
        }
    }

    /// The *cleanup* form of a diverging call is recognised too.
    ///
    /// With a live `Drop` local, rustc prints the call's single successor as its
    /// cleanup edge (`-> bb4`) and marks the target `bb4 (cleanup)`, rather than
    /// the `-> unwind continue` arm above. The call still never returns, so it must
    /// still be a diverging call -- the destination's `!` type and the target's
    /// `(cleanup)` marker are the two facts the parser combines once the body is
    /// read. Without this, an `assert!` in any function with a live RAII local was
    /// still a dropped path.
    #[test]
    fn parses_the_cleanup_form_of_a_diverging_call() {
        let dump = "fn f(_1: u8) -> u8 {\n    debug x => _1;\n    let mut _0: u8;\n    let _2: Guard;\n    let mut _3: bool;\n    let mut _4: !;\n\n    bb0: {\n        _2 = Guard(const 0_u8);\n        _3 = Lt(copy _1, const 200_u8);\n        switchInt(move _3) -> [0: bb2, otherwise: bb1];\n    }\n\n    bb1: {\n        _0 = const 1_u8;\n        return;\n    }\n\n    bb2: {\n        _4 = core::panicking::panic(const \"assertion failed: x < 200\") -> bb4;\n    }\n\n    bb3 (cleanup): {\n        resume;\n    }\n\n    bb4 (cleanup): {\n        drop(_2) -> [return: bb3, unwind terminate(cleanup)];\n    }\n}\n";
        let prog = parse_program(dump);
        let bb2 = prog.fns[0].blocks.iter().find(|b| b.id == 2).expect("bb2");
        match &bb2.term {
            Term::Call { callee, diverges, .. } => {
                assert_eq!(*callee, Callee::Name("core::panicking::panic".to_string()));
                assert!(*diverges, "a `!`-typed call into a cleanup block diverges");
            }
            other => panic!("expected a diverging call, got {other:?}"),
        }
        // The cleanup blocks themselves are marked, and a returning call is left
        // alone -- the marker is not applied to every `-> bbN`.
        assert!(prog.fns[0].blocks.iter().find(|b| b.id == 4).unwrap().cleanup);
        assert!(!prog.fns[0].blocks.iter().find(|b| b.id == 0).unwrap().cleanup);
    }

    /// An ordinary returning call keeps its target, even into a block that happens
    /// to be a cleanup block -- the destination is not `!`, so it is not diverging.
    #[test]
    fn a_returning_call_into_a_cleanup_block_is_not_diverging() {
        let dump = "fn f(_1: u8) -> u8 {\n    debug x => _1;\n    let mut _0: u8;\n    let mut _2: u8;\n\n    bb0: {\n        _2 = g(copy _1) -> bb1;\n    }\n\n    bb1 (cleanup): {\n        _0 = copy _2;\n        return;\n    }\n}\n";
        let prog = parse_program(dump);
        match &prog.fns[0].blocks[0].term {
            Term::Call { diverges, target, .. } => {
                assert!(!*diverges, "a `u8` destination is not a diverging call");
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

    /// A borrow of an enum payload parses as a `Ref`, not as a cast.
    ///
    /// `_4 = &((_1 as Run).0: u8)` -- how a `match` arm guard's payload read
    /// lowers -- contains the word ` as ` inside its parentheses. The cast arm's
    /// `find(" as ")` matched that, split the string into a cast of `&((_1`, which
    /// parses as neither a place nor an operand, and the borrow got no address, so
    /// the guard read `Unknown` and the `switchInt` on it was "unmodelled switch
    /// discriminant". The reference arm is tried first, so the downcast place
    /// parses whole and the `Ref` is produced.
    #[test]
    fn a_borrow_of_an_enum_payload_is_a_ref_not_a_cast() {
        let mut enums = BTreeMap::new();
        enums.insert(
            "Msg".to_string(),
            EnumLayout {
                variants: vec![
                    ("Ping".to_string(), 0),
                    ("Data".to_string(), 1),
                    ("Stop".to_string(), 2),
                ],
            },
        );
        let rv = parse_rvalue("&((_1 as Data).0: u8)", &enums);
        let Rvalue::Ref(place) = rv else { panic!("expected a Ref, got {rv:?}") };
        assert_eq!(place, Place { local: 1, proj: vec![Proj::Downcast(1), Proj::Field(0)] });
        // A real cast still parses as a cast: `_1 as u32` is not a place.
        let rv = parse_rvalue("move _1 as u32 (IntToInt)", &enums);
        assert!(matches!(rv, Rvalue::Cast(..)), "a cast must stay a cast, got {rv:?}");
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

    /// A named `const` item's literal body is collected, and only a literal.
    ///
    /// The dump prints the item's body separately from its use, so the value has
    /// to be gathered before it can be inlined. An item whose body is an
    /// expression, or a qualified associated constant, must *not* enter the table:
    /// the first has no literal to read, and the second is never referred to by
    /// the plain name.
    ///
    /// A bare definition is kept only when the name is *used* bare somewhere. The
    /// dump prints a crate-level item's use site by its bare name and a
    /// function-local item's by a qualified path, but both definitions look alike,
    /// so a bare definition with no bare use site is a function-local item (or an
    /// unused one) and must not become a program-wide key -- see
    /// [`const_mentions`] and [`a_local_const_does_not_leak_to_another_function`].
    #[test]
    fn named_const_items_are_collected_only_when_literal() {
        let dump = "const K: u8 = const 5_u8;\n\
                    const NEG: i8 = const -1_i8;\n\
                    const B: bool = const true;\n\
                    const UNUSED: u8 = const 9_u8;\n\
                    const EXPR: u8 = {\n    let mut _0: u8;\n\n    bb0: {\n        \
                    _0 = const 1_u8;\n        return;\n    }\n}\n\
                    const ARR::{constant#0}: usize = const 3_usize;\n\
                    fn uses() -> u8 {\n    let mut _0: u8;\n\n    bb0: {\n        \
                    _0 = const K;\n        _0 = const NEG;\n        _0 = const B;\n        \
                    return;\n    }\n}\n";
        let prog = parse_program(dump);
        assert_eq!(prog.consts.get("K"), Some(&Const::UInt(5, Some(Ty::U8))));
        assert_eq!(prog.consts.get("NEG"), Some(&Const::UInt(0xff, Some(Ty::I8))));
        assert_eq!(prog.consts.get("B"), Some(&Const::Bool(true)));
        assert!(!prog.consts.contains_key("UNUSED"), "a bare definition with no bare use is not kept");
        assert!(!prog.consts.contains_key("EXPR"), "an expression body is not a literal");
        assert!(!prog.consts.contains_key("ARR"), "a qualified name is not collected");
    }

    /// A function-local `const`'s definition must not become a bare program-wide
    /// key, or another function's contract could name it.
    ///
    /// `const L: u8 = const 3_u8;` is printed the same way for a crate-level item
    /// and a function-local one; the use site is the only tell -- a crate item is
    /// used bare (`const L`), a local one qualified (`const f::L`). Here `L` is
    /// used only qualified, so it is a local of `f` and must not enter the table
    /// under the bare key. With the bare key present, `g`'s contract could write
    /// `requires: L == 3` and be *proved* against a name `g` cannot see.
    #[test]
    fn a_local_const_does_not_leak_to_another_function() {
        let dump = "fn f() -> u8 {\n    let mut _0: u8;\n\n    bb0: {\n        \
                    _0 = const f::L;\n        return;\n    }\n}\n\
                    const L: u8 = const 3_u8;\n\
                    fn g() -> u8 {\n    let mut _0: u8;\n\n    bb0: {\n        \
                    _0 = const 3_u8;\n        return;\n    }\n}\n";
        let prog = parse_program(dump);
        assert!(!prog.consts.contains_key("L"), "a local const must not get a bare key");
    }

    /// A `const NAME` inside a string literal or an `alloc` block is *data*, not a
    /// use, and must not make `NAME` look crate-level.
    ///
    /// The bare-use scan is the only in-dump tell between a crate-level `const`
    /// and a function-local one, so a false positive here hands a function-local
    /// item a program-wide key -- the false proof
    /// [`a_local_const_does_not_leak_to_another_function`] guards, reopened through
    /// a string. A `debug s => const "const L";` binding and the `alloc` block
    /// behind the string both spell `const L` as text. The `alloc` data line is the
    /// real dump shape -- a gutter and a right-hand column that spells the bytes out
    /// -- so it is *not* a `//` comment and the comment skip does not cover it.
    #[test]
    fn a_string_literal_is_not_a_const_use() {
        let uses = const_mentions(
            "    debug s => const \"const L\";\n\
             alloc12 (size: 7, align: 1) {\n\
             \x20   63 6f 6e 73 74 20 4c 4b                       │ const L\n}\n\
             \x20   _0 = const L;\n",
        )
        .bare_uses;
        assert!(uses.contains("L"), "the real use site is still read: {uses:?}");
        let only_string = const_mentions("    debug s => const \"const M\";\n").bare_uses;
        assert!(
            only_string.is_empty(),
            "a `const NAME` inside a string literal is not a use: {only_string:?}"
        );
        let only_alloc = const_mentions(
            "alloc4 (size: 4, align: 1) {\n\
             \x20   1u8, 1u8, 1u8, 1u8,\n\
             alloc7 (size: 7, align: 1) {\n\
             \x20   63 6f 6e 73 74 20 4e 4f 4e                       │ const NON\n}\n",
        )
        .bare_uses;
        assert!(
            only_alloc.is_empty(),
            "an `alloc` data block is not a use: {only_alloc:?}"
        );
    }

    /// A crate-level `const` a contract names but no body uses keeps its bare key,
    /// because the source says the item is module-scoped.
    ///
    /// The bare-use test is silent for a constant with no use site at all, so the
    /// definition would be dropped and the contract left unreadable -- a lost
    /// proof. The `crate_consts` set is the source's word on the item's scope.
    #[test]
    fn a_crate_level_const_with_no_use_site_is_kept() {
        let dump = "const ONLY: u8 = const 7_u8;\n\
                    fn g() -> u8 {\n    let mut _0: u8;\n\n    bb0: {\n        \
                    _0 = const 3_u8;\n        return;\n    }\n}\n";
        // Without the source's word, the bare definition is dropped.
        assert!(!parse_program(dump).consts.contains_key("ONLY"));
        // With it, the definition is kept so a contract can name it.
        let mut scoped = std::collections::BTreeSet::new();
        scoped.insert("ONLY".to_string());
        let prog = parse_program_scoped(dump, &BTreeMap::new(), &scoped, &std::collections::BTreeSet::new(), &BTreeMap::new(), &BTreeMap::new(), &BTreeMap::new(), &std::collections::BTreeSet::new());
        assert_eq!(prog.consts.get("ONLY"), Some(&Const::UInt(7, Some(Ty::U8))));
        // The tell must not resurrect a name the source did *not* declare: a
        // function-local `L` (used qualified) stays out of the table.
        let dump2 = "fn f() -> u8 {\n    let mut _0: u8;\n\n    bb0: {\n        \
                     _0 = const f::L;\n        return;\n    }\n}\n\
                     const L: u8 = const 3_u8;\n";
        let prog2 = parse_program_scoped(dump2, &BTreeMap::new(), &scoped, &std::collections::BTreeSet::new(), &BTreeMap::new(), &BTreeMap::new(), &BTreeMap::new(), &std::collections::BTreeSet::new());
        assert!(!prog2.consts.contains_key("L"), "a name not in the source's set stays out");
    }

    /// A bare definition whose tail name is used only *qualified* is a
    /// function-local item, and must not keep a bare key even when the source
    /// calls the name crate-level.
    ///
    /// A `#[cfg]`-disabled `const K` is in the source set but not in the dump, so
    /// the only `K` is a local's -- and rustc prints that local's definition bare
    /// (`const K: u8 = const 3_u8;`) with a qualified use (`const owner::K`). The
    /// source's word alone would then record `K = 3` as a crate constant, and a
    /// contract on another function could name it. The qualified-use/qualified-def
    /// mismatch is the in-dump tell that the bare definition is that local.
    #[test]
    fn a_qualified_only_use_keeps_its_bare_definition_out() {
        // The local's definition is bare; its use is qualified, with no qualified
        // definition anywhere. `crate_consts` claims `K` (the source saw a
        // `#[cfg]`-disabled item), and that must not be enough.
        let dump = "fn owner() -> u8 {\n    let mut _0: u8;\n\n    bb0: {\n        \
                    _0 = const owner::K;\n        return;\n    }\n}\n\
                    const K: u8 = const 3_u8;\n";
        let mut scoped = std::collections::BTreeSet::new();
        scoped.insert("K".to_string());
        let prog = parse_program_scoped(dump, &BTreeMap::new(), &scoped, &std::collections::BTreeSet::new(), &BTreeMap::new(), &BTreeMap::new(), &BTreeMap::new(), &std::collections::BTreeSet::new());
        assert!(
            !prog.consts.contains_key("K"),
            "a qualified-only use means the bare definition is that local: {:?}",
            prog.consts
        );
        // The control: a real module constant defines *and* uses its path
        // qualified, so its bare spelling is not a local's and the module path is
        // recorded under its own key.
        let module = "fn g() -> u8 {\n    let mut _0: u8;\n\n    bb0: {\n        \
                      _0 = const a::K;\n        return;\n    }\n}\n\
                      const a::K: u8 = const 5_u8;\n";
        let prog = parse_program(module);
        assert_eq!(prog.consts.get("a::K"), Some(&Const::UInt(5, Some(Ty::U8))));
    }

    /// An *associated* constant's use must not claim a bare definition, or a
    /// compiled crate constant of the same name is discarded.
    ///
    /// rustc uses an associated constant as `const Foo::K` but defines it as
    /// `const <impl at …>::K`, so the use path has no matching definition -- the
    /// same shape a function-local whose crate twin was `#[cfg]`-disabled has. The
    /// tell that separates them is the prefix: `owner::K` names a *function*, so
    /// the bare `K` is that local; `Foo::K` names an associated item, so the bare
    /// `K` is the compiled crate constant and must be kept.
    #[test]
    fn an_associated_use_does_not_claim_a_crate_const() {
        let dump = "const K: u8 = const 7_u8;\n\
                    const <impl at file.rs:3:1: 3:9>::K: u8 = const 3_u8;\n\
                    fn uses_assoc() -> u8 {\n    let mut _0: u8;\n\n    bb0: {\n        \
                    _0 = const Foo::K;\n        return;\n    }\n}\n";
        let mut scoped = std::collections::BTreeSet::new();
        scoped.insert("K".to_string());
        let prog = parse_program_scoped(
            dump,
            &BTreeMap::new(),
            &scoped,
            &std::collections::BTreeSet::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &std::collections::BTreeSet::new(),
        );
        assert_eq!(
            prog.consts.get("K"),
            Some(&Const::UInt(7, Some(Ty::U8))),
            "the compiled crate `K` must survive an associated `Foo::K`: {:?}",
            prog.consts
        );
    }

    /// A function-local `const` inside a *method* or a *nested* function must still
    /// be refused, even though its use path has more than one `::`.
    ///
    /// `Foo::method::L` and `outer::inner::M` are locals, and the owning function is
    /// the path's last `::` segment -- not the whole prefix. Reading the whole
    /// prefix would let both leak back in as program-wide names.
    #[test]
    fn a_method_or_nested_local_use_still_claims_its_bare_definition() {
        // A `#[cfg]`-disabled crate `L`/`M` is gone from the dump, so each local's
        // definition prints *bare* while its use stays qualified -- exactly the
        // shape that would otherwise take the crate key.
        let dump = "fn <impl at file.rs:2:1: 2:9>::method(_1: &Foo) -> u8 {\n    \
                    let mut _0: u8;\n\n    bb0: {\n        _0 = const Foo::method::L;\n        \
                    return;\n    }\n}\n\
                    const L: u8 = const 4_u8;\n\
                    fn outer() -> u8 {\n    let mut _0: u8;\n\n    bb0: {\n        \
                    _0 = const 0_u8;\n        return;\n    }\n}\n\
                    fn inner() -> u8 {\n    let mut _0: u8;\n\n    bb0: {\n        \
                    _0 = const outer::inner::M;\n        return;\n    }\n}\n\
                    const M: u8 = const 1_u8;\n";
        let mut scoped = std::collections::BTreeSet::new();
        scoped.insert("L".to_string());
        scoped.insert("M".to_string());
        let prog = parse_program_scoped(
            dump,
            &BTreeMap::new(),
            &scoped,
            &std::collections::BTreeSet::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &std::collections::BTreeSet::new(),
        );
        assert!(
            !prog.consts.contains_key("L"),
            "a method-local `L` must not get a bare key: {:?}",
            prog.consts
        );
        assert!(
            !prog.consts.contains_key("M"),
            "a nested-fn-local `M` must not get a bare key: {:?}",
            prog.consts
        );
    }

    /// A `const` whose body rustc prints as a CTFE brace-block must still fold to
    /// its value.
    ///
    /// On rustc 1.85 (the MSRV floor) a constant that folds to a literal prints as
    /// `const K: u8 = { … _0 = const 7_u8; … }` rather than the inline
    /// `const K: u8 = const 7_u8;` the current stable prints. The literal is the
    /// assignment to the return place `_0`, and reading it keeps the item so a
    /// contract that names it resolves -- otherwise the same contract is readable
    /// on stable and unreadable on the MSRV, which is the kind of toolchain-shaped
    /// gap this front end exists to avoid.
    #[test]
    fn a_ctfe_brace_block_const_folds_to_its_literal() {
        let dump = "const K: u8 = {\n    let mut _0: u8;\n\n    bb0: {\n        \
                    _0 = const 7_u8;\n        return;\n    }\n}\n\
                    fn reads() -> u8 {\n    let mut _0: u8;\n\n    bb0: {\n        \
                    _0 = const K;\n        return;\n    }\n}\n";
        let prog = parse_program(dump);
        assert_eq!(
            prog.consts.get("K"),
            Some(&Const::UInt(7, Some(Ty::U8))),
            "a CTFE brace-block `const` must fold to its `_0` literal: {:?}",
            prog.consts
        );
        // A block that *computes* its value is now interpreted concretely: the
        // checked add folds to `3 + 4`, and the item is recorded rather than
        // dropped, so a contract that names it decides. The value is the folded
        // result, not a guess -- the body's own `assert(!overflow)` is checked.
        let computed = "const C: u8 = {\n    let mut _0: u8;\n    let mut _1: (u8, bool);\n\n    \
                        bb0: {\n        _1 = AddWithOverflow(const 3_u8, const 4_u8);\n        \
                        assert(!move (_1.1: bool), \"x\", const 3_u8, const 4_u8) -> \
                        [success: bb1, unwind continue];\n    }\n\n    bb1: {\n        \
                        _0 = move (_1.0: u8);\n        return;\n    }\n}\n\
                        fn reads() -> u8 {\n    let mut _0: u8;\n\n    bb0: {\n        \
                        _0 = const C;\n        return;\n    }\n}\n";
        let prog = parse_program(computed);
        assert_eq!(
            prog.consts.get("C"),
            Some(&Const::UInt(7, Some(Ty::U8))),
            "a computed const body folds to its value: {:?}",
            prog.consts
        );
        // A *branching* body must fold to the **taken** arm, not the first arm in
        // textual order. `if false { 7 } else { 8 }` is 8, and bb1 (which holds 7)
        // prints first: folding the first arm would store 7 and certify a claim
        // about a value the constant never has. Following the `switchInt` on the
        // discriminant's actual value is what keeps this honest.
        let branching = "const K: u8 = {\n    let mut _0: u8;\n    let mut _1: bool;\n\n    \
                         bb0: {\n        _1 = const false;\n        switchInt(move _1) -> [0: bb2, \
                         otherwise: bb1];\n    }\n\n    bb1: {\n        _0 = const 7_u8;\n        \
                         goto -> bb3;\n    }\n\n    bb2: {\n        _0 = const 8_u8;\n        \
                         goto -> bb3;\n    }\n\n    bb3: {\n        return;\n    }\n}\n\
                         fn reads() -> u8 {\n    let mut _0: u8;\n\n    bb0: {\n        \
                         _0 = const K;\n        return;\n    }\n}\n";
        let prog = parse_program(branching);
        assert_eq!(
            prog.consts.get("K"),
            Some(&Const::UInt(8, Some(Ty::U8))),
            "a branching const body folds to the taken arm: {:?}",
            prog.consts
        );
    }

    /// The folder refuses every shape it cannot interpret exactly, and each
    /// refusal leaves the item out of the table (an unreadable name at a use
    /// site), never a guessed value.
    ///
    /// This is the soundness half of [`a_ctfe_brace_block_const_folds_to_its_literal`]:
    /// the folder *does* fold expressions, so what it must not do is fold one it
    /// did not fully understand. A call, a non-literal operand, a place with a
    /// subscript, and a failed `assert` are the four ways a `const` body can leave
    /// the modelled subset, and each is asserted here.
    #[test]
    fn a_const_body_outside_the_modelled_subset_is_refused_not_guessed() {
        let reads = "fn reads() -> u8 {\n    let mut _0: u8;\n\n    bb0: {\n        \
                     _0 = const C;\n        return;\n    }\n}\n";
        // A call in the body: the callee's value is not a literal here, so the
        // item cannot be folded.
        let call = format!(
            "const C: u8 = {{\n    let mut _0: u8;\n\n    bb0: {{\n        \
             _0 = helper(const 1_u8) -> [return: bb1, unwind continue];\n    }}\n\n    \
             bb1: {{\n        return;\n    }}\n}}\n{reads}"
        );
        assert!(!parse_program(&call).consts.contains_key("C"), "a call body is refused");

        // A path the folder has not resolved, used as an operand of an operation:
        // the operand is not a literal, so the item is refused. (A bare
        // `_0 = const OTHER` is read by the older literal path, not the folder, so
        // the path is put inside an operation to reach the folder.)
        let unknown = format!(
            "const C: u8 = {{\n    let mut _0: u8;\n\n    bb0: {{\n        \
             _0 = Add(const OTHER, const 1_u8);\n        return;\n    }}\n}}\n{reads}"
        );
        assert!(
            !parse_program(&unknown).consts.contains_key("C"),
            "an unresolved path operand is refused"
        );

        // A place with a *subscript* has no key in the folder's store, so the read
        // is refused rather than taken from the wrong slot.
        let subscript = format!(
            "const C: u8 = {{\n    let mut _0: u8;\n    let mut _1: [u8; 2];\n\n    bb0: {{\n        \
             _0 = _1[0];\n        return;\n    }}\n}}\n{reads}"
        );
        assert!(
            !parse_program(&subscript).consts.contains_key("C"),
            "a subscripted read is refused"
        );

        // A failed `assert`: rustc would not emit a const whose check fails, so a
        // failure means the body is not the shape the folder understands. Folding
        // past it would store a value the constant never had.
        let failing_assert = format!(
            "const C: u8 = {{\n    let mut _0: u8;\n\n    bb0: {{\n        \
             _0 = const 3_u8;\n        assert(const false, \"x\") -> [success: bb1, unwind continue];\n    }}\n\n    \
             bb1: {{\n        return;\n    }}\n}}\n{reads}"
        );
        assert!(
            !parse_program(&failing_assert).consts.contains_key("C"),
            "a failed assert is refused"
        );

        // The control: the same shape with a *satisfied* assert folds, so the
        // refusals above are about the shapes and not about the harness.
        let ok = format!(
            "const C: u8 = {{\n    let mut _0: u8;\n\n    bb0: {{\n        \
             _0 = const 3_u8;\n        assert(const true, \"x\") -> [success: bb1, unwind continue];\n    }}\n\n    \
             bb1: {{\n        return;\n    }}\n}}\n{reads}"
        );
        assert_eq!(
            parse_program(&ok).consts.get("C"),
            Some(&Const::UInt(3, Some(Ty::U8))),
            "a satisfied assert folds"
        );
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

    /// A `str` literal is decoded; anything else is refused.
    ///
    /// The refusal is the load-bearing half: a path constant
    /// (`core::num::MAX`) reaching the string reader must not become a message,
    /// and an escape the printer does not emit must not be silently dropped.
    #[test]
    fn a_string_literal_is_decoded_and_a_non_literal_is_refused() {
        assert_eq!(parse_str_literal(r#""zero""#).as_deref(), Some("zero"));
        assert_eq!(parse_str_literal(r#""a\"b\n""#).as_deref(), Some("a\"b\n"));
        assert_eq!(parse_str_literal(r#""\u{1f600}""#).as_deref(), Some("\u{1f600}"));
        assert_eq!(parse_str_literal("core::num::MAX"), None);
        assert_eq!(parse_str_literal(r#""\q""#), None, "an unknown escape is refused");
        assert_eq!(parse_str_literal("\"unterminated"), None);
    }

    /// A byte-string literal decodes to raw bytes, not to UTF-8 text.
    #[test]
    fn a_byte_string_literal_decodes_to_raw_bytes() {
        assert_eq!(parse_byte_str_literal(r#"b"\x04bad \xc0\x00""#).as_deref(), Some(&[
            0x04, b'b', b'a', b'd', b' ', 0xC0, 0x00,
        ][..]));
        assert_eq!(parse_byte_str_literal("b\"\"").as_deref(), Some(&[][..]));
        assert_eq!(parse_byte_str_literal("\"not bytes\""), None);
    }

    /// The `new::<LEN, _>` byte template decodes to the same pieces `new_v1`
    /// passes, and a malformed one is refused rather than guessed at.
    #[test]
    fn the_byte_template_decodes_to_the_same_pieces_as_new_v1() {
        // `panic!("bad {}", x)`, as stable prints it.
        let pieces = decode_format_template(&[0x04, b'b', b'a', b'd', b' ', 0xC0, 0x00]);
        assert_eq!(pieces.as_deref(), Some(&["bad ".to_string(), String::new()][..]));
        // `panic!("fmt {} and {}", x, y)`.
        let mut t = vec![0x04];
        t.extend_from_slice(b"fmt ");
        t.push(0xC0);
        t.push(0x05);
        t.extend_from_slice(b" and ");
        t.push(0xC0);
        t.push(0x00);
        let pieces = decode_format_template(&t).expect("a well-formed template");
        assert_eq!(pieces, vec!["fmt ".to_string(), " and ".to_string(), String::new()]);
        // A template that never terminates is refused.
        assert_eq!(decode_format_template(&[0x04, b'a']), None);
    }

    /// The placeholder count comes from the argument count, not the piece count.
    ///
    /// `panic!("{} tail", x)` prints `["", " tail"]` with *one* argument, so a
    /// join that put a `{}` in every gap would claim two placeholders and name a
    /// message that is not the one in the source.
    #[test]
    fn the_placeholder_count_follows_the_argument_count() {
        let pieces = |v: &[&str]| v.iter().map(|s| s.to_string()).collect::<Vec<_>>();
        assert_eq!(join_format_pieces(&pieces(&["plain"]), 0), "plain");
        assert_eq!(join_format_pieces(&pieces(&["", " tail"]), 1), "{} tail");
        assert_eq!(join_format_pieces(&pieces(&["a", "b"]), 1), "a{}b");
        assert_eq!(join_format_pieces(&pieces(&["a", "b", "c"]), 2), "a{}b{}c");
        // A leading argument (`panic!("{}{}", x, y)`) is `["", "", ""]` with two
        // arguments, which the gap rule alone would render as three placeholders.
        assert_eq!(join_format_pieces(&pieces(&["", "", ""]), 2), "{}{}");
        assert_eq!(join_format_pieces(&pieces(&[]), 3), "");
    }
}

