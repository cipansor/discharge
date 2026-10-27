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
    Unit,
    /// A shared or mutable reference. Modelled as its referent's width, because
    /// the frontend does not track aliasing (see the module docs on scope).
    Ref(Box<Ty>),
    /// Anything else: structs, enums, slices, `!`, …
    Other(String),
}

impl Ty {
    /// Bit width, when the type is a bit-vector or boolean.
    pub fn width(&self) -> Option<u8> {
        Some(match self {
            Ty::Bool => 1,
            Ty::U8 => 8,
            Ty::U16 => 16,
            Ty::U32 => 32,
            Ty::U64 | Ty::Usize => 64,
            Ty::U128 => 128,
            Ty::I8 => 8,
            Ty::I16 => 16,
            Ty::I32 => 32,
            Ty::I64 | Ty::Isize => 64,
            Ty::I128 => 128,
            _ => return None,
        })
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
        }
        Ty::Other(s.to_string())
    }
}

/// A projection out of a place: `_3.1` is `Field(1)`, `_2[0]` is `Index(0)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Proj {
    Field(u32),
    Index(u64),
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
    /// `&place`
    Ref(Place),
    /// `Len(place)` — array length.
    Len(Place),
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
    pub local_names: BTreeMap<LocalIdx, String>,
    pub blocks: Vec<Block>,
}

impl MirFn {
    pub fn ty_of(&self, local: LocalIdx) -> Option<&Ty> {
        self.locals.get(&local)
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

/// Parse a place like `_3.1` or `_2` or `_1.0[0]`.
fn parse_place(s: &str) -> Option<Place> {
    let s = strip_annot(s).trim();
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
    let mut place = Place::new(local);
    let mut rest = &s[i..];
    while !rest.is_empty() {
        if let Some(r) = rest.strip_prefix('.') {
            let n: String = r.chars().take_while(|c| c.is_ascii_digit()).collect();
            if n.is_empty() {
                return None;
            }
            place.proj.push(Proj::Field(n.parse().ok()?));
            rest = &r[n.len()..];
        } else {
            // `?` on `strip_prefix` is the same `None` the old `else { return
            // None }` produced, and it is what lets the index parse fail closed.
            let r = rest.strip_prefix('[')?;
            let close = r.find(']')?;
            let n = r[..close].trim().parse::<u64>().ok()?;
            place.proj.push(Proj::Index(n));
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
fn parse_operand(s: &str) -> Operand {
    let t = s.trim();
    if let Some(r) = t.strip_prefix("copy ") {
        return Operand::Copy(parse_place(r).unwrap_or(Place::new(u32::MAX)));
    }
    if let Some(r) = t.strip_prefix("move ") {
        return Operand::Move(parse_place(r).unwrap_or(Place::new(u32::MAX)));
    }
    if let Some(r) = t.strip_prefix("const ") {
        return Operand::Const(parse_const(r));
    }
    // A bare place, e.g. inside `switchInt(_1)`.
    match parse_place(t) {
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
fn parse_assert(rest: &str) -> Option<(Operand, bool, String, Vec<Operand>, usize)> {
    let (inner, after) = take_until_close(rest)?;
    let parts = split_top_level(inner, ',');
    if parts.is_empty() {
        return None;
    }
    let raw_cond = parts[0].trim();
    let (negated, cond) = match raw_cond.strip_prefix('!') {
        Some(r) => (true, parse_operand(r)),
        None => (false, parse_operand(raw_cond)),
    };
    let mut msg = String::new();
    let mut args = Vec::new();
    if parts.len() > 1 {
        let raw = parts[1].trim();
        msg = unquote(raw);
        for p in &parts[2..] {
            args.push(parse_operand(p));
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
fn parse_rvalue(s: &str) -> Rvalue {
    let t = s.trim();
    // A call is handled by the caller (it is a terminator).
    //
    // The cast check has to come *before* the `const ` check, because rustc prints
    // a cast constant as `const 3_i32 as u32 (IntToInt)`. Matching `const ` first
    // hands the whole string to `parse_const`, which reads `i32 as u32 (IntToInt)`
    // as a type name and produces a constant with no width -- an `Unknown` that
    // then makes every guard written against it unmodelled.
    if let Some(i) = t.find(" as ") {
        let (src, dst) = (t[..i].trim(), t[i + 4..].trim());
        let ty_text = dst.split_whitespace().next().unwrap_or(dst);
        return Rvalue::Cast(parse_operand(src), Ty::parse(ty_text));
    }
    if let Some(rest) = t.strip_prefix("const ") {
        return Rvalue::Use(Operand::Const(parse_const(rest)));
    }
    if t.starts_with("copy ") || t.starts_with("move ") {
        return Rvalue::Use(parse_operand(t));
    }
    // `&_1`, `&mut _1`
    if let Some(r) = t.strip_prefix("&mut ").or_else(|| t.strip_prefix('&')) {
        if let Some(p) = parse_place(r) {
            return Rvalue::Ref(p);
        }
    }
    if let Some(rest) = t.strip_prefix("Len(") {
        if let Some(p) = parse_place(rest.trim_end_matches(')')) {
            return Rvalue::Len(p);
        }
    }
    // An operator call: `Name(args)`.
    if let Some(open) = t.find('(') {
        if t.ends_with(')') {
            let name = t[..open].trim();
            let inner = &t[open + 1..t.len() - 1];
            let args: Vec<Operand> = split_top_level(inner, ',').iter().map(|a| parse_operand(a)).collect();
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
        }
    }
    // An array literal: `[const 1_u32, const 2_u32]`
    if t.starts_with('[') && t.ends_with(']') {
        let inner = &t[1..t.len() - 1];
        let args: Vec<Operand> = split_top_level(inner, ',').iter().map(|a| parse_operand(a)).collect();
        return Rvalue::Aggregate(args);
    }
    // A tuple literal: `(move _5, move _4)`
    if t.starts_with('(') && t.ends_with(')') {
        let inner = &t[1..t.len() - 1];
        if !inner.trim().is_empty() {
            let args: Vec<Operand> =
                split_top_level(inner, ',').iter().map(|a| parse_operand(a)).collect();
            if args.len() > 1 {
                return Rvalue::Aggregate(args);
            }
        }
    }
    Rvalue::Unknown(t.to_string())
}

/// Parse one statement or terminator line.
fn parse_stmt_or_term(line: &str) -> Result<Stmt, Term> {
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
        let discr = parse_operand(inner);
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
        return Err(match parse_assert(r) {
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
            let dest = parse_place(dest_text).unwrap_or(Place::new(u32::MAX));
            if let Some(open) = call.find('(') {
                if call.ends_with(')') {
                    let name = call[..open].trim();
                    let inner = &call[open + 1..call.len() - 1];
                    let args: Vec<Operand> =
                        split_top_level(inner, ',').iter().map(|a| parse_operand(a)).collect();
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
        if let Some(place) = parse_place(dest_text) {
            return Ok(Stmt::Assign(place, parse_rvalue(rhs)));
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
    let lines: Vec<&str> = text.lines().collect();
    let mut prog = MirProgram::default();
    let mut i = 0;
    while i < lines.len() {
        let line = lines[i];
        if let Some((name, args, ret_ty)) = parse_fn_header(line) {
            let mut f = MirFn {
                name,
                arg_locals: args.iter().map(|(l, _)| *l).collect(),
                ret_ty: ret_ty.clone(),
                locals: BTreeMap::new(),
                local_names: BTreeMap::new(),
                blocks: Vec::new(),
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
                        if let Some(idx) = parse_local(p.trim().trim_end_matches(';')) {
                            f.local_names.insert(idx, n.trim().to_string());
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
                    match parse_stmt_or_term(t) {
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
}
