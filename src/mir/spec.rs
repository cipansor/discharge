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

use crate::mir::parse::Ty;
use crate::smt::{self, Pred, Var};

/// A contract attached to a function.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct FnContract {
    /// Raw text of each `#[requires(...)]`, in source order.
    pub requires: Vec<String>,
    /// Raw text of each `#[ensures(...)]`, in source order.
    pub ensures: Vec<String>,
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
            }
            continue;
        }
        // A function item: attach whatever is pending and start fresh. A
        // function with no contract is not recorded, so the set of entries is
        // exactly "the functions that carry a claim" rather than "every function
        // in the file".
        if let Some(name) = fn_name(line) {
            if !pending.requires.is_empty() || !pending.ensures.is_empty() {
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

impl std::fmt::Display for SpecError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "cannot read contract `{}`: {}", self.text, self.reason)
    }
}

/// Turn a `requires` contract into a predicate over the named arguments.
pub fn eval_requires(
    text: &str,
    args: &BTreeMap<String, Var>,
    signed: &BTreeSet<String>,
) -> Result<Pred, SpecError> {
    let mut p = Parser::new(text, args, None, signed, false);
    let pred = p.parse_or()?;
    p.expect_end()?;
    Ok(pred)
}

/// Turn an `ensures` contract into a predicate over the arguments and `ret`.
pub fn eval_ensures(
    text: &str,
    args: &BTreeMap<String, Var>,
    ret: Var,
    signed: &BTreeSet<String>,
    ret_signed: bool,
) -> Result<Pred, SpecError> {
    let mut p = Parser::new(text, args, Some(ret), signed, ret_signed);
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
        Parser { toks: tokenize(s), pos: 0, args, ret, text: s.to_string(), signed, ret_signed }
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
            left = match op {
                "+" => smt::add(left, r),
                "-" => smt::sub(left, r),
                "|" => smt::bor(left, r),
                _ => smt::bxor(left, r),
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
            left = if op == "*" { smt::mul(left, r) } else { smt::band(left, r) };
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
                // The width is taken from the widest argument, so a literal in a
                // contract is a constant at the arguments' width. A contract
                // whose literal does not fit that width is refused by the engine
                // as ill-formed, which surfaces as `Unknown`.
                let w = self.args.values().chain(self.ret.iter()).map(|v| smt::bits(*v)).max().unwrap_or(64);
                Ok((smt::word(n, w), false))
            }
            Some(Tok::Ident(name)) => {
                self.pos += 1;
                if name == "ret" || name == "result" {
                    let v = self.ret.ok_or_else(|| self.err("`ret` is only meaningful in `ensures`"))?;
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
                    if let Some(k) = type_bound(&ty, &a) {
                        let w = self.args.values().chain(self.ret.iter()).map(|v| smt::bits(*v)).max().unwrap_or(64);
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
fn type_bound(ty: &str, assoc: &str) -> Option<u64> {
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
    match assoc {
        "MAX" if signed => Some((1u64 << (bits - 1)) - 1),
        "MAX" => Some(if bits == 64 { u64::MAX } else { (1u64 << bits) - 1 }),
        // `MIN` for a signed type is the most negative value, which as a bit
        // pattern is the top bit alone.
        "MIN" if signed => Some(1u64 << (bits - 1)),
        "MIN" => Some(0),
        _ => None,
    }
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
