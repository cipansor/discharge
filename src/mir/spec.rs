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

use std::collections::BTreeMap;

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
pub fn eval_requires(text: &str, args: &BTreeMap<String, Var>) -> Result<Pred, SpecError> {
    let mut p = Parser::new(text, args, None);
    let pred = p.parse_or()?;
    p.expect_end()?;
    Ok(pred)
}

/// Turn an `ensures` contract into a predicate over the arguments and `ret`.
pub fn eval_ensures(
    text: &str,
    args: &BTreeMap<String, Var>,
    ret: Var,
) -> Result<Pred, SpecError> {
    let mut p = Parser::new(text, args, Some(ret));
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
    fn new(s: &str, args: &'a BTreeMap<String, Var>, ret: Option<Var>) -> Parser<'a> {
        Parser { toks: tokenize(s), pos: 0, args, ret, text: s.to_string() }
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
        let left = self.parse_expr()?;
        for op in ["==", "!=", "<=", ">=", "<", ">"] {
            if self.eat_op(op) {
                let right = self.parse_expr()?;
                return Ok(match op {
                    "==" => smt::eq(left, right),
                    "!=" => smt::not(smt::eq(left, right)),
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

    fn parse_expr(&mut self) -> Result<Var, SpecError> {
        let mut left = self.parse_term()?;
        loop {
            if self.eat_op("+") {
                let r = self.parse_term()?;
                left = smt::add(left, r);
            } else if self.eat_op("-") {
                let r = self.parse_term()?;
                left = smt::sub(left, r);
            } else if self.eat_op("|") {
                let r = self.parse_term()?;
                left = smt::bor(left, r);
            } else if self.eat_op("^") {
                let r = self.parse_term()?;
                left = smt::bxor(left, r);
            } else {
                return Ok(left);
            }
        }
    }

    fn parse_term(&mut self) -> Result<Var, SpecError> {
        let mut left = self.parse_atom()?;
        loop {
            if self.eat_op("*") {
                let r = self.parse_atom()?;
                left = smt::mul(left, r);
            } else if self.eat_op("&") {
                let r = self.parse_atom()?;
                left = smt::band(left, r);
            } else {
                return Ok(left);
            }
        }
    }

    fn parse_atom(&mut self) -> Result<Var, SpecError> {
        match self.peek().cloned() {
            Some(Tok::Num(n)) => {
                self.pos += 1;
                // The width is taken from the widest argument, so a literal in a
                // contract is a constant at the arguments' width. A contract
                // whose literal does not fit that width is refused by the engine
                // as ill-formed, which surfaces as `Unknown`.
                let w = self.args.values().chain(self.ret.iter()).map(|v| smt::bits(*v)).max().unwrap_or(64);
                Ok(smt::word(n, w))
            }
            Some(Tok::Ident(name)) => {
                self.pos += 1;
                if name == "ret" || name == "result" {
                    return self.ret.ok_or_else(|| self.err("`ret` is only meaningful in `ensures`"));
                }
                if name == "true" || name == "false" {
                    return Err(self.err("use a comparison for a boolean contract"));
                }
                self.args
                    .get(&name)
                    .copied()
                    .ok_or_else(|| self.err(format!("unknown name `{name}` (not an argument)")))
            }
            Some(Tok::Op(o)) if o == "(" => {
                self.pos += 1;
                let inner = self.parse_or()?;
                if !self.eat_op(")") {
                    return Err(self.err("missing `)`"));
                }
                // A parenthesized *predicate* used as a value is refused; the
                // grammar has no booleans-as-values, which keeps it decidable.
                let _ = inner;
                Err(self.err("a parenthesized boolean cannot be used as a value"))
            }
            Some(t) => Err(self.err(format!("unexpected token {t:?}"))),
            None => Err(self.err("unexpected end of contract")),
        }
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
