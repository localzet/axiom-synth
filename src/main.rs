use anyhow::{bail, Context, Result};
use std::{
    collections::{BTreeMap, HashSet},
    env, fmt, fs,
};

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
enum Expr {
    X,
    Const(i64),
    Neg(Box<Expr>),
    Add(Box<Expr>, Box<Expr>),
    Sub(Box<Expr>, Box<Expr>),
    IfNeg(Box<Expr>, Box<Expr>),
}
impl Expr {
    fn eval(&self, x: i64) -> i64 {
        match self {
            Self::X => x,
            Self::Const(v) => *v,
            Self::Neg(a) => a.eval(x).wrapping_neg(),
            Self::Add(a, b) => a.eval(x).wrapping_add(b.eval(x)),
            Self::Sub(a, b) => a.eval(x).wrapping_sub(b.eval(x)),
            Self::IfNeg(a, b) => {
                if x < 0 {
                    a.eval(x)
                } else {
                    b.eval(x)
                }
            }
        }
    }
    fn cost(&self) -> usize {
        match self {
            Self::X | Self::Const(_) => 1,
            Self::Neg(a) => 1 + a.cost(),
            Self::Add(a, b) | Self::Sub(a, b) => 1 + a.cost() + b.cost(),
            Self::IfNeg(a, b) => 2 + a.cost() + b.cost(),
        }
    }
}
impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::X => write!(f, "x"),
            Self::Const(v) => write!(f, "{v}"),
            Self::Neg(a) => write!(f, "(-{a})"),
            Self::Add(a, b) => write!(f, "({a}+{b})"),
            Self::Sub(a, b) => write!(f, "({a}-{b})"),
            Self::IfNeg(a, b) => write!(f, "if x<0 {{{a}}} else {{{b}}}"),
        }
    }
}

fn main() -> Result<()> {
    let mut args = env::args().skip(1);
    if args.next().as_deref() != Some("synth") {
        bail!("usage: axiom-synth synth spec.aix --out candidate.axp [--max-depth N]");
    }
    let spec_path = args.next().context("missing spec.aix")?;
    if args.next().as_deref() != Some("--out") {
        bail!("expected --out");
    }
    let out = args.next().context("missing output path")?;
    let mut max_depth = 3usize;
    if let Some(flag) = args.next() {
        if flag != "--max-depth" {
            bail!("unexpected flag {flag}");
        }
        max_depth = args.next().context("missing depth")?.parse()?;
    }
    let doc = parse_ir(&fs::read_to_string(spec_path)?)?;
    let min: i64 = doc["domain.min"].parse()?;
    let max: i64 = doc["domain.max"].parse()?;
    let clauses = ensures(&doc);
    let mut universe = vec![Expr::X, Expr::Const(-1), Expr::Const(0), Expr::Const(1)];
    let mut seen: HashSet<Vec<i64>> = HashSet::new();
    let mut best = None;
    for depth in 0..=max_depth {
        let current = universe.clone();
        for e in &current {
            let signature: Vec<i64> = (min..=max).map(|x| e.eval(x)).collect();
            if !seen.insert(signature) {
                continue;
            }
            if (min..=max).all(|x| {
                clauses
                    .iter()
                    .all(|c| eval_bool(c, x, e.eval(x)).unwrap_or(false))
            }) {
                best = Some(e.clone());
                break;
            }
        }
        if best.is_some() {
            break;
        }
        if depth == max_depth {
            break;
        }
        let base = universe.clone();
        for a in &base {
            universe.push(Expr::Neg(Box::new(a.clone())));
        }
        for a in &base {
            for b in &base {
                if a.cost() + b.cost() <= 8 {
                    universe.push(Expr::Add(Box::new(a.clone()), Box::new(b.clone())));
                    universe.push(Expr::Sub(Box::new(a.clone()), Box::new(b.clone())));
                    universe.push(Expr::IfNeg(Box::new(a.clone()), Box::new(b.clone())));
                }
            }
        }
        universe.sort_by_key(Expr::cost);
        universe.truncate(10000);
    }
    let e = best.context("no satisfying program found within search bound")?;
    fs::write(out, emit_program(&doc, &e))?;
    println!("synthesized: {e} (cost={})", e.cost());
    Ok(())
}

fn emit_program(doc: &BTreeMap<String, String>, e: &Expr) -> String {
    let mut code = Vec::new();
    let reg = compile(e, &mut code);
    code.push(format!("RETURN r{reg}"));
    format!(
        "AXIOM-PROGRAM/1\nmodule={}\ncapabilities=\nsource_expr={}\ncode:\n{}\nend\n",
        doc["module"],
        e,
        code.join("\n")
    )
}
fn compile(e: &Expr, code: &mut Vec<String>) -> usize {
    match e {
        Expr::X => {
            let r = next_reg(code);
            code.push(format!("LOAD_INPUT r{r} x"));
            r
        }
        Expr::Const(v) => {
            let r = next_reg(code);
            code.push(format!("CONST r{r} {v}"));
            r
        }
        Expr::Neg(a) => {
            let x = compile(a, code);
            let r = next_reg(code);
            code.push(format!("NEG r{r} r{x}"));
            r
        }
        Expr::Add(a, b) => {
            let x = compile(a, code);
            let y = compile(b, code);
            let r = next_reg(code);
            code.push(format!("ADD r{r} r{x} r{y}"));
            r
        }
        Expr::Sub(a, b) => {
            let x = compile(a, code);
            let y = compile(b, code);
            let r = next_reg(code);
            code.push(format!("SUB r{r} r{x} r{y}"));
            r
        }
        Expr::IfNeg(a, b) => {
            let x = compile(a, code);
            let y = compile(b, code);
            let r = next_reg(code);
            code.push(format!("SELECT_NEG r{r} r{x} r{y}"));
            r
        }
    }
}
fn next_reg(code: &[String]) -> usize {
    code.iter()
        .filter_map(|l| l.split_whitespace().nth(1))
        .filter_map(|r| r.strip_prefix('r'))
        .filter_map(|n| n.parse::<usize>().ok())
        .max()
        .map(|n| n + 1)
        .unwrap_or(0)
}
fn parse_ir(raw: &str) -> Result<BTreeMap<String, String>> {
    let mut it = raw.lines();
    if it.next() != Some("AXIOM-IR/1") {
        bail!("bad IR header");
    }
    let mut m = BTreeMap::new();
    for l in it.filter(|l| !l.trim().is_empty()) {
        let (k, v) = l.split_once('=').context("bad IR line")?;
        m.insert(k.to_owned(), v.to_owned());
    }
    Ok(m)
}
fn ensures(doc: &BTreeMap<String, String>) -> Vec<String> {
    doc.iter()
        .filter(|(k, _)| k.starts_with("ensures."))
        .map(|(_, v)| v.clone())
        .collect()
}
fn eval_bool(expr: &str, x: i64, result: i64) -> Result<bool> {
    let e = expr.trim();
    if let Some((a, b)) = split_top(e, "||") {
        return Ok(eval_bool(a, x, result)? || eval_bool(b, x, result)?);
    }
    if let Some((a, b)) = split_top(e, "&&") {
        return Ok(eval_bool(a, x, result)? && eval_bool(b, x, result)?);
    }
    for op in ["==", "!=", ">=", "<=", ">", "<"] {
        if let Some((a, b)) = split_top(e, op) {
            let a = eval_int(a, x, result)?;
            let b = eval_int(b, x, result)?;
            return Ok(match op {
                "==" => a == b,
                "!=" => a != b,
                ">=" => a >= b,
                "<=" => a <= b,
                ">" => a > b,
                "<" => a < b,
                _ => unreachable!(),
            });
        }
    }
    if e == "true" {
        return Ok(true);
    }
    if e == "false" {
        return Ok(false);
    }
    bail!("unsupported clause: {e}")
}
fn eval_int(expr: &str, x: i64, result: i64) -> Result<i64> {
    let e = expr.trim().trim_matches(|c| c == '(' || c == ')').trim();
    match e {
        "x" => Ok(x),
        "result" => Ok(result),
        "-x" => Ok(x.wrapping_neg()),
        _ => Ok(e.parse()?),
    }
}
fn split_top<'a>(expr: &'a str, op: &str) -> Option<(&'a str, &'a str)> {
    let mut depth = 0i32;
    let b = expr.as_bytes();
    let o = op.as_bytes();
    let mut i = 0;
    while i + o.len() <= b.len() {
        match b[i] as char {
            '(' => depth += 1,
            ')' => depth -= 1,
            _ => {}
        }
        if depth == 0 && &b[i..i + o.len()] == o {
            return Some((&expr[..i], &expr[i + o.len()..]));
        }
        i += 1;
    }
    None
}
