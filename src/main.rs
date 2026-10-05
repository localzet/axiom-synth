// SPDX-FileCopyrightText: 2026 Ivan Zorin <creator@localzet.com> (Localzet contributions)
// SPDX-License-Identifier: MIT
use anyhow::{bail, Context, Result};
use std::{collections::HashSet, env, fmt, fs};

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
            Self::Const(value) => *value,
            Self::Neg(inner) => inner.eval(x).wrapping_neg(),
            Self::Add(left, right) => left.eval(x).wrapping_add(right.eval(x)),
            Self::Sub(left, right) => left.eval(x).wrapping_sub(right.eval(x)),
            Self::IfNeg(negative, nonnegative) => {
                if x < 0 {
                    negative.eval(x)
                } else {
                    nonnegative.eval(x)
                }
            }
        }
    }

    fn cost(&self) -> usize {
        match self {
            Self::X | Self::Const(_) => 1,
            Self::Neg(inner) => 1 + inner.cost(),
            Self::Add(left, right) | Self::Sub(left, right) => 1 + left.cost() + right.cost(),
            Self::IfNeg(left, right) => 2 + left.cost() + right.cost(),
        }
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::X => write!(f, "x"),
            Self::Const(value) => write!(f, "{value}"),
            Self::Neg(inner) => write!(f, "(-{inner})"),
            Self::Add(left, right) => write!(f, "({left} + {right})"),
            Self::Sub(left, right) => write!(f, "({left} - {right})"),
            Self::IfNeg(left, right) => write!(f, "if x < 0 then {left} else {right}"),
        }
    }
}

fn main() -> Result<()> {
    let mut args = env::args().skip(1);
    if args.next().as_deref() != Some("synth") {
        bail!("usage: axiom-synth synth spec.aix --examples examples.axexamples --out candidate.axp [--max-depth N]");
    }
    let spec_path = args.next().context("missing spec.aix")?;
    if args.next().as_deref() != Some("--examples") {
        bail!("expected --examples");
    }
    let examples_path = args.next().context("missing examples file")?;
    if args.next().as_deref() != Some("--out") {
        bail!("expected --out");
    }
    let out_path = args.next().context("missing output path")?;

    let mut max_depth = 3usize;
    if let Some(flag) = args.next() {
        if flag != "--max-depth" {
            bail!("unexpected flag: {flag}");
        }
        max_depth = args.next().context("missing depth")?.parse()?;
    }

    let spec = fs::read_to_string(spec_path)?;
    let module = parse_value(&spec, "module")?.to_owned();
    let examples = parse_examples(&fs::read_to_string(examples_path)?)?;
    let candidate = synthesize(&examples, max_depth).context("no candidate found")?;
    fs::write(out_path, emit_program(&module, &candidate))?;
    println!("synthesized: {candidate} (cost={})", candidate.cost());
    Ok(())
}

fn synthesize(examples: &[(i64, i64)], max_depth: usize) -> Option<Expr> {
    let mut universe = vec![Expr::X, Expr::Const(-1), Expr::Const(0), Expr::Const(1)];
    let mut signatures: HashSet<Vec<i64>> = HashSet::new();

    for depth in 0..=max_depth {
        universe.sort_by_key(Expr::cost);
        for expr in universe.clone() {
            let signature: Vec<_> = examples.iter().map(|(x, _)| expr.eval(*x)).collect();
            if !signatures.insert(signature) {
                continue;
            }
            if examples
                .iter()
                .all(|(x, expected)| expr.eval(*x) == *expected)
            {
                return Some(expr);
            }
        }

        if depth == max_depth {
            break;
        }
        let base = universe.clone();
        for inner in &base {
            universe.push(Expr::Neg(Box::new(inner.clone())));
        }
        for left in &base {
            for right in &base {
                if left.cost() + right.cost() > 8 {
                    continue;
                }
                universe.push(Expr::Add(Box::new(left.clone()), Box::new(right.clone())));
                universe.push(Expr::Sub(Box::new(left.clone()), Box::new(right.clone())));
                universe.push(Expr::IfNeg(Box::new(left.clone()), Box::new(right.clone())));
            }
        }
        universe.sort_by_key(Expr::cost);
        universe.truncate(20_000);
    }
    None
}

fn parse_examples(raw: &str) -> Result<Vec<(i64, i64)>> {
    let mut lines = raw.lines();
    if lines.next() != Some("AXIOM-EXAMPLES/1") {
        bail!("bad examples header");
    }
    let mut out = Vec::new();
    for line in lines.filter(|line| !line.trim().is_empty()) {
        let mut x = None;
        let mut result = None;
        for field in line.split(',') {
            let (key, value) = field.split_once('=').context("bad example field")?;
            match key.trim() {
                "x" => x = Some(value.trim().parse()?),
                "result" => result = Some(value.trim().parse()?),
                _ => bail!("unknown example key: {key}"),
            }
        }
        out.push((
            x.context("example misses x")?,
            result.context("example misses result")?,
        ));
    }
    Ok(out)
}

fn parse_value<'a>(raw: &'a str, key: &str) -> Result<&'a str> {
    raw.lines()
        .find_map(|line| line.strip_prefix(&format!("{key}=")))
        .context("missing key")
}

fn emit_program(module: &str, expr: &Expr) -> String {
    let mut code = Vec::new();
    let register = compile(expr, &mut code);
    code.push(format!("RETURN r{register}"));
    format!(
        "AXIOM-PROGRAM/2\nmodule={module}\ninputs=x\noutput=result\ncapabilities=\nsource.expr={expr}\ncode:\n{}\nend\n",
        code.join("\n")
    )
}

fn compile(expr: &Expr, code: &mut Vec<String>) -> usize {
    match expr {
        Expr::X => {
            let dest = next_register(code);
            code.push(format!("LOAD_INPUT r{dest} x"));
            dest
        }
        Expr::Const(value) => {
            let dest = next_register(code);
            code.push(format!("CONST r{dest} {value}"));
            dest
        }
        Expr::Neg(inner) => {
            let source = compile(inner, code);
            let dest = next_register(code);
            code.push(format!("NEG r{dest} r{source}"));
            dest
        }
        Expr::Add(left, right) => {
            let left = compile(left, code);
            let right = compile(right, code);
            let dest = next_register(code);
            code.push(format!("ADD r{dest} r{left} r{right}"));
            dest
        }
        Expr::Sub(left, right) => {
            let left = compile(left, code);
            let right = compile(right, code);
            let dest = next_register(code);
            code.push(format!("SUB r{dest} r{left} r{right}"));
            dest
        }
        Expr::IfNeg(negative, nonnegative) => {
            let negative = compile(negative, code);
            let nonnegative = compile(nonnegative, code);
            let dest = next_register(code);
            code.push(format!(
                "SELECT_NEG_INPUT r{dest} x r{negative} r{nonnegative}"
            ));
            dest
        }
    }
}

fn next_register(code: &[String]) -> usize {
    code.iter()
        .flat_map(|line| line.split_whitespace())
        .filter_map(|word| word.strip_prefix('r'))
        .filter_map(|number| number.parse::<usize>().ok())
        .max()
        .map(|number| number + 1)
        .unwrap_or(0)
}

#[cfg(test)]
mod tests {
    use super::synthesize;

    #[test]
    fn fits_examples_without_proving_generalization() {
        let candidate = synthesize(&[(0, 0), (-1, 1), (1, 1)], 3).unwrap();
        for (input, output) in [(0, 0), (-1, 1), (1, 1)] {
            assert_eq!(candidate.eval(input), output);
        }
        // Finite examples admit cheaper candidates that overfit.
        assert_ne!(candidate.eval(-7), 7);
    }
}
