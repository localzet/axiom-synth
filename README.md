# axiom-synth

A deterministic enumerative synthesizer. It searches a small expression grammar and emits the first `AXIOM-PROGRAM/1`
candidate satisfying every postcondition across the declared finite domain.

> **Maturity:** research prototype v0.1. The default verifier proves properties by exhaustive evaluation over an
> explicitly finite input domain. A VALID receipt is therefore a theorem about that bounded model, not a claim of
> unbounded program correctness.


The important architectural rule is already present: **the synthesizer is untrusted**. A candidate must still pass
`axiom-verifier` before `axiom-runtime` accepts it.

```bash
cargo run -- synth spec.aix --out candidate.axp --max-depth 3
```
