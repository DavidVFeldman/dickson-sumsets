# Dickson's conjecture and infinite multidimensional sum-sets within the primes

Paper and Lean 4 formalization.

**D. Feldman and R. Impagliazzo.**

Assuming Dickson's conjecture, for every prime `p` and every `n` with
`1 ≤ n ≤ p - 2` the set of primes contains a sum-set
`{p} + E_0 + ... + E_n` with each `E_i` an infinite set of even numbers
containing `0`.  Unconditionally, no such configuration exists once
`n ≥ p - 1`.  The threshold is therefore sharp.

## Contents

- `paper/` — the manuscript (`dickson_sumsets.tex`, `dickson_sumsets.pdf`).
- `RequestProject/` — the Lean 4 formalization.
  - `Main.lean` — Dickson's conjecture as a `Prop`; the unconditional
    impossibility result (Proposition 2) and its pigeonhole lemma.
  - `MainTheorem.lean` — the conditional main theorem (Theorem 1) and
    the supporting residue, chain-limit, and infinitude lemmas.
  - `Construction.lean` — the greedy construction: critical values,
    births, the residue discipline, confinement, and the step lemma.
- `axiom_check.lean`, `VERIFY.md` — how to reproduce the verification.
- `VALIDATION_REPORT.md` — the formalization report.

## Verification

Both principal results are machine-checked.  Dickson's conjecture is an
explicit hypothesis of the conditional statement, never an axiom, so the
axiom footprint of the whole development is `propext`,
`Classical.choice`, `Quot.sound`.

    lake build
    lake env lean axiom_check.lean

See `VERIFY.md` for details.

## Acknowledgment

The formalization was carried out with Aristotle (Harmonic) in
collaboration with Claude (Anthropic).

## License

Apache License 2.0.
