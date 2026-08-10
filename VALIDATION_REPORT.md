# Validation report

## Completion status

The requested development is complete (100%). The remaining proof of
`bounded_prime_finite_sums_sequence_exists` is now supplied through the
history-sensitive construction in `RequestProject/Construction.lean`, and the
original theorem contracts in `RequestProject/MainTheorem.lean` are unchanged.

The construction preserves the five specified design decisions: urgency uses
the `card + 1` threshold; `res` is the least good residue; the room invariant
uses the e-independent doubled critical-value bound; birth stability is proved
explicitly and used by the discipline invariant; and empty subsets contribute
the anchor `p`.

## Machine-checked results

A full `lake build` completed successfully, including both
`RequestProject.Construction` and `RequestProject.MainTheorem`.

The following declarations were separately checked and have exactly the axiom
footprint shown below:

- `DicksonSumsets.Construction.bounded_prime_finite_sums_sequence_exists'`
- `DicksonSumsets.bounded_prime_finite_sums_sequence_exists`
- `DicksonSumsets.finite_prime_box_chain_exists`
- `DicksonSumsets.exists_good_residue`
- `DicksonSumsets.primeAnchoredBox_iUnion`
- `DicksonSumsets.infinite_iUnion_of_unbounded_card`
- `DicksonSumsets.prime_anchored_box_exists`
- `DicksonSumsets.prime_anchored_box_exists_some_prime`

Permitted axioms used:

- `propext`
- `Classical.choice`
- `Quot.sound`

No other axioms occur in those theorem footprints. `DicksonConjecture` remains
an explicit theorem hypothesis and was not introduced as an axiom.

A source scan found no proof placeholders (`sorry` or `admit`), no
`native_decide`, no `implemented_by`, and no added axiom declarations in the
Lean sources. `RequestProject/Main.lean`, including its unconditional
Proposition 2 development, was not weakened or modified.

## Audited material

The explanatory correspondence between the Lean bookkeeping and the paper's
prose proof—birth times, critical values, urgent primes, CRT residue choices,
confinement, Dickson admissibility, and recursive assembly—was reviewed while
integrating the supplied skeleton. This prose-level correspondence is an audit;
the formal declarations and dependencies listed above are machine-checked.

The build emits only non-fatal style/deprecation linter warnings; it emits no
errors and no warning that a declaration uses `sorry`.
