import RequestProject.Main
import RequestProject.MainTheorem

/-! Run with `lake env lean axiom_check.lean`.  Each line prints the
axioms a declaration depends on; all should show only `propext`,
`Classical.choice`, `Quot.sound`. -/

#print axioms DicksonSumsets.no_prime_anchored_box_at_dimension_p
#print axioms DicksonSumsets.no_prime_anchored_box_of_card_ge
#print axioms DicksonSumsets.exists_good_residue
#print axioms DicksonSumsets.Construction.bounded_prime_finite_sums_sequence_exists'
#print axioms DicksonSumsets.bounded_prime_finite_sums_sequence_exists
#print axioms DicksonSumsets.finite_prime_box_chain_exists
#print axioms DicksonSumsets.prime_anchored_box_exists
#print axioms DicksonSumsets.prime_anchored_box_exists_some_prime
