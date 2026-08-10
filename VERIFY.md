# Local verification (one machine, three commands)

The only unverifiable claim in this archive is Aristotle's build
attestation.  To replace trust with a check, on any machine with
elan installed:

    cd dickson_sumsets_verified
    lake build                       # fetches pinned Mathlib; no errors, no sorry warnings
    grep -rn "sorry\|admit\|native_decide" RequestProject/*.lean   # prose hits only
    lake env lean axiom_check.lean   # prints axiom footprints

Expected output of the last command: each declaration lists exactly
`propext`, `Classical.choice`, `Quot.sound` — and
`DicksonSumsets.no_prime_anchored_box_at_dimension_p` (the
unconditional Proposition 2) must NOT list `DicksonConjecture`
anywhere, which is automatic since it is a hypothesis, not an axiom;
its absence from the axiom print is the point of the design.
