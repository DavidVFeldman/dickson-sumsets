import RequestProject.Construction

/-!
# Target: the conditional main theorem

This file states, without proving, the main theorem of the paper
*Dickson's conjecture and infinite multidimensional sum-sets within
the primes* (Feldman–Impagliazzo), together with supporting lemma
targets extracted from the paper's proof.  The unconditional
Proposition 2 is already machine-checked in `Main.lean`
(`no_prime_anchored_box_at_dimension_p`, `no_prime_anchored_box_of_card_ge`);
the present file is the commission for the other half of the sharp
dichotomy.

## Ground rules

* `DicksonConjecture` (defined in `Main.lean`) must be used only as an
  explicit hypothesis, never installed as an axiom.
* No `sorry`, `admit`, `native_decide`, or new axioms in the final
  development; only `propext`, `Classical.choice`, `Quot.sound`.
* The statement of `prime_anchored_box_exists` below is the contract:
  it may not be weakened.  Auxiliary lemmas may be restated or
  restructured freely.

## Statement-fidelity notes (read before "simplifying" hypotheses)

* `hn : 1 ≤ n` is load-bearing, not cosmetic.  Dropping it makes the
  statement false: with `n = 0`, `p = 2` the constraint `n + 2 ≤ p`
  holds, yet any positive even `x` gives `2 + x` even and `≥ 4`, hence
  composite, so no infinite even set `E 0` can work.
* `n + 2 ≤ p` is the truncated-subtraction-safe form of the paper's
  `n ≤ p - 2`.  Do not restate with `p - 2` in `ℕ`.
* The three structural conditions (infinite, `0 ∈ E i`, all elements
  even) are all part of the paper's claim; none may be dropped.
-/

open scoped BigOperators

namespace DicksonSumsets

/-- **Residue-choice lemma** — equations (room) and (sq) of the paper.
If `q` is prime with `(n + 1) * |C| < q` and `n + 1 < q`, there is a
residue `s` avoiding, for every `0 ≤ k ≤ n` and every `c ∈ C`, the
single residue forbidden by the pair `(k, c)`; the multiplier `k + 1`
is invertible because `k + 1 ≤ n + 1 < q`.

In the application `C` is the image in `ZMod q` of the critical values
present at the birth of `q`; since `q` itself is then a critical
value, `0 ∈ C`, and the case `k = 0`, `c = 0` forces `s ≠ 0` — no
separate hypothesis is needed to obtain a nonzero residue. -/
lemma exists_good_residue (q : ℕ) [hq : Fact q.Prime] (n : ℕ)
    (C : Finset (ZMod q))
    (hroom : (n + 1) * C.card < q) (hn : n + 1 < q) :
    ∃ s : ZMod q, ∀ k : ℕ, k ≤ n → ∀ c ∈ C,
      ((k : ZMod q) + 1) * s + c ≠ 0 := by
  -- The set of forbidden residues
  let bad := Finset.biUnion (Finset.range (n + 1)) (fun k =>
    Finset.image (fun c => -((k + 1 : ZMod q)⁻¹) * c) C)
  -- There are at most (n + 1) * |C| forbidden residues
  have hbad_card : bad.card ≤ (n + 1) * C.card := by
    calc bad.card ≤ ∑ k ∈ Finset.range (n + 1), (Finset.image (fun c => -((k + 1 : ZMod q)⁻¹) * c) C).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ k ∈ Finset.range (n + 1), C.card := by
          apply Finset.sum_le_sum; intros; apply Finset.card_image_le
      _ = (n + 1) * C.card := by simp
  -- Since (n + 1) * |C| < q and |ZMod q| = q, there's a good element
  have hqcard : Fintype.card (ZMod q) = q := ZMod.card q
  have hbaddr : bad.card < Fintype.card (ZMod q) := by
    rw [hqcard]
    exact Nat.lt_of_le_of_lt hbad_card hroom
  by_contra hall_bad
  push_neg at hall_bad
  -- If all residues are bad, then bad = univ
  have hbad_univ : bad = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro s
    obtain ⟨k, hk, c, hc, heq⟩ := hall_bad s
    simp only [bad, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image]
    refine ⟨k, by omega, c, hc, ?_⟩
    have hk1 : (k : ZMod q) + 1 ≠ 0 := by
      have hlt : (k + 1 : ℕ) < q := by omega
      simp only [ne_eq]
      intro h
      have hqpos : 0 < q := hq.1.pos
      rw [show (k : ZMod q) + 1 = (k + 1 : ℕ) by simp] at h
      rw [ZMod.natCast_eq_zero_iff] at h
      exact Nat.not_dvd_of_pos_of_lt (by omega) hlt h
    have hinv : ((k : ZMod q) + 1)⁻¹ * ((k : ZMod q) + 1) = 1 := by
      field_simp
    have heq' : ((k : ZMod q) + 1) * s = -c := by linear_combination heq
    have : -((k + 1 : ZMod q)⁻¹) * c = s := by
      calc -((k + 1 : ZMod q)⁻¹) * c = ((k + 1 : ZMod q)⁻¹) * (-c) := by ring
        _ = ((k + 1 : ZMod q)⁻¹) * (((k : ZMod q) + 1) * s) := by rw [heq']
        _ = ((k + 1 : ZMod q)⁻¹ * ((k : ZMod q) + 1)) * s := by rw [mul_assoc]
        _ = s := by rw [hinv, one_mul]
    exact this
  rw [hbad_univ] at hbaddr
  have huniv : (Finset.univ : Finset (ZMod q)).card = Fintype.card (ZMod q) := Finset.card_univ
  rw [huniv] at hbaddr
  exact Nat.not_lt.mpr (le_refl _) hbaddr


/-- **Limit step**: a pointwise-increasing chain of finite
configurations, each of whose finite anchored boxes lies in the
primes, has union with anchored box in the primes.  (Any choice
function into the union takes values in a single stage, by
directedness of the chain.) -/
lemma primeAnchoredBox_iUnion (p n : ℕ)
    (F : ℕ → Fin (n + 1) → Finset ℕ)
    (hmono : ∀ t i, F t i ⊆ F (t + 1) i)
    (hbox : ∀ t (x : Fin (n + 1) → ℕ),
      (∀ i, x i ∈ F t i) → (p + ∑ i, x i).Prime) :
    PrimeAnchoredBox p (fun i => ⋃ t, (F t i : Set ℕ)) := by
  intro x hx
  -- For each i, there exists some t_i with x i ∈ F t_i i
  have hmem : ∀ i, ∃ t : ℕ, x i ∈ F t i := fun i => by
    have := hx i
    simp only [Set.mem_iUnion] at this
    exact this
  choose t ht using hmem
  -- Take T = max of all t_i; by monotonicity, x i ∈ F T i for all i
  let T := Finset.univ.sup t
  have hmono_step : ∀ (i : Fin (n + 1)) (s s' : ℕ), s ≤ s' → F s i ⊆ F s' i := by
    intro i
    suffices ∀ s' : ℕ, ∀ s ≤ s', F s i ⊆ F s' i by exact fun s s' h => this s' s h
    intro s'
    induction s' with
    | zero => intro s hs; rw [Nat.le_zero.mp hs]
    | succ s' ih =>
      intro s hs
      rcases Nat.lt_or_eq_of_le hs with hlt | rfl
      · exact Set.Subset.trans (ih s (Nat.lt_succ_iff.mp hlt)) (hmono s' i)
      · rfl
  have hT : ∀ i, x i ∈ F T i := fun i =>
    (hmono_step i (t i) T (Finset.le_sup (Finset.mem_univ i))) (ht i)
  exact hbox T x hT


/-- **Infinitude at the limit** from unbounded stage cardinalities. -/
lemma infinite_iUnion_of_unbounded_card (F : ℕ → Finset ℕ)
    (hgrow : ∀ m : ℕ, ∃ t, m ≤ (F t).card) :
    (⋃ t, (F t : Set ℕ)).Infinite := by
  by_contra hfin
  set S := ⋃ t, (F t : Set ℕ) with hS_def
  have hS_finite : S.Finite := Set.not_infinite.mp hfin
  have hbound : ∀ t, (F t).card ≤ hS_finite.toFinset.card := by
    intro t
    apply Finset.card_le_card
    exact hS_finite.subset_toFinset.mpr (Set.subset_iUnion (fun t => (F t : Set ℕ)) t)
  obtain ⟨t, ht⟩ := hgrow (hS_finite.toFinset.card + 1)
  linarith [hbound t]


/-- A symmetric form of the greedy construction: the selected even numbers
have all anchored sums of at most `n + 1` distinct terms prime.  Partitioning
this sequence cyclically gives the coordinate-wise construction below. -/
lemma bounded_prime_finite_sums_sequence_exists
    (hDickson : DicksonConjecture)
    (p n : ℕ) (hp : p.Prime) (hn : 1 ≤ n) (hnp : n + 2 ≤ p) :
    ∃ e : ℕ → ℕ, Function.Injective e ∧
      (∀ j, Even (e j)) ∧
      ∀ s : Finset ℕ, s.card ≤ n + 1 →
        (p + ∑ j ∈ s, e j).Prime := by
  exact Construction.bounded_prime_finite_sums_sequence_exists' p n hDickson hp hn hnp

/-- Core finite-stage construction from the paper.  Each stage enlarges every
coordinate, preserves the finite prime-box property, and has at least the
stage number of elements in every coordinate.  The proof is the greedy
Dickson/CRT construction with critical and urgent primes described below. -/
lemma finite_prime_box_chain_exists
    (hDickson : DicksonConjecture)
    (p n : ℕ) (hp : p.Prime) (hn : 1 ≤ n) (hnp : n + 2 ≤ p) :
    ∃ F : ℕ → Fin (n + 1) → Finset ℕ,
      (∀ t i, F t i ⊆ F (t + 1) i) ∧
      (∀ t i, 0 ∈ F t i) ∧
      (∀ t i, ∀ x ∈ F t i, Even x) ∧
      (∀ t (x : Fin (n + 1) → ℕ),
        (∀ i, x i ∈ F t i) → (p + ∑ i, x i).Prime) ∧
      (∀ t i, t ≤ (F t i).card) := by
  obtain ⟨e, he_inj, he_even, he_primes⟩ := bounded_prime_finite_sums_sequence_exists hDickson p n hp hn hnp
  -- Define F t i = {0} ∪ {e k | k < (t+1)*(n+1) ∧ k ≡ i (mod n+1)}
  let S : ℕ → Fin (n + 1) → Finset ℕ := fun t i => Finset.filter (fun k => k % (n + 1) = i) (Finset.range ((t + 1) * (n + 1)))
  let F : ℕ → Fin (n + 1) → Finset ℕ := fun t i => {0} ∪ Finset.image e (S t i)
  use F
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  -- 1. Monotonicity: F t i ⊆ F (t + 1) i
  · intro t i x hx
    simp only [F, Finset.mem_union] at hx ⊢
    obtain hx | hx := hx
    · simp only [Finset.mem_singleton] at hx; simp [hx]
    · simp only [Finset.mem_image] at hx
      obtain ⟨k, hk, rfl⟩ := hx
      right
      simp only [Finset.mem_image]
      use k
      simp [S] at hk ⊢
      exact ⟨Nat.lt_of_lt_of_le hk.1 (Nat.mul_le_mul_right _ (Nat.le_succ _)), hk.2⟩
  -- 2. 0 ∈ F t i
  · intro t i
    simp [F, Finset.mem_union, Finset.mem_singleton]
  -- 3. All elements even
  · intro t i x hx
    simp [F] at hx
    rcases hx with rfl | ⟨k, hk, rfl⟩
    · exact Even.zero
    · exact he_even k
  -- 4. Prime box property
  · intro t x hx
    -- For each i, x i ∈ F t i means x i = 0 or x i = e k for some k ∈ S t i
    -- Define s = {i | x i ≠ 0}
    let s := Finset.univ.filter (fun i => x i ≠ 0)
    -- For each i ∈ s, x i = e (k i) for some k i
    have hx_nonzero : ∀ i ∈ s, ∃ k ∈ S t i, x i = e k := by
      intro i his
      simp [s] at his
      have hi := hx i
      simp only [F] at hi
      rw [Finset.mem_union, Finset.mem_singleton] at hi
      rcases hi with h0 | hi
      · exact absurd h0 his
      · rw [Finset.mem_image] at hi
        obtain ⟨k', hk', hkx⟩ := hi
        exact ⟨k', hk', hkx.symm⟩
    choose f hf using hx_nonzero
    -- Define g : Fin (n+1) → ℕ by g i = f i a if i ∈ s, else 0
    -- For i ∈ s, x i = e (g i)
    let g : Fin (n + 1) → ℕ := fun i => if hi : x i = 0 then 0 else f i (by simpa [s] using hi)
    have hg : ∀ i, x i = if hi : x i = 0 then 0 else e (g i) := by
      intro i
      by_cases hi : x i = 0 <;> simp [g, hi]
      have := hf i (by simpa [s] using hi)
      simp at this
      exact this.2
    -- Rewrite the sum: only nonzero terms contribute
    have hsum : ∑ i, x i = ∑ i ∈ s, e (g i) := by
      rw [show ∑ i : Fin (n + 1), x i = ∑ i : Fin (n + 1), if x i = 0 then 0 else e (g i) from Finset.sum_congr rfl fun i _ => hg i]
      rw [Finset.sum_ite]
      simp [s]
    rw [hsum]
    -- The g i values are distinct since g i ∈ S t i means (g i) % (n+1) = i
    -- Define ks = {g i | i ∈ s}
    let ks := s.image g
    -- Show the sum equals sum over ks
    have hsum_eq : ∑ i ∈ s, e (g i) = ∑ j ∈ ks, e j := by
      rw [Finset.sum_image]
      intro i hi j hj heq
      -- g i = g j implies i = j since (g i) % (n+1) = i and (g j) % (n+1) = j
      have hi' : i ∈ s := hi
      have hj' : j ∈ s := hj
      have hiS := hf i hi'
      have hjS := hf j hj'
      simp [S] at hiS hjS
      have himod := hiS.1.2
      have hjmod := hjS.1.2
      -- g i = f i hi' and g j = f j hj'
      -- So g i % (n+1) = i and g j % (n+1) = j
      -- Since g i = g j, we have i = j
      have hi'' : x i ≠ 0 := by simp [s] at hi; exact hi
      have hj'' : x j ≠ 0 := by simp [s] at hj; exact hj
      have hg_eq_i : g i = f i (by simp [s]; exact hi'') := by simp [g, hi'']
      have hg_eq_j : g j = f j (by simp [s]; exact hj'') := by simp [g, hj'']
      rw [hg_eq_i, hg_eq_j] at heq
      -- Now heq : f i _ = f j _
      -- himod : f i hi' % (n+1) = i
      -- hjmod : f j hj' % (n+1) = j
      -- Since f i hi' = f j hj', their residues are equal, so i = j
      -- heq says g i = g j
      -- Since x i ≠ 0 and x j ≠ 0, g i = f i (_proof_) and g j = f j (_proof_)
      -- The k values are unique because x i = e (f i _) and e is injective
      apply Fin.ext
      -- f i hi' and f i hi'' are the same because e is injective and x i = e (f i _)
      have hf_unique : ∀ i (a b : i ∈ s), f i a = f i b := by
        intro i a b
        have ha := hf i a
        have hb := hf i b
        simp at ha hb
        exact he_inj (ha.2.symm.trans hb.2)
      -- Now we can show f i hi' = f j hj'
      -- hi'' and hj'' are proofs of i ∈ s and j ∈ s
      have hi''' : i ∈ s := by simp [s]; exact hi''
      have hj''' : j ∈ s := by simp [s]; exact hj''
      -- heq : f i (...) = f j (...), so f i hi''' = f j hj'''
      have heq' : f i hi' = f j hj' := by
        rw [← hf_unique i hi' hi''', ← hf_unique j hj' hj''']
        exact heq
      -- Now use heq' with himod and hjmod
      rw [heq'] at himod
      exact congrArg Fin.val (Fin.ext (by omega : (i : ℕ) = j))
    rw [hsum_eq]
    -- Now |ks| = |s.image g| ≤ |s| ≤ n+1
    apply he_primes
    calc (s.image g).card ≤ s.card := Finset.card_image_le
      _ ≤ Finset.card Finset.univ := Finset.card_le_card (Finset.filter_subset _ _)
      _ = n + 1 := Finset.card_fin _
  -- 5. Growth: t ≤ |F t i|
  · intro t i
    -- S t i = {k < (t+1)*(n+1) | k % (n+1) = i} has t+1 elements: i, i+(n+1), ..., i+t*(n+1)
    have hS_card : (S t i).card = t + 1 := by
      have hS_eq : S t i = Finset.image (fun j => i + j * (n + 1)) (Finset.range (t + 1)) := by
        ext k
        simp [S]
        constructor
        · rintro ⟨hk_lt, hk_mod⟩
          use k / (n + 1)
          have hdiv := Nat.div_add_mod k (n + 1)
          simp [hk_mod] at hdiv
          constructor
          · -- k / (n + 1) ≤ t
            have : (n + 1) * (k / (n + 1)) < (t + 1) * (n + 1) := by omega
            nlinarith
          · -- i + k / (n + 1) * (n + 1) = k
            linarith
        · rintro ⟨q, hq_lt, rfl⟩
          refine ⟨by have : (i : ℕ) < n + 1 := Fin.is_lt i; nlinarith, ?_⟩
          simp [Nat.add_mod, Nat.mod_eq_of_lt (Fin.is_lt i)]
      rw [hS_eq, Finset.card_image_of_injective _ fun a b hab => by
        have : a * (n + 1) = b * (n + 1) := by omega
        nlinarith, Finset.card_range]
    calc t ≤ t + 1 := Nat.le_succ _
      _ = (S t i).card := hS_card.symm
      _ = (Finset.image e (S t i)).card := (Finset.card_image_of_injective _ he_inj).symm
      _ ≤ ({0} ∪ Finset.image e (S t i)).card := Finset.card_le_card (Finset.subset_union_right)
      _ = (F t i).card := rfl

/-- **Main theorem of the paper** (Theorem 1, sharp form).  Assuming
Dickson's conjecture, for every prime `p` and every `n` with
`1 ≤ n` and `n + 2 ≤ p` there are `n + 1` infinite sets of even
naturals, each containing `0`, whose anchored sum-set
`{p} + E 0 + ⋯ + E n` lies in the primes.

Together with `no_prime_anchored_box_at_dimension_p` this makes the
threshold sharp: `p - 1` sets are impossible, `p - 1` is the count
`n + 1` reaches exactly when `n = p - 2`. -/
theorem prime_anchored_box_exists
    (hDickson : DicksonConjecture)
    (p n : ℕ) (hp : p.Prime) (hn : 1 ≤ n) (hnp : n + 2 ≤ p) :
    ∃ E : Fin (n + 1) → Set ℕ,
      (∀ i, (E i).Infinite) ∧
      (∀ i, 0 ∈ E i) ∧
      (∀ i, ∀ x ∈ E i, Even x) ∧
      PrimeAnchoredBox p E := by
  obtain ⟨F, hmono, hzero, heven, hbox, hgrow⟩ :=
    finite_prime_box_chain_exists hDickson p n hp hn hnp
  let E : Fin (n + 1) → Set ℕ := fun i => ⋃ t, (F t i : Set ℕ)
  refine ⟨E, ?_, ?_, ?_, ?_⟩
  · intro i
    apply infinite_iUnion_of_unbounded_card
    intro m
    exact ⟨m, hgrow m i⟩
  · intro i
    simp only [E, Set.mem_iUnion]
    exact ⟨0, hzero 0 i⟩
  · intro i x hx
    simp only [E, Set.mem_iUnion] at hx
    obtain ⟨t, ht⟩ := hx
    exact heven t i x ht
  · exact primeAnchoredBox_iUnion p n F hmono hbox

/-- The original (pre-sharpening) form of the theorem: for every
`n ≥ 1` some prime anchor works.  Follows from
`prime_anchored_box_exists` via `Nat.exists_infinite_primes`. -/
theorem prime_anchored_box_exists_some_prime
    (hDickson : DicksonConjecture) (n : ℕ) (hn : 1 ≤ n) :
    ∃ p : ℕ, p.Prime ∧
      ∃ E : Fin (n + 1) → Set ℕ,
        (∀ i, (E i).Infinite) ∧
        (∀ i, 0 ∈ E i) ∧
        (∀ i, ∀ x ∈ E i, Even x) ∧
        PrimeAnchoredBox p E := by
  obtain ⟨p, hle, hp⟩ := Nat.exists_infinite_primes (n + 2)
  exact ⟨p, hp, prime_anchored_box_exists hDickson p n hp hn hle⟩

/-! ## Supporting targets from the paper's proof

The proof in the paper (Section "Proof of Theorem 1") is an infinite
greedy construction.  The lemmas below isolate its two clean finite
ingredients and its limit step; the recursion itself is described
after them.
-/

/-! ## The recursion (prose blueprint, keyed to the paper)

The heart of the proof is the inductive insertion of elements
`e i j` in round-robin coordinate order.  The paper's bookkeeping,
which the formalization must reproduce or strengthen:

1. **State.**  After finitely many insertions one has segments
   `F : Fin (n + 1) → Finset ℕ` with `0 ∈ F i`, all elements even,
   and the finite box property `∀ x, (∀ i, x i ∈ F i) →
   (p + ∑ i, x i).Prime`.

2. **Critical values** (paper, "Critical values and the residues
   s_q"): elements of the current sum-set representable as
   `p + ∑_{i ∈ T} x i` with `T ⊊ Finset.univ` and `x i ∈ F i \ {0}`.
   All are primes.  `p` itself (empty `T`) is critical from the
   outset.

3. **Births and residues.**  When a prime `q` first becomes a
   critical value, `C_q` := critical values at that moment,
   `N_q := |C_q|`.  The growing-room invariant (condition (ii) of the
   insertion step) guarantees `(n + 1) * N_q < q`, so
   `exists_good_residue` supplies `s_q ≠ 0`; every element inserted
   afterwards is `≡ s_q (mod q)`.  For `q = p`: birth at the start,
   `C_p = {p}`, and `n + 1 < p` (from `hn`, `hnp`) makes any nonzero
   residue admissible — this is exactly where `n + 2 ≤ p` is spent.

4. **Confinement lemma** (paper, Lemma 3): every later critical value
   is `≡ c + k * s_q (mod q)` with `c ∈ C_q`, `0 ≤ k ≤ n`.  Proof:
   in a critical representation at most `n` coordinates are present;
   delete those inserted after the birth of `q` (each `≡ s_q`); the
   rest is a critical value already present at birth.
   **Formalization warning:** this argument uses birth *times*.  Either
   carry the construction history explicitly (recommended: build the
   whole construction as a single strong recursion over the stage
   `t : ℕ`, with births defined as stage numbers), or design a
   history-free strengthened invariant — but note the naive
   history-free version `∀ c critical, ∀ 1 ≤ m ≤ n + 1, q ∤ c + m*s_q`
   is NOT self-propagating (the range of `m` degrades by one per
   insertion); the per-value headroom `n - k` must be tracked.

5. **Urgent primes** (paper, "Frozen primes"): `q` not critical with
   `q ≤` cardinality of the upcoming sum-set; permanently, all later
   insertions are `≡ 0 (mod q)`.  `q = 2` is urgent from the first
   insertion and never critical (critical values are odd primes), so
   evenness of all inserted elements is automatic.

6. **Insertion step** (paper, "The inductive step"): with
   `C* = {p} + ∑_{i' < i} F i' + ∑_{i' > i} (old) F i'` (all critical
   values, since coordinate `i` is omitted), set `A :=` product of
   urgent and critical primes, choose `B` by CRT (`≡ 0` at urgent,
   `≡ s_q` at critical), and check Dickson admissibility of
   `{A*m + B + c : c ∈ C*}` in three exhaustive cases:
   `q ∤ A` (then `|C*| < q` since `q` exceeds the upcoming sum-set
   size); `q` urgent (then `A*m + B + c ≡ c`, a prime `≠ q`);
   `q` critical (then `≡ (k+1)*s_q + c₀ ≠ 0` by confinement and the
   defining property of `s_q`).  Dickson (`dickson_for_linear_forms`)
   gives infinitely many admissible `m`; choose `e i j := A*m + B`
   large enough for size conditions (i) (new sums exceed all old sums
   and all tracked primes — so urgent primes never become critical and
   new sums are genuinely new) and (ii) (new sums exceed
   `(n + 1) * N + 1` for `N` the post-insertion critical count — the
   growing-room invariant for any primes born critical at this step;
   several may be born at once, and they then lie in one another's
   `C_q`, as the confinement lemma requires).

7. **Conclusion.**  Round-robin order gives each coordinate
   infinitely many insertions; `infinite_iUnion_of_unbounded_card`
   and `primeAnchoredBox_iUnion` finish.
-/

end DicksonSumsets
