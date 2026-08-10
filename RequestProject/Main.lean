import Mathlib

open scoped BigOperators

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

namespace DicksonSumsets

/-- A finite family of natural-number linear forms is admissible when no prime
    divides its product for every input.  The pointwise formulation avoids an
    empty-product convention and is equivalent for a nonempty family. -/
def Admissible {ι : Type*} [Fintype ι] (a b : ι → ℕ) : Prop :=
  ∀ q : ℕ, q.Prime → ∃ m : ℕ, ∀ i : ι, ¬q ∣ a i * m + b i

/-- Dickson's conjecture, stated only as a proposition.  It is not installed as
    an axiom: conditional results take a term of this type as a hypothesis. -/
def DicksonConjecture : Prop :=
  ∀ (ι : Type) (_ : Fintype ι) (a b : ι → ℕ),
    (∀ i, 0 < a i) → Admissible a b →
      Set.Infinite {m : ℕ | ∀ i, (a i * m + b i).Prime}

/-- A local way to invoke Dickson's conjecture.  In particular, every result
    using it must expose `hDickson` among its hypotheses. -/
theorem dickson_for_linear_forms
    (hDickson : DicksonConjecture) (ι : Type) [Fintype ι]
    (a b : ι → ℕ) (ha : ∀ i, 0 < a i) (hadm : Admissible a b) :
    Set.Infinite {m : ℕ | ∀ i, (a i * m + b i).Prime} :=
  hDickson ι (inferInstance : Fintype ι) a b ha hadm

/-- Every choice from a finite family of sets gives a prime after adding the
    anchor.  This is the precise finite sum-set containment used below. -/
def PrimeAnchoredBox (p : ℕ) {ι : Type*} [Fintype ι]
    (E : ι → Set ℕ) : Prop :=
  ∀ x : ι → ℕ, (∀ i, x i ∈ E i) →
    (p + ∑ i, x i).Prime

/-- Prefix-sum pigeonhole: among `p` natural numbers there is a nonempty
    consecutive block whose sum is divisible by `p`. -/
lemma exists_nonempty_interval_sum_dvd
    (p : ℕ) (hp : 0 < p) (x : Fin p → ℕ) :
    ∃ a b : ℕ, a < b ∧ b ≤ p ∧
      p ∣ ∑ k ∈ Finset.Ico a b, x ⟨k % p, Nat.mod_lt k hp⟩ := by
  letI : NeZero p := ⟨Nat.ne_of_gt hp⟩
  let f : Fin (p + 1) → ZMod p := fun k =>
    ∑ i ∈ Finset.range k.val, (x ⟨i % p, Nat.mod_lt i hp⟩ : ZMod p)
  have hc : Fintype.card (ZMod p) < Fintype.card (Fin (p + 1)) := by simp
  obtain ⟨u, v, huv, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt f hc
  rcases lt_or_gt_of_ne (Fin.val_ne_iff.mpr huv) with huvlt | hvult
  · refine ⟨u.val, v.val, huvlt, Nat.le_of_lt_succ v.isLt, ?_⟩
    apply (ZMod.natCast_eq_zero_iff _ p).mp
    have hsum : (∑ k ∈ Finset.Ico u.val v.val,
        (x ⟨k % p, Nat.mod_lt k hp⟩ : ZMod p)) = 0 := by
      have hrange : (Finset.range v.val : Finset ℕ) =
          Finset.range u.val ∪ Finset.Ico u.val v.val := by ext k; simp; omega
      have hdis : Disjoint (Finset.range u.val) (Finset.Ico u.val v.val) := by
        exact Finset.disjoint_left.mpr (by simp; omega)
      have h := heq
      dsimp [f] at h
      rw [hrange, Finset.sum_union hdis] at h
      rw [← add_left_inj (∑ i ∈ Finset.range u.val,
        (x ⟨i % p, Nat.mod_lt i hp⟩ : ZMod p))]
      simpa using h
    simpa only [Nat.cast_sum] using hsum
  · refine ⟨v.val, u.val, hvult, Nat.le_of_lt_succ u.isLt, ?_⟩
    apply (ZMod.natCast_eq_zero_iff _ p).mp
    have hsum : (∑ k ∈ Finset.Ico v.val u.val,
        (x ⟨k % p, Nat.mod_lt k hp⟩ : ZMod p)) = 0 := by
      have hrange : (Finset.range u.val : Finset ℕ) =
          Finset.range v.val ∪ Finset.Ico v.val u.val := by ext k; simp; omega
      have hdis : Disjoint (Finset.range v.val) (Finset.Ico v.val u.val) := by
        exact Finset.disjoint_left.mpr (by simp; omega)
      have h := heq.symm
      dsimp [f] at h
      rw [hrange, Finset.sum_union hdis] at h
      rw [← add_left_inj (∑ i ∈ Finset.range v.val,
        (x ⟨i % p, Nat.mod_lt i hp⟩ : ZMod p))]
      simpa using h
    simpa only [Nat.cast_sum] using hsum

/-- The unconditional obstruction in Proposition 2 of the paper. -/
theorem no_prime_anchored_box_at_dimension_p
    (p : ℕ) (hp : p.Prime) (E : Fin p → Set ℕ)
    (hzero : ∀ i, 0 ∈ E i)
    (hpos : ∀ i, ∃ x ∈ E i, 0 < x) :
    ¬ PrimeAnchoredBox p E := by
  intro hbox
  choose x hxE hxpos using hpos
  obtain ⟨a, b, hab, hbp, hdvd⟩ :=
    exists_nonempty_interval_sum_dvd p hp.pos x
  let y : Fin p → ℕ := fun i => if i.val ∈ Finset.Ico a b then x i else 0
  have hyE : ∀ i, y i ∈ E i := by
    intro i
    simp only [y]
    split <;> simp_all
  have hsum : ∑ i, y i =
      ∑ k ∈ Finset.Ico a b, x ⟨k % p, Nat.mod_lt k hp.pos⟩ := by
    dsimp [y]
    rw [← Finset.sum_filter]
    apply Finset.sum_bij (fun i _ => i.val)
    · intro i hi
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hi
    · intro i _ j _ h
      exact Fin.ext h
    · intro k hk
      have hklt : k < p := lt_of_lt_of_le (Finset.mem_Ico.mp hk).2 hbp
      refine ⟨⟨k, hklt⟩, ?_, rfl⟩
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and]
    · intro i _
      simp [Nat.mod_eq_of_lt i.isLt]
  have hprime := hbox y hyE
  have hpdiv : p ∣ p + ∑ i, y i :=
    dvd_add (dvd_refl p) (by rwa [hsum])
  have hne : p ≠ p + ∑ i, y i := by
    have ha_mem : a ∈ Finset.Ico a b := by simp [hab]
    have hsumpos : 0 < ∑ k ∈ Finset.Ico a b,
        x ⟨k % p, Nat.mod_lt k hp.pos⟩ :=
      Finset.sum_pos' (fun k _ => Nat.zero_le _) ⟨a, ha_mem, hxpos _⟩
    rw [hsum]
    omega
  exact (Nat.not_prime_of_dvd_of_ne hpdiv hp.ne_one hne) hprime

/-- The finite-family consequence stated after Proposition 2: any family with
    at least `p` coordinates already contains the forbidden subconfiguration. -/
theorem no_prime_anchored_box_of_card_ge
    (p : ℕ) (hp : p.Prime) {ι : Type*} [Fintype ι]
    (hcard : p ≤ Fintype.card ι) (E : ι → Set ℕ)
    (hzero : ∀ i, 0 ∈ E i)
    (hpos : ∀ i, ∃ x ∈ E i, 0 < x) :
    ¬ PrimeAnchoredBox p E := by
  classical
  let emb : Fin p → ι := fun i =>
    (Fintype.equivFin ι).symm (Fin.castLE hcard i)
  have hinj : Function.Injective emb := by
    intro i j h
    dsimp [emb] at h
    exact Fin.castLE_injective hcard ((Fintype.equivFin ι).symm.injective h)
  let E' : Fin p → Set ℕ := fun i => E (emb i)
  have hbad : ¬ PrimeAnchoredBox p E' :=
    no_prime_anchored_box_at_dimension_p p hp E'
      (fun i => hzero _) (fun i => hpos _)
  intro hbox
  apply hbad
  intro x hx
  let z : ι → ℕ := fun j => ∑ i, if emb i = j then x i else 0
  have hzE : ∀ j, z j ∈ E j := by
    intro j
    by_cases h : ∃ i, emb i = j
    · obtain ⟨i, rfl⟩ := h
      have hz : z (emb i) = x i := by
        dsimp [z]
        calc
          _ = ∑ k, if k = i then x k else 0 := by
            apply Finset.sum_congr rfl
            intro k _
            by_cases hki : k = i
            · subst k; simp
            · have : emb k ≠ emb i := fun he => hki (hinj he)
              simp [hki, this]
          _ = x i := by simp
      rw [hz]
      exact hx i
    · have hz : z j = 0 := by
        dsimp [z]
        apply Finset.sum_eq_zero
        intro i _
        split
        next he => exact False.elim (h ⟨i, he⟩)
        next => rfl
      rw [hz]
      exact hzero j
  have hsum : ∑ j, z j = ∑ i, x i := by
    dsimp [z]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    simp
  rw [← hsum]
  exact hbox z hzE

end DicksonSumsets
