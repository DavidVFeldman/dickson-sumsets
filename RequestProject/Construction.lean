import RequestProject.Main

/-!
# Construction skeleton for `bounded_prime_finite_sums_sequence_exists`

UNCOMPILED BLUEPRINT.  Written without a Lean toolchain: definitions and
statements are intended to elaborate as written, but names of Mathlib
lemmas and tactic details must be repaired freely.  What must be
preserved is the mathematical content of each declaration; every proof
is given in prose in the docstring at the granularity of a routine
Lean argument.  Statements marked (KEY) carry the mathematical weight.

Conventions: the construction history is a list `L : List ℕ` of chosen
elements, oldest first.  All bookkeeping is a function of `L`.
`p` and `n` are fixed throughout; hypotheses `hp : p.Prime`,
`hn : 1 ≤ n`, `hnp : n + 2 ≤ p` are ambient.
-/

open scoped BigOperators
open Finset

namespace DicksonSumsets
namespace Construction

variable (p n : ℕ)

/-- Anchored sums of at most `n` distinct chosen elements: the critical
values.  (`s = ∅` contributes `p` itself, so `p ∈ critVals L` always.) -/
def critVals (L : List ℕ) : Finset ℕ :=
  (L.toFinset.powerset.filter fun s => s.card ≤ n).image fun s => p + ∑ x ∈ s, x

/-- Anchored sums of at most `n + 1` distinct chosen elements: the
values that must be prime. -/
def allVals (L : List ℕ) : Finset ℕ :=
  (L.toFinset.powerset.filter fun s => s.card ≤ n + 1).image fun s => p + ∑ x ∈ s, x

/-- Birth of `q`: the least prefix length at which `q` is critical.
Meaningful only when `q ∈ critVals p n L`. -/
noncomputable def birth (L : List ℕ) (q : ℕ) : ℕ :=
  sInf {t | q ∈ critVals p n (L.take t)}

/-- Critical values present at the birth of `q` (the paper's `C_q`). -/
noncomputable def birthSet (L : List ℕ) (q : ℕ) : Finset ℕ :=
  critVals p n (L.take (birth p n L q))

/-- The residue `s_q`: LEAST `s` with `1 ≤ s < q` avoiding, for all
`k ≤ n` and `c ∈ C_q`, the divisibility `q ∣ (k+1)*s + c`.  Least
makes it a function of the history; no choice. -/
noncomputable def res (L : List ℕ) (q : ℕ) : ℕ :=
  sInf {s | 1 ≤ s ∧ s < q ∧ ∀ k ≤ n, ∀ c ∈ birthSet p n L q, ¬ q ∣ (k + 1) * s + c}

/-- Urgency at a prefix: `q` prime, not a critical value, and at most
one more than the current critical count.  NOTE the `+ 1`: with
threshold `q ≤ card` alone, `2` fails to be urgent before the first
insertion (`critVals [] = {p}` has card 1) and evenness collapses.
With `+ 1`, `2` is urgent at every prefix, since critical values are
`≥ p ≥ 3` so `2` is never critical, and `card ≥ 1` always. -/
def Urgent (L : List ℕ) (q : ℕ) : Prop :=
  q.Prime ∧ q ∉ critVals p n L ∧ q ≤ (critVals p n L).card + 1

/-- The invariant.  Fields 4–6 are per-entry conditions relative to the
prefix strictly before that entry, so extending by one element reduces
`Good (L ++ [e])` to `Good L` plus conditions on `e` alone. -/
structure Good (L : List ℕ) : Prop where
  /-- entries strictly increase (gives injectivity and `Nodup`). -/
  mono : L.Chain' (· < ·)
  /-- every anchored ≤(n+1)-sum is prime (in particular every critical
  value is prime, since `critVals ⊆ allVals`). -/
  primes : ∀ v ∈ allVals p n L, v.Prime
  /-- discipline at critical primes: every entry at a position `u` with
  `birth ≤ u` is `≡ res q (mod q)`.  (Birth computed in `L`; by
  `birth_stable` below this agrees with birth in any extension.) -/
  disc : ∀ q ∈ critVals p n L, ∀ u (h : u < L.length),
    birth p n L q ≤ u → L.get ⟨u, h⟩ % q = res p n L q % q
  /-- discipline at urgent primes: an entry is divisible by every prime
  urgent at its own prefix. -/
  frozen : ∀ u (h : u < L.length), ∀ q,
    Urgent p n (L.take u) q → q ∣ L.get ⟨u, h⟩
  /-- size condition (i): each entry exceeds every anchored
  ≤(n+1)-sum of its prefix (hence exceeds all previous entries, all
  old sums, and all tracked primes, which are `≤ card + 1 <` old
  sums… see `tracked_lt`). -/
  big : ∀ u (h : u < L.length), ∀ v ∈ allVals p n (L.take u),
    v < L.get ⟨u, h⟩
  /-- size condition (ii), growing room for newborns: each entry
  exceeds `(n+1) * (bound on the post-insertion critical count)`.
  Stated with the e-independent bound `newbound` (below) so the step
  lemma can impose it before choosing the entry. -/
  room : ∀ u (h : u < L.length),
    (n + 1) * ((critVals p n (L.take u)).card + (critVals p n (L.take u)).card) <
      L.get ⟨u, h⟩

/-!  On `room`: post-insertion critical values are old ones together
with `p + e + (≤(n-1)-sum of old)`, i.e. `e + c` for `c` an old
≤(n-1)-anchored sum; there are at most `|critVals(prefix)|` of those,
so `N_post ≤ 2 * |critVals(prefix)|` — the bound used above, available
BEFORE `e` is chosen.  Any newborn critical prime `q'` satisfies
`q' = p + e + … > e > (n+1) * N_post ≥ (n+1) * |birthSet q'|`, which is
the growing-room inequality (`birthSet q' ⊆ critVals(post)` since the
birth prefix of a newborn is `take (u+1)`).  -/

/- ================= elementary structural lemmas ================= -/

/-- `critVals` is monotone under `take` (prefixes only add subsets). -/
lemma critVals_take_mono (L : List ℕ) {t₁ t₂ : ℕ} (h : t₁ ≤ t₂) :
    critVals p n (L.take t₁) ⊆ critVals p n (L.take t₂) := by
  unfold critVals
  intro x hx
  simp only [Finset.mem_image] at hx ⊢
  obtain ⟨s, hs, rfl⟩ := hx
  simp only [Finset.mem_filter, Finset.mem_powerset] at hs ⊢
  have hsub : (L.take t₁).toFinset ⊆ (L.take t₂).toFinset := fun a ha => by
    rw [List.mem_toFinset] at ha ⊢
    have htaketaket : L.take t₁ = (L.take t₂).take t₁ := by simp [List.take_take, min_eq_left h]
    rw [htaketaket] at ha
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp ha
    refine List.mem_iff_get.mpr ⟨⟨i.val, ?_⟩, ?_⟩
    · have hlen1 := @List.length_take ℕ t₁ (L.take t₂)
      have hlen2 := @List.length_take ℕ t₂ L
      have hi_bound := i.2
      simp_all [min_eq_left h]
    · simp_all
  exact ⟨s, ⟨fun a ha => hsub (hs.1 ha), hs.2⟩, rfl⟩


/-- `critVals (L.take t) = critVals L` for `t ≥ length`; and
`critVals L ⊆ critVals (L ++ [e])`. -/
lemma critVals_append (L : List ℕ) (e : ℕ) :
    critVals p n L ⊆ critVals p n (L ++ [e]) := by
  unfold critVals
  intro x hx
  rw [Finset.mem_image] at hx ⊢
  obtain ⟨s, hs, rfl⟩ := hx
  refine ⟨s, ?_, rfl⟩
  have hs1 : s ⊆ L.toFinset := by
    have := Finset.mem_filter.mp hs |>.1
    rwa [Finset.mem_powerset] at this
  rw [List.toFinset_append]
  simp only [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨hs1.trans (Finset.subset_union_left), Finset.mem_filter.mp hs |>.2⟩


/-- `p ∈ critVals L` (empty subset), and every element of
`critVals L` is `≥ p`. -/
lemma p_mem_critVals (L : List ℕ) : p ∈ critVals p n L := by
  unfold critVals
  simp only [Finset.mem_image]
  use ∅
  refine ⟨?_, rfl⟩
  simp

/-- Births are stable under extension: if `q ∈ critVals p n L` then
`birth p n (L ++ [e]) q = birth p n L q`, and likewise `birthSet` and
`res` agree.  (The defining sets `{t | q ∈ critVals (take t)}` agree
for `t ≤ L.length`, and are nonempty there by hypothesis, so the
infima agree.)  This is what lets `disc` be stated with birth-in-`L`
and remain meaningful along the construction. -/
lemma birth_stable (L : List ℕ) (e : ℕ) {q : ℕ}
    (hq : q ∈ critVals p n L) :
    birth p n (L ++ [e]) q = birth p n L q ∧
    birthSet p n (L ++ [e]) q = birthSet p n L q ∧
    res p n (L ++ [e]) q = res p n L q := by
  -- First prove the defining sets for birth are equal
  have hset_eq : {t : ℕ | q ∈ critVals p n ((L ++ [e]).take t)} = {t : ℕ | q ∈ critVals p n (L.take t)} := by
    ext t
    by_cases htL : t ≤ L.length
    · simp [List.take_append_of_le_length htL]
    · have htL' : t ≥ (L ++ [e]).length := by simp; omega
      have htL'' : t > L.length := by omega
      simp only [Set.mem_setOf_eq]
      have heq1 : L.take t = L := by
        have key : ∀ l : List ℕ, l.length ≤ t → l.take t = l := by
          intro l hl
          rw [List.take_eq_take_min, min_eq_right hl, List.take_length]
        exact key L (by omega)
      have heq2 : (L ++ [e]).take t = L ++ [e] := by
        have key : ∀ l : List ℕ, l.length ≤ t → l.take t = l := by
          intro l hl
          rw [List.take_eq_take_min, min_eq_right hl, List.take_length]
        exact key (L ++ [e]) htL'
      rw [heq1, heq2]
      constructor
      · exact fun _ => hq
      · intro h; exact (critVals_append p n L e) h
  -- Therefore birth is the same
  have hbirth : birth p n (L ++ [e]) q = birth p n L q := by
    unfold birth
    rw [hset_eq]
  -- Birth is ≤ L.length, so (L ++ [e]).take (birth ...) = L.take (birth ...)
  have hb_le : birth p n L q ≤ L.length := by
    unfold birth
    apply Nat.sInf_le
    simp only [Set.mem_setOf_eq, List.take_length]
    exact hq
  have hbirth_set_eq : birthSet p n (L ++ [e]) q = birthSet p n L q := by
    unfold birthSet
    rw [hbirth]
    congr 1
    rw [List.take_append_of_le_length (hb_le : birth p n L q ≤ L.length)]
  have hres_eq : res p n (L ++ [e]) q = res p n L q := by
    unfold res
    rw [hbirth_set_eq]
  exact ⟨hbirth, hbirth_set_eq, hres_eq⟩


/-- The base case.  `critVals p n [] = {p}` (only the empty subset),
so `allVals p n [] = {p}` as well; `Good []` follows from `hp`, all
per-entry clauses being vacuous. -/
lemma good_nil (hp : p.Prime) : Good p n [] := by
  refine ⟨List.chain'_nil, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [allVals, List.toFinset_nil, Finset.powerset_empty]
    simp [hp]
  · intro q hq u h; cases h
  · intro u h q; cases h
  · intro u h v hv; cases h
  · intro u h; cases h

/-- (KEY) The residue is well defined: if `Good L`, `q ∈ critVals L`
is prime, and `(n+1) * (birthSet q).card < q`, then `res q` lies in
`{1,…,q−1}` and satisfies its defining avoidance property.
Proof: transfer `exists_good_residue` (already proved, in `ZMod q`)
through `ZMod.natCast_self_eq_zero` / `(ZMod.natCast_eq_zero_iff_dvd …)`
to exhibit one member of the defining set; `sInf` of a nonempty set of
naturals is a member.  Nonzeroness: `q ∈ birthSet q` (birth prefix
realizes `q` as a critical value — `Nat.sInf_mem` of the nonempty birth
set), so the pair `k = 0, c = q` rules out `s ≡ 0`; combined with
`s < q` this gives `1 ≤ s`.  NOTE: `exists_good_residue` needs
`n + 1 < q`; supply it from `(n+1)*card < q` and `card ≥ 1`
(`q ∈ birthSet q`). -/
lemma res_spec (L : List ℕ) (hg : Good p n L) {q : ℕ} (hq : q.Prime)
    (hmem : q ∈ critVals p n L)
    (hroom : (n + 1) * (birthSet p n L q).card < q) :
    1 ≤ res p n L q ∧ res p n L q < q ∧
      ∀ k ≤ n, ∀ c ∈ birthSet p n L q, ¬ q ∣ (k + 1) * res p n L q + c := by
  haveI : Fact q.Prime := ⟨hq⟩
  -- Local copy of exists_good_residue for this q
  have exists_good_residue_local : ∀ (n : ℕ)
      (C : Finset (ZMod q)) (hroom : (n + 1) * C.card < q) (hn : n + 1 < q),
      ∃ s : ZMod q, ∀ k : ℕ, k ≤ n → ∀ c ∈ C, ((k : ZMod q) + 1) * s + c ≠ 0 := by
    intro n C hroom hn
    let bad := Finset.biUnion (Finset.range (n + 1)) (fun k =>
      Finset.image (fun c => -((k + 1 : ZMod q)⁻¹) * c) C)
    have hbad_card : bad.card ≤ (n + 1) * C.card := by
      calc bad.card ≤ ∑ k ∈ Finset.range (n + 1), (Finset.image (fun c => -((k + 1 : ZMod q)⁻¹) * c) C).card :=
          Finset.card_biUnion_le
        _ ≤ ∑ k ∈ Finset.range (n + 1), C.card := by
            apply Finset.sum_le_sum; intros; apply Finset.card_image_le
        _ = (n + 1) * C.card := by simp
    have hqcard : Fintype.card (ZMod q) = q := ZMod.card q
    have hbaddr : bad.card < Fintype.card (ZMod q) := by
      rw [hqcard]
      exact Nat.lt_of_le_of_lt hbad_card hroom
    by_contra hall_bad
    push_neg at hall_bad
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
        have hqpos : 0 < q := Nat.Prime.pos hq
        rw [show (k : ZMod q) + 1 = (k + 1 : ℕ) by simp] at h
        rw [ZMod.natCast_eq_zero_iff] at h
        exact Nat.not_dvd_of_pos_of_lt (by omega) hlt h
      have hinv : ((k : ZMod q) + 1)⁻¹ * ((k : ZMod q) + 1) = 1 := by field_simp
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
  -- Define the set of good residues
  let S := {s : ℕ | 1 ≤ s ∧ s < q ∧ ∀ k ≤ n, ∀ c ∈ birthSet p n L q, ¬ q ∣ (k + 1) * s + c}
  -- Show S is nonempty using exists_good_residue
  have hnonempty : S.Nonempty := by
    -- First, show birthSet.card ≥ 1 (q ∈ birthSet q)
    have hq_in_birthSet : q ∈ birthSet p n L q := by
      unfold birthSet
      have hne : {t : ℕ | q ∈ critVals p n (L.take t)}.Nonempty := ⟨L.length, by
        simp only [Set.mem_setOf_eq]
        simp [hmem]⟩
      exact Nat.sInf_mem hne
    have hcard_pos : (birthSet p n L q).card ≥ 1 := Finset.card_pos.mpr ⟨q, hq_in_birthSet⟩
    -- Derive n + 1 < q
    have hnlt : n + 1 < q := by
      have : n + 1 ≤ (n + 1) * (birthSet p n L q).card := Nat.le_mul_of_pos_right _ hcard_pos
      exact Nat.lt_of_le_of_lt this hroom
    -- Apply exists_good_residue_local
    let C := (birthSet p n L q).image (fun x : ℕ => (x : ZMod q))
    have hroom' : (n + 1) * C.card < q := by
      calc (n + 1) * C.card ≤ (n + 1) * (birthSet p n L q).card := by
              apply Nat.mul_le_mul_left; exact Finset.card_image_le
        _ < q := hroom
    obtain ⟨s, hs⟩ := exists_good_residue_local n C hroom' hnlt
    -- Convert s to a natural number in [1, q-1]
    use s.val
    refine ⟨?_, s.val_lt, ?_⟩
    · -- Show 1 ≤ s.val: s ≠ 0 because q ∈ birthSet q means 0 ∈ C
      have hq_mod : (q : ZMod q) = 0 := by simp
      have h0_in_C : (0 : ZMod q) ∈ C := by
        rw [Finset.mem_image]
        refine ⟨q, hq_in_birthSet, ?_⟩
        exact hq_mod
      have hs_ne_zero : s ≠ 0 := by
        intro h
        specialize hs 0 (by omega) 0 h0_in_C
        simp [h] at hs
      exact Nat.one_le_iff_ne_zero.mpr (ZMod.val_ne_zero s |>.mpr hs_ne_zero)
    · -- Show the avoidance property
      intro k hk c hc
      have hcC : (c : ZMod q) ∈ C := Finset.mem_image_of_mem _ hc
      have := hs k hk c hcC
      have heq : ((k + 1) * s.val + c : ZMod q) = ((k + 1) * s + c : ZMod q) := by simp
      have hne : ((k + 1) * s.val + c : ZMod q) ≠ 0 := by rw [heq]; exact hs k hk c hcC
      intro hdvd
      apply hne
      rw [heq]
      rw [show (k + 1 : ZMod q) * s + c = ((k + 1) * s.val + c : ℕ) from by simp]
      obtain ⟨m, hm⟩ := hdvd
      simp [hm]
  have hsInf_mem : sInf S ∈ S := Nat.sInf_mem hnonempty
  exact hsInf_mem

/-- Growing room holds for every critical prime of a good list: for
`q = p` from the base case (`birthSet p = {p}`, card 1,
`(n+1) * 1 < p` is `hnp`); for a `q` born at entry `u` from the
`room` clause at `u` together with the newborn bound of the comment
above. -/
lemma room_of_good (hp : p.Prime) (hn : 1 ≤ n) (hnp : n + 2 ≤ p)
    (L : List ℕ) (hg : Good p n L) {q : ℕ}
    (hq : q.Prime) (hmem : q ∈ critVals p n L) :
    (n + 1) * (birthSet p n L q).card < q := by
  -- Let u = birth p n L q
  set u := birth p n L q with hu_def
  -- The birthSet is critVals at the birth prefix
  have hbirthSet : birthSet p n L q = critVals p n (L.take u) := rfl
  -- q ∈ birthSet q (since q ∈ critVals at birth prefix by definition of birth)
  have hq_mem_birthSet : q ∈ birthSet p n L q := by
    unfold birthSet
    have : q ∈ critVals p n (L.take u) := by
      have := Nat.sInf_mem (show {t | q ∈ critVals p n (List.take t L)}.Nonempty from by
        exact ⟨L.length, by simpa using hmem⟩)
      simpa using this
    exact this
  -- Case split on whether u = 0 or u > 0
  by_cases hu0 : u = 0
  · -- Case u = 0: q ∈ critVals [], so q = p
    simp only [hu0, List.take_zero] at hbirthSet hq_mem_birthSet
    -- critVals [] = {p}
    have hcriteq : critVals p n [] = {p} := by
      ext x
      simp [critVals]
      constructor <;> intro h <;> rw [h]
    rw [hbirthSet, hcriteq] at hq_mem_birthSet ⊢
    -- q = p
    have hqp : q = p := Finset.mem_singleton.mp hq_mem_birthSet
    rw [hqp]
    simp
    omega
  · -- Case u > 0: q born at some position
    -- u > 0 means u = u' + 1 for some u' ≥ 0
    have hu_pos : 0 < u := Nat.pos_of_ne_zero hu0
    set u' := u - 1 with hu'_def
    have hu_eq : u = u' + 1 := by omega
    -- u ≤ L.length since q ∈ critVals L
    have hu_le : u ≤ L.length := by
      unfold birth at hu_def
      have hmem' : q ∈ critVals p n (List.take L.length L) := by rw [List.take_length]; exact hmem
      exact Nat.sInf_le hmem'
    -- u' < L.length
    have hu'_lt : u' < L.length := by omega
    -- Apply room at u'
    have hroom := hg.room u' hu'_lt
    -- q ∉ critVals (L.take u') by minimality of birth
    have hq_not_in_old : q ∉ critVals p n (L.take u') := by
      intro h
      have : u ≤ u' := by
        unfold birth at hu_def
        exact Nat.sInf_le h
      omega
    -- L.take (u' + 1) = L.take u' ++ [L.get u']
    have htakesucc : L.take (u' + 1) = L.take u' ++ [L.get ⟨u', hu'_lt⟩] := by
      rw [List.take_succ, List.getElem?_eq_getElem hu'_lt]
      rfl
    -- q > L.get u' because q = p + ... + L.get u' + ... (L.get u' is in the sum)
    have hq_gt : q > L.get ⟨u', hu'_lt⟩ := by
      have hq_in_u : q ∈ critVals p n (L.take (u' + 1)) := by
        rw [hu_eq] at hbirthSet
        exact hbirthSet ▸ hq_mem_birthSet
      rw [htakesucc] at hq_in_u
      -- q = p + sum over some subset containing L.get u'
      rw [critVals] at hq_in_u
      -- The subset s for q must contain L.get u'; otherwise q ∈ critVals (L.take u')
      rw [Finset.mem_image] at hq_in_u
      obtain ⟨T, hT_mem, hT_eq⟩ := hq_in_u
      have hT_card : T.card ≤ n := by
        have := Finset.mem_filter.mp hT_mem
        exact this.2
      have hT_sub : T ⊆ (L.take u' ++ [L.get ⟨u', hu'_lt⟩]).toFinset := by
        have := Finset.mem_filter.mp hT_mem
        simp only [Finset.mem_powerset] at this
        exact this.1
      rw [← hT_eq]
      by_cases hget_in_T : L.get ⟨u', hu'_lt⟩ ∈ T
      · -- If L.get u' ∈ T, then q = p + ∑ x ∈ T, x ≥ p + L.get u' > L.get u'
        have hsum_ge : L.get ⟨u', hu'_lt⟩ ≤ ∑ x ∈ T, x := by
          have := Finset.single_le_sum (f := fun x => x) (fun _ _ => Nat.zero_le _) hget_in_T
          exact this
        omega
      · -- If L.get u' ∉ T, then T ⊆ (L.take u').toFinset, so q ∈ critVals (L.take u'), contradiction
        have hT_sub' : T ⊆ (L.take u').toFinset ∪ ({L.get ⟨u', hu'_lt⟩} : Finset ℕ) := by
          rw [List.toFinset_append] at hT_sub
          simp at hT_sub ⊢
          exact hT_sub
        have hT_sub_old : T ⊆ (L.take u').toFinset := by
          intro x hx
          have h := hT_sub' hx
          simp only [Finset.mem_union] at h
          rcases h with h1 | h2
          · exact h1
          · rw [Finset.mem_singleton] at h2
            rw [h2] at hx
            exact False.elim (hget_in_T hx)
        have hq_in_old : p + ∑ x ∈ T, x ∈ critVals p n (L.take u') := by
          unfold critVals
          exact Finset.mem_image.mpr ⟨T, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hT_sub_old, hT_card⟩, rfl⟩
        rw [hT_eq] at hq_in_old
        exact absurd hq_in_old hq_not_in_old
    -- Now we have: (n+1) * 2 * |critVals(prefix)| < L.get u' < q
    -- And |birthSet q| = |critVals (L.take u)| ≤ 2 * |critVals (L.take u')|
    -- So (n+1) * |birthSet q| < q
    have hbirthSet_eq : birthSet p n L q = critVals p n (L.take u) := rfl
    rw [hu_eq] at hbirthSet_eq
    have hcard_bound : (birthSet p n L q).card ≤ 2 * (critVals p n (L.take u')).card := by
      rw [hbirthSet_eq]
      set e := L.get ⟨u', hu'_lt⟩ with he_def
      -- critVals (take (u'+1)) has old values plus newborns of form p + e + sum(old subset)
      -- Number of newborns ≤ |critVals (take u')|
      -- So total ≤ 2 * |critVals (take u')|
      have key : (critVals p n (L.take (u' + 1))).card ≤
                 (critVals p n (L.take u')).card + (critVals p n (L.take u')).card := by
        rw [htakesucc]
        -- critVals (M ++ [e]) consists of:
        -- 1. Old: p + sum of subset of M (at most |critVals M|)
        -- 2. Newborns: p + e + sum of subset of M (at most |critVals M|)
        -- So total ≤ 2 * |critVals M|
        -- We show critVals (M ++ [e]) ⊆ critVals M ∪ {e + c | c ∈ critVals M}
        have hunion : (critVals p n (L.take u' ++ [e]) : Finset ℕ) ⊆
                      critVals p n (L.take u') ∪ (critVals p n (L.take u')).image (fun c : ℕ => c + e) := by
          intro x hx
          simp only [Finset.mem_union]
          rw [critVals] at hx ⊢
          rw [Finset.mem_image] at hx
          obtain ⟨s, hs_mem, rfl⟩ := hx
          rw [Finset.mem_filter, Finset.mem_powerset] at hs_mem
          by_cases he_in_s : e ∈ s
          · -- e ∈ s: output is e + (p + sum of s \ {e})
            right
            set t := s \ {e} with ht_def
            rw [Finset.mem_image]
            use p + ∑ x ∈ t, x
            refine ⟨?_, ?_⟩
            · rw [Finset.mem_image]
              use t
              refine ⟨?_, rfl⟩
              rw [Finset.mem_filter]
              constructor
              · rw [Finset.mem_powerset]
                intro y hy
                have hyt : y ∈ t := hy
                rw [ht_def] at hyt
                have hy_s : y ∈ s := Finset.mem_sdiff.mp hyt |>.1
                have hy_ne_e : y ≠ e := by
                  have := Finset.mem_sdiff.mp hyt |>.2
                  simp at this
                  exact this
                have hy_append : y ∈ (List.take u' L ++ [e]).toFinset := hs_mem.1 hy_s
                rw [List.mem_toFinset, List.mem_append] at hy_append
                rcases hy_append with hy1 | hy2
                · rwa [List.mem_toFinset]
                · simp at hy2
                  exact absurd hy2 hy_ne_e
              · rw [ht_def]
                simp [Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.mpr he_in_s)]
                omega
            · -- (p + ∑ x ∈ t, x) + e = p + ∑ x ∈ s, x
              rw [ht_def]
              have hsub : {e} ⊆ s := Finset.singleton_subset_iff.mpr he_in_s
              rw [← Finset.sum_sdiff hsub]
              rw [add_assoc, Finset.sum_singleton]
          · -- e ∉ s: output is p + sum of s, which is in critVals M
            left
            rw [Finset.mem_image]
            use s
            refine ⟨?_, rfl⟩
            rw [Finset.mem_filter]
            refine ⟨?_, hs_mem.2⟩
            rw [Finset.mem_powerset]
            intro y hy
            have := hs_mem.1 hy
            rw [List.mem_toFinset] at this
            rw [List.mem_append] at this
            rcases this with h1 | h2
            · rwa [List.mem_toFinset]
            · simp at h2
              exact False.elim (he_in_s (h2 ▸ hy))
        have h1 : (critVals p n (L.take u' ++ [e]) : Finset ℕ).card ≤
                  (critVals p n (L.take u') ∪ (critVals p n (L.take u')).image (fun c : ℕ => c + e)).card :=
          Finset.card_le_card hunion
        have h2 : (critVals p n (L.take u') ∪ (critVals p n (L.take u')).image (fun c : ℕ => c + e)).card ≤
                  (critVals p n (L.take u')).card + ((critVals p n (L.take u')).image (fun c : ℕ => c + e)).card :=
          Finset.card_union_le _ _
        have h3 : ((critVals p n (L.take u')).image (fun c : ℕ => c + e)).card ≤
                  (critVals p n (L.take u')).card := Finset.card_image_le
        linarith
      linarith
    calc (n + 1) * (birthSet p n L q).card
        ≤ (n + 1) * (2 * (critVals p n (L.take u')).card) := Nat.mul_le_mul_left _ hcard_bound
      _ = (n + 1) * ((critVals p n (L.take u')).card + (critVals p n (L.take u')).card) := by ring_nf
      _ < L.get ⟨u', hu'_lt⟩ := hroom
      _ < q := hq_gt


/-- (KEY) Confinement.  For a good `L`, a critical prime `q`, and ANY
critical value `c' ∈ critVals L`:
`∃ c ∈ birthSet q, ∃ k ≤ n, c' ≡ c + k * res q [MOD q]`.
Proof: write `c' = p + ∑_{x ∈ s} x` with `s ⊆ L.toFinset`,
`s.card ≤ n`.  Split `s` into elements at positions `< birth q`
(giving `s_old`) and `≥ birth q` (`s_new`); positions are unique by
`mono` (strict increase ⇒ `Nodup`).  Each element of `s_new` is
`≡ res q (mod q)` by `disc` (its position is `≥ birth`, and
`q ∈ critVals` of the whole list restricts to the birth prefix by
definition of birth).  So `c' ≡ (p + ∑ s_old) + s_new.card * res q`.
And `p + ∑ s_old ∈ birthSet q` because `s_old` is a ≤n-subset of the
birth prefix.  Take `k = s_new.card ≤ s.card ≤ n`. -/
lemma confinement (L : List ℕ) (hg : Good p n L) {q : ℕ}
    (hq : q.Prime) (hmem : q ∈ critVals p n L)
    {c' : ℕ} (hc' : c' ∈ critVals p n L) :
    ∃ c ∈ birthSet p n L q, ∃ k ≤ n,
      (c' : ZMod q) = (c : ZMod q) + (k : ZMod q) * (res p n L q : ZMod q) := by
  -- Extract the subset s from c'
  rw [critVals] at hc'
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hc'
  -- L has no duplicates since it's strictly increasing
  have hn_dup : L.Nodup := List.chain'_iff_pairwise.mp hg.mono |>.nodup
  -- Define s_old and s_new based on position
  let birthL := birth p n L q
  let s_old := s.filter (fun x => List.idxOf x L < birthL)
  let s_new := s.filter (fun x => birthL ≤ List.idxOf x L)
  -- Key facts about s_old and s_new
  have hs_partition : s = s_old ∪ s_new := by
    ext x
    simp only [Finset.mem_union, Finset.mem_filter, s_old, s_new]
    by_cases hx : x ∈ s <;> simp [hx, Nat.lt_or_ge]
  have hs_disj : Disjoint s_old s_new := by
    apply Finset.disjoint_left.mpr
    intro x hx hx'
    simp only [Finset.mem_filter, s_old, s_new] at hx hx'
    omega
  have hs_sum : ∑ x ∈ s, x = ∑ x ∈ s_old, x + ∑ x ∈ s_new, x := by
    rw [hs_partition, Finset.sum_union hs_disj]
  -- Each element of s_new is at position ≥ birthL, so by disc it's ≡ res q (mod q)
  have hs_new_mod : ∀ x ∈ s_new, x % q = res p n L q % q := by
    intro x hx
    simp only [Finset.mem_filter, s_new] at hx
    have hs_mem : s ∈ L.toFinset.powerset := (Finset.mem_filter.mp hs).1
    have hx_mem : x ∈ L.toFinset := Finset.mem_powerset.mp hs_mem hx.1
    have hx_in : x ∈ L := List.mem_toFinset.mp hx_mem
    have hidx : List.idxOf x L < L.length := List.idxOf_lt_length_iff.mpr hx_in
    have hbirth_le : birthL ≤ List.idxOf x L := hx.2
    have hget : L.get ⟨List.idxOf x L, hidx⟩ = x := List.getElem_idxOf hidx
    rw [← hget]
    exact hg.disc q hmem (List.idxOf x L) hidx hbirth_le
  -- s_old ⊆ (L.take birthL).toFinset, so p + ∑ x ∈ s_old, x ∈ birthSet p n L q
  have hs_old_subset : s_old ⊆ (L.take birthL).toFinset := by
    intro x hx
    simp only [Finset.mem_filter, s_old] at hx
    have hs_mem : s ∈ L.toFinset.powerset := (Finset.mem_filter.mp hs).1
    have hx_mem : x ∈ L.toFinset := Finset.mem_powerset.mp hs_mem hx.1
    rw [List.mem_toFinset]
    have hbirth_le_len : birthL ≤ L.length := Nat.sInf_le (by simp [hmem])
    have hlen : List.idxOf x L < (List.take birthL L).length := by simp [hx.2, hbirth_le_len]
    have hle : List.idxOf x L < L.length := lt_of_lt_of_le hx.2 hbirth_le_len
    have heq1 : L[List.idxOf x L] = x := List.getElem_idxOf hle
    have heq2 : (List.take birthL L)[List.idxOf x L]'hlen = L[List.idxOf x L] := by
      simp [List.getElem_take]
    rw [← heq1, ← heq2]
    exact List.getElem_mem hlen
  have hs_old_card : s_old.card ≤ n := by
    calc s_old.card ≤ s.card := Finset.card_le_card (Finset.filter_subset _ _)
      _ ≤ n := (Finset.mem_filter.mp hs).2
  have hc_birth : p + ∑ x ∈ s_old, x ∈ birthSet p n L q := by
    simp only [birthSet, critVals]
    exact Finset.mem_image.mpr ⟨s_old, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hs_old_subset, hs_old_card⟩, rfl⟩
  -- Show ∑ x ∈ s_new, x ≡ s_new.card * res q (mod q)
  have hs_new_sum_mod : (∑ x ∈ s_new, x) % q = (s_new.card * res p n L q) % q := by
    have heq : ∑ x ∈ s_new, x % q = s_new.card * (res p n L q % q) := by
      calc ∑ x ∈ s_new, x % q = ∑ _x ∈ s_new, res p n L q % q := Finset.sum_congr rfl hs_new_mod
        _ = s_new.card * (res p n L q % q) := by simp
    conv_lhs => rw [← Nat.mod_mod_of_dvd _ (dvd_refl q), Finset.sum_nat_mod, heq]
    simp [Nat.mul_mod, Nat.mod_mod]
  -- Now construct the result
  use p + ∑ x ∈ s_old, x, hc_birth, s_new.card
  refine ⟨?_, ?_⟩
  · calc s_new.card ≤ s.card := Finset.card_le_card (Finset.filter_subset _ _)
      _ ≤ n := (Finset.mem_filter.mp hs).2
  · -- Show (p + ∑ x ∈ s, x) ≡ (p + ∑ x ∈ s_old, x) + s_new.card * res q (mod q)
    have hsum_eq : (p + ∑ x ∈ s, x) = (p + ∑ x ∈ s_old, x) + ∑ x ∈ s_new, x := by
      rw [hs_sum]; ring
    rw [hsum_eq]
    have : (∑ x ∈ s_new, x) ≡ (s_new.card * res p n L q) [MOD q] := by
      rw [Nat.ModEq, hs_new_sum_mod]
    rw [Nat.ModEq] at this
    norm_cast
    rw [ZMod.natCast_eq_natCast_iff']
    simp [Nat.add_mod, this]

/-- Tracked primes: critical ∪ urgent.  Finite: critical primes are
elements of the finset `critVals`; urgent primes lie below
`card + 2`. -/
noncomputable def tracked (L : List ℕ) : Finset ℕ :=
  ((critVals p n L).filter Nat.Prime) ∪
    ((Finset.range ((critVals p n L).card + 2)).filter fun q =>
      q.Prime ∧ q ∉ critVals p n L)

/-- CRT over the tracked primes: there exist `A > 0` and `B` with
`A = ∏ tracked`, every prime divisor of `A` tracked, `B ≡ res q (mod q)`
for critical `q`, and `q ∣ B` for urgent `q`.  Distinct primes are
pairwise coprime; iterate `Nat.chineseRemainder` over the finset (or
use the `ZMod` product equivalence).  Routine but fiddly; isolate. -/
lemma crt_exists (L : List ℕ) (hg : Good p n L) :
    ∃ A B : ℕ, 0 < A ∧
      (∀ q, q.Prime → (q ∣ A ↔ q ∈ tracked p n L)) ∧
      (∀ q ∈ tracked p n L, q ∈ critVals p n L →
        B % q = res p n L q % q) ∧
      (∀ q ∈ tracked p n L, q ∉ critVals p n L → q ∣ B) := by
  -- A is the product of all tracked primes
  let A := (tracked p n L).prod id
  -- Define the target residue for each tracked prime
  let r : ℕ → ℕ := fun q => if q ∈ critVals p n L then res p n L q else 0
  -- B from CRT: B ≡ r q (mod q) for all q ∈ tracked
  have hcoprime : ∀ q₁ q₂, q₁ ∈ tracked p n L → q₂ ∈ tracked p n L → q₁ ≠ q₂ → Nat.Coprime q₁ q₂ := by
    intro q₁ q₂ hq₁ hq₂ hne
    have hp1 : q₁.Prime := by
      rw [tracked] at hq₁
      exact (Finset.mem_union.mp hq₁).elim
        (fun h => (Finset.mem_filter.mp h).2)
        (fun h => (Finset.mem_filter.mp h).2.1)
    have hp2 : q₂.Prime := by
      rw [tracked] at hq₂
      exact (Finset.mem_union.mp hq₂).elim
        (fun h => (Finset.mem_filter.mp h).2)
        (fun h => (Finset.mem_filter.mp h).2.1)
    exact Nat.coprime_primes hp1 hp2 |>.mpr hne
  -- Properties of A = product of tracked primes
  -- Show B exists using CRT
  have hA_pos : 0 < A := Finset.prod_pos fun q hq => Nat.Prime.pos (by
    rw [tracked] at hq
    exact (Finset.mem_union.mp hq).elim
      (fun h => (Finset.mem_filter.mp h).2)
      (fun h => (Finset.mem_filter.mp h).2.1))
  -- Key lemma: q | A iff q ∈ tracked (for prime q)
  have hA_div : ∀ q, q.Prime → (q ∣ A ↔ q ∈ tracked p n L) := by
    intro q hq
    have hprod : A = (tracked p n L).prod id := rfl
    rw [hprod]
    constructor
    · intro hdiv
      by_contra hnotin
      have hcop : ∀ x ∈ tracked p n L, Nat.Coprime q x := by
        intro x hx
        have hxq : x ≠ q := fun eq => hnotin (eq.symm ▸ hx)
        have hqx : q ≠ x := hxq.symm
        have hx_prime : x.Prime := by
          rw [tracked] at hx
          exact (Finset.mem_union.mp hx).elim
            (fun h => (Finset.mem_filter.mp h).2)
            (fun h => (Finset.mem_filter.mp h).2.1)
        exact Nat.coprime_primes hq hx_prime |>.mpr hqx
      have hcop_prod : Nat.Coprime q ((tracked p n L).prod id) := by
        apply Nat.Coprime.prod_right
        exact hcop
      exact Nat.Prime.not_dvd_one hq (hcop_prod.dvd_of_dvd_mul_left (by simpa using hdiv))
    · intro hmem
      exact Finset.dvd_prod_of_mem _ hmem
  -- Now construct B using CRT
  -- Define target residues: res q for critical q, 0 for urgent q
  let r : ℕ → ℕ := fun q => if q ∈ critVals p n L then res p n L q else 0
  -- Use ZMod.chineseRemainder to get existence via ring isomorphism
  have hb : ∃ B, ∀ q ∈ tracked p n L, B % q = r q % q := by
    -- For empty tracked, B = 0 works
    by_cases hempty : (tracked p n L).Nonempty
    · -- For nonempty tracked, we use CRT
      -- Use a direct existence argument
      have : ∃ B : ℕ, ∀ q ∈ tracked p n L, B ≡ r q [MOD q] := by
        -- CRT: existence for pairwise coprime moduli
        have hcop_all : ∀ s : Finset ℕ, (∀ q ∈ s, q ∈ tracked p n L) →
          (∀ q₁ q₂, q₁ ∈ s → q₂ ∈ s → q₁ ≠ q₂ → Nat.Coprime q₁ q₂) →
          ∃ B : ℕ, ∀ q ∈ s, B ≡ r q [MOD q] := by
          intro s hs hcop_s
          induction s using Finset.induction_on with
          | empty => exact ⟨0, by simp⟩
          | insert ha ih hain =>
            -- Get B₀ for ih
            have hiht : ∀ q ∈ ih, q ∈ tracked p n L := fun q hq => hs q (Finset.mem_insert_of_mem hq)
            have hicop : ∀ q₁ q₂, q₁ ∈ ih → q₂ ∈ ih → q₁ ≠ q₂ → q₁.Coprime q₂ :=
              fun q₁ q₂ hq₁ hq₂ hne => hcop_s q₁ q₂ (Finset.mem_insert_of_mem hq₁) (Finset.mem_insert_of_mem hq₂) hne
            have ⟨B₀, hB₀⟩ := ‹(∀ q ∈ ih, q ∈ tracked p n L) → (∀ q₁ q₂, q₁ ∈ ih → q₂ ∈ ih → q₁ ≠ q₂ → q₁.Coprime q₂) → ∃ B, ∀ q ∈ ih, B ≡ r q [MOD q]› hiht hicop
            -- ha is coprime to all q ∈ ih
            have hha_tracked : ha ∈ tracked p n L := hs ha (Finset.mem_insert_self ha ih)
            -- M = ∏ q ∈ ih, q
            let M := ih.prod id
            have hcop_ha_M : Nat.Coprime ha M := by
              apply Nat.Coprime.prod_right
              intro q hq
              have hne : ha ≠ q := fun h => hain (h ▸ hq)
              exact hcop_s ha q (Finset.mem_insert_self ha ih) (Finset.mem_insert_of_mem hq) hne
            -- Find k such that B₀ + k * M ≡ r ha [MOD ha]
            -- We use the extended Euclidean algorithm implicitly
            -- k * M ≡ r ha - B₀ [MOD ha]
            -- Since gcd(ha, M) = 1, M has an inverse mod ha
            have hha_pos : 0 < ha := by
              have hprime : ha.Prime := by
                have := hs ha (Finset.mem_insert_self ha ih)
                rw [tracked] at this
                exact (Finset.mem_union.mp this).elim (fun h => (Finset.mem_filter.mp h).2)
                  (fun h => (Finset.mem_filter.mp h).2.1)
              exact hprime.pos
            -- Use Nat.chineseRemainder to find k with k ≡ B₀ [MOD M] and k ≡ r ha [MOD ha]
            have ⟨k, hk_M, hk_ha⟩ := Nat.chineseRemainder hcop_ha_M.symm B₀ (r ha)
            use k
            intro q hq
            by_cases hq_ha : q = ha
            · rw [hq_ha]
              exact hk_ha
            · have hq_ih : q ∈ ih := Finset.mem_insert.mp hq |>.resolve_left hq_ha
              -- k ≡ B₀ [MOD M] and q | M, so k ≡ B₀ [MOD q]
              -- B₀ ≡ r q [MOD q] by hB₀
              have hq_dvd_M : q ∣ M := Finset.dvd_prod_of_mem id hq_ih
              exact (hk_M.of_dvd hq_dvd_M).trans (hB₀ q hq_ih)
        exact hcop_all (tracked p n L) (fun q hq => hq) hcoprime
      obtain ⟨B, hB⟩ := this
      use B
      intro q hq
      exact hB q hq
    · use 0
      intro q hq
      exfalso
      exact hempty ⟨q, hq⟩
  obtain ⟨B, hB⟩ := hb
  use A, B
  refine ⟨hA_pos, hA_div, ?_, ?_⟩
  · intro q hq_t hq_c
    have hr : r q = res p n L q := if_pos hq_c
    rw [← hr]
    exact hB q hq_t
  · intro q hq_t hq_nocrit
    have hr : r q = 0 := if_neg hq_nocrit
    have hBq := hB q hq_t
    rw [hr] at hBq
    exact Nat.dvd_of_mod_eq_zero hBq


/-- (KEY) Admissibility of the family `m ↦ A*m + (B + c)`, `c` ranging
over `critVals L`.  Three exhaustive cases for a test prime `q`:
1. `q ∤ A` (untracked): then `q > (critVals L).card + 1 > card`, and
   each `c` forbids at most one residue class of `m` (as `q ∤ A`,
   `A` is invertible mod `q`), so some `m` avoids all of them.
2. `q` urgent: `A*m + B + c ≡ 0 + 0 + c ≡ c (mod q)`, and `c` is
   prime (from `Good.primes`, `critVals ⊆ allVals`) with `c ≠ q`
   (`q ∉ critVals`), so `q ∤ c`.
3. `q` critical: `A*m + B + c ≡ res q + c`; by `confinement`,
   `c ≡ c₀ + k * res q` with `c₀ ∈ birthSet q`, `k ≤ n`, so the value
   is `≡ (k+1) * res q + c₀ ≢ 0` by `res_spec` (`k + 1 ≤ n + 1`).
Note for case 2/3 the congruences for `B` come from `crt_exists` and
`q ∣ A` kills the `A*m` term. -/
lemma admissible (L : List ℕ) (hg : Good p n L)
    (hp : p.Prime) (hn : 1 ≤ n) (hnp : n + 2 ≤ p)
    {A B : ℕ} (hA : 0 < A)
    (hAfac : ∀ q, q.Prime → (q ∣ A ↔ q ∈ tracked p n L))
    (hBcrit : ∀ q ∈ tracked p n L, q ∈ critVals p n L →
      B % q = res p n L q % q)
    (hBurg : ∀ q ∈ tracked p n L, q ∉ critVals p n L → q ∣ B) :
    ∀ q : ℕ, q.Prime → ∃ m : ℕ, ∀ c ∈ critVals p n L,
      ¬ q ∣ A * m + (B + c) := by
  intro q hq
  by_cases hq_tracked : q ∈ tracked p n L
  · -- Case: q is tracked
    by_cases hq_crit : q ∈ critVals p n L
    · -- Case 3: q is critical
      use 0
      intro c hc
      -- q ∣ A since q is tracked
      have hqA : q ∣ A := (hAfac q hq).mpr hq_tracked
      -- B ≡ res q (mod q)
      have hBmod : B % q = res p n L q % q := hBcrit q hq_tracked hq_crit
      -- By confinement, c ≡ c₀ + k * res q (mod q)
      have hconf := confinement p n L hg hq hq_crit hc
      obtain ⟨c₀, hc₀, k, hk, hc_eq⟩ := hconf
      -- Need to show q ∤ B + c
      intro hdiv
      -- From hc_eq in ZMod q, get c ≡ c₀ + k * res q (mod q)
      haveI := Fact.mk hq
      have hc_mod : c % q = (c₀ + k * res p n L q) % q := by
        have := hc_eq
        norm_cast at this
        rw [ZMod.natCast_eq_natCast_iff'] at this
        exact this
      -- B + c ≡ res q + c₀ + k * res q = c₀ + (k+1)*res q (mod q)
      have hsum_mod : (B + c) % q = (c₀ + (k + 1) * res p n L q) % q := by
        have hBmod' : B ≡ res p n L q [MOD q] := hBmod
        have hc_mod' : c ≡ c₀ + k * res p n L q [MOD q] := hc_mod
        have h1 : B + c ≡ res p n L q + (c₀ + k * res p n L q) [MOD q] := Nat.ModEq.add hBmod' hc_mod'
        have h2 : (res p n L q + (c₀ + k * res p n L q)) = c₀ + (k + 1) * res p n L q := by ring
        rw [Nat.ModEq] at h1
        rw [h1, h2]
      simp only [mul_zero, zero_add] at hdiv
      have hdiv' : (B + c) % q = 0 := Nat.mod_eq_zero_of_dvd hdiv
      rw [hsum_mod] at hdiv'
      -- Now need (n+1) * card(birthSet q) < q to apply res_spec
      have hroom := room_of_good p n hp hn hnp L hg hq hq_crit
      have := res_spec p n L hg hq hq_crit hroom
      exact this.2.2 k hk c₀ hc₀ (Nat.dvd_of_mod_eq_zero (by rw [add_comm] at hdiv'; exact hdiv'))
    · -- Case 2: q is urgent (tracked but not critical)
      use 0
      intro c hc
      -- q ∣ A since q is tracked
      have hqA : q ∣ A := (hAfac q hq).mpr hq_tracked
      -- q ∣ B since q is tracked but not critical (urgent)
      have hqB : q ∣ B := hBurg q hq_tracked hq_crit
      simp only [mul_zero, zero_add] at *
      -- A * 0 + B + c = B + c ≡ c (mod q)
      -- c is prime and c ≠ q (since q ∉ critVals)
      have hc_subset : c ∈ allVals p n L := by
        rw [critVals] at hc
        obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hc
        simp only [allVals, Finset.mem_image, Finset.mem_filter, Finset.mem_powerset]
        exact ⟨s, ⟨Finset.mem_powerset.mp (Finset.mem_filter.mp hs).1, by linarith [(Finset.mem_filter.mp hs).2]⟩, rfl⟩
      have hc_prime : c.Prime := hg.primes c hc_subset
      intro hdiv
      have : q ∣ B + c := hdiv
      have hdiv_c : q ∣ c := by
        have : (B + c) % q = c % q := by
          rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hqB, zero_add, Nat.mod_mod]
        have hzero : (B + c) % q = 0 := Nat.mod_eq_zero_of_dvd hdiv
        rw [hzero] at this
        exact Nat.dvd_of_mod_eq_zero this.symm
      -- q and c are both prime, q ∣ c means q = c
      have heq : q = c := by
        exact (Nat.prime_dvd_prime_iff_eq hq hc_prime).mp hdiv_c
      exact hq_crit (heq.symm ▸ hc)
  · -- Case 1: q is untracked
    -- q ∉ tracked means q ∉ critVals and q ≥ (critVals).card + 2
    have hq_not_crit : q ∉ critVals p n L := by
      intro h
      apply hq_tracked
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨h, hq⟩)
    have hq_ge : (critVals p n L).card + 2 ≤ q := by
      by_contra h
      push_neg at h
      apply hq_tracked
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h, hq, hq_not_crit⟩)
    -- q ∤ A since q is untracked
    have hq_nodiv : ¬ q ∣ A := by
      rw [hAfac q hq]
      exact hq_tracked
    -- For each c, there's at most one forbidden residue class for m mod q
    -- We need to find m avoiding all of them
    haveI : Fact q.Prime := ⟨hq⟩
    -- Key: A is invertible mod q since q ∤ A
    have hA_coprime : Nat.Coprime A q := Nat.Coprime.symm (hq.coprime_iff_not_dvd.mpr hq_nodiv)
    have hA_ne_zero : (A : ZMod q) ≠ 0 := by
      simp only [ne_eq, ZMod.natCast_eq_zero_iff]
      exact hq_nodiv
    have hA_unit : IsUnit (A : ZMod q) := by
      apply IsUnit.mk0
      exact hA_ne_zero
    -- For each c, the forbidden m is -A⁻¹ * (B + c) mod q
    -- There are at most |critVals| forbidden residues, but q > |critVals|
    -- Build the set of forbidden residues
    let badResidues : Finset (ZMod q) := (critVals p n L).image (fun c : ℕ => -(A : ZMod q)⁻¹ * (B + c))
    -- |badResidues| ≤ |critVals|
    have hbad_card : badResidues.card ≤ (critVals p n L).card := Finset.card_image_le
    -- q > |critVals| ≥ |badResidues|, so there's a good residue
    have hq_gt : q > badResidues.card := by linarith
    -- ZMod q has q elements
    have hcard : Fintype.card (ZMod q) = q := ZMod.card q
    -- There exists a residue not in badResidues
    have hnonempty : ∃ r : ZMod q, r ∉ badResidues := by
      by_contra hall
      push_neg at hall
      have : badResidues = Finset.univ := by ext; simp [hall]
      rw [this] at hbad_card
      simp at hbad_card
      linarith
    obtain ⟨r, hr⟩ := hnonempty
    -- Use r as our m
    use r.val
    intro c hc
    -- Show q ∤ A * r + (B + c)
    intro hdiv
    -- Convert to ZMod: A * r + (B + c) = 0
    have hzero : (A : ZMod q) * r + (B + c) = 0 := by
      have hdvd : q ∣ A * r.val + (B + c) := hdiv
      obtain ⟨k, hk⟩ := hdvd
      have heq : (A * r.val + (B + c) : ℕ) = q * k := hk
      rw [show (r : ZMod q) = ↑r.val from r.natCast_zmod_val.symm]
      rw [show (A : ZMod q) * ↑r.val + (↑B + ↑c) = ↑(A * r.val + (B + c)) from by simp]
      rw [heq]
      simp
    -- So r = -A⁻¹ * (B + c)
    have hbad : r = -(A : ZMod q)⁻¹ * (B + c) := by
      have hinv : (A : ZMod q)⁻¹ * (A : ZMod q) = 1 := inv_mul_cancel₀ hA_ne_zero
      have heq : (A : ZMod q) * r = -(B + c) := by linear_combination hzero
      calc r = 1 * r := by ring
        _ = ((A : ZMod q)⁻¹ * (A : ZMod q)) * r := by rw [hinv]
        _ = (A : ZMod q)⁻¹ * ((A : ZMod q) * r) := by ring
        _ = (A : ZMod q)⁻¹ * (-(B + c)) := by rw [heq]
        _ = -(A : ZMod q)⁻¹ * (B + c) := by ring
    exact hr (Finset.mem_image.mpr ⟨c, hc, hbad.symm⟩)


/-- (KEY) The step.  From `Good L` produce `e` with `Good (L ++ [e])`.
Assemble: `crt_exists` + `admissible` + `dickson_for_linear_forms`
(from `Main.lean`, instantiated with the finite index `critVals L`,
forms `m ↦ A*m + (B + c)`) give an infinite set of `m` for which ALL
`A*m + B + c` are prime.  An infinite set of naturals contains
elements above any bound (`Set.Infinite.exists_gt`); choose `m` with
`e := A*m + B` exceeding both `max (allVals L)` and
`(n+1) * (2 * (critVals L).card)`.  Then check the fields of
`Good (L ++ [e])` one by one:
* `mono`: `e >` every old entry (old entries are `< p + entry ≤`
  some old `allVal < e`).
* `primes`: new ≤(n+1)-sums either avoid `e` (old, prime by `hg`) or
  equal `e + c` with `c ∈ critVals L` an old ≤n-sum — and
  `e + c = A*m + (B + c)` is prime by the choice of `m`.
* `disc` for old entries: births of old critical primes are stable
  (`birth_stable`), residues unchanged; for newborn critical primes
  the condition constrains only entries at positions `≥ birth =
  length (L ++ [e])`… i.e. none yet, vacuous.  `disc` for the new
  entry: for `q` critical in `L`, `e = A*m + B ≡ B ≡ res q` since
  `q ∣ A`.
* `frozen` for the new entry: `q` urgent at prefix `L` divides `A`
  (tracked) and `B`, hence `e`.  Old entries unchanged (urgency at
  their prefixes is a statement about those prefixes only).
* `big`, `room` for the new entry: the two lower bounds imposed on
  `e`; old entries unchanged. -/
lemma step (hp : p.Prime) (hn : 1 ≤ n) (hnp : n + 2 ≤ p)
    (hDickson : DicksonConjecture)
    (L : List ℕ) (hg : Good p n L) :
    ∃ e : ℕ, Good p n (L ++ [e]) := by
  -- Get A, B from CRT
  obtain ⟨A, B, hApos, hAfac, hBcrit, hBurg⟩ := crt_exists p n L hg
  -- The family {m ↦ A*m + (B + c) | c ∈ critVals L} is admissible
  have hadm : ∀ q : ℕ, q.Prime → ∃ m : ℕ, ∀ c ∈ critVals p n L, ¬ q ∣ A * m + (B + c) :=
    admissible p n L hg hp hn hnp hApos hAfac hBcrit hBurg
  -- Set up indexed family: ι = {c : ℕ // c ∈ critVals L}
  let ι := {c : ℕ // c ∈ critVals p n L}
  -- Define a and b
  let a : ι → ℕ := fun c => A
  let b : ι → ℕ := fun c => B + c
  -- a i = A > 0 for all i
  have ha : ∀ i : ι, 0 < a i := fun _ => hApos
  -- The family is admissible
  have hadm' : Admissible a b := by
    intro q hq
    obtain ⟨m, hm⟩ := hadm q hq
    exact ⟨m, fun i => hm i i.prop⟩
  -- By Dickson, infinitely many m make all forms prime
  have hinf := dickson_for_linear_forms hDickson ι a b ha hadm'
  -- Define the bound: e must exceed max of allVals L and room bound
  have hall_nonempty : (allVals p n L).Nonempty := by
    use p
    have h : p ∈ critVals p n L := p_mem_critVals p n L
    have hsub : critVals p n L ⊆ allVals p n L := by
      unfold critVals allVals
      intro x hx
      simp only [Finset.mem_image] at hx ⊢
      obtain ⟨s, hs, rfl⟩ := hx
      simp only [Finset.mem_filter, Finset.mem_powerset] at hs ⊢
      exact ⟨s, ⟨hs.1, by omega⟩, rfl⟩
    exact hsub h
  let bound := max ((allVals p n L).max' hall_nonempty + 1) ((n + 1) * 2 * (critVals p n L).card + 1)
  -- The good m set is infinite, so find one large enough
  have hbound_mem : ∀ m, (∀ i : ι, (a i * m + b i).Prime) → A * m + B > bound → True := fun _ _ _ => trivial
  obtain ⟨m, hm_prime, hm_large⟩ : ∃ m, (∀ i : ι, (a i * m + b i).Prime) ∧ A * m + B > bound := by
    have : {m | ∀ i : ι, (a i * m + b i).Prime}.Infinite := hinf
    obtain ⟨m, hm⟩ := this.exists_gt bound
    refine ⟨m, hm.1, ?_⟩
    have hApos : 0 < A := hApos
    have : m > bound := hm.2
    calc A * m + B ≥ m + B := by nlinarith
      _ > bound := by linarith
  -- Set e = A * m + B
  let e := A * m + B
  use e
  refine ⟨?mono, ?primes, ?disc, ?frozen, ?big, ?room⟩
  · -- mono: L ++ [e] is strictly increasing
    have hmono_L : L.Chain' (· < ·) := hg.mono
    have hn_dup : L.Nodup := List.chain'_iff_pairwise.mp hmono_L |>.nodup
    -- Direct construction
    apply List.chain'_append.mpr
    refine ⟨hmono_L, ?_, ?_⟩
    · -- IsChain [e] - singleton is a chain
      exact @List.isChain_singleton _ (fun x1 x2 => x1 < x2) e
    · -- ∀ x ∈ L.getLast?, ∀ y ∈ [e].head?, x < y (vacuously true)
      intro x hx
      cases L with
      | nil => simp at hx
      | cons hd tl =>
        simp [List.getLast?] at hx
        simp [List.head?]
        subst hx
        -- Need to show (hd :: tl).getLast < e
        -- The last element is in L, and L.last < allVals.max < bound < e
        have hne : hd :: tl ≠ [] := by simp
        set lastEl := (hd :: tl).getLast hne with hlastEl_def
        have hmem : lastEl ∈ (hd :: tl) := List.getLast_mem hne
        have hpx : p + lastEl ∈ allVals p n (hd :: tl) := by
          rw [allVals]
          apply Finset.mem_image.mpr
          use {lastEl}
          simp [Finset.mem_filter, Finset.mem_powerset, List.mem_toFinset, Finset.sum_singleton]
          exact List.mem_cons.mp hmem
        have hle : lastEl < (allVals p n (hd :: tl)).max' hall_nonempty :=
          lt_of_lt_of_le (by omega) (Finset.le_max' _ _ hpx)
        have hle_bound : lastEl < bound := by
          have h1 : (allVals p n (hd :: tl)).max' hall_nonempty < bound := by
            apply lt_of_lt_of_le _ (le_max_left _ _)
            simp
          omega
        simp only [e]
        linarith
  · -- primes: all values in allVals p n (L ++ [e]) are prime
    intro v hv
    simp only [allVals, Finset.mem_image] at hv
    obtain ⟨s, hs, rfl⟩ := hv
    simp only [Finset.mem_filter, Finset.mem_powerset] at hs
    by_cases he : e ∈ s
    · -- e ∈ s: write s = t ∪ {e}
      -- Let t = s \ {e}
      let t := s.erase e
      have ht_sub_L : t ⊆ L.toFinset := by
        intro x hx
        rw [Finset.mem_erase] at hx
        obtain ⟨hx_ne_e, hx_in_s⟩ := hx
        have hmem := hs.1 hx_in_s
        simp [List.mem_toFinset, List.toFinset_append] at hmem
        rw [List.mem_toFinset]
        exact hmem.resolve_left hx_ne_e
      have ht_card : t.card ≤ n := by
        have : t.card = s.card - 1 := by simp [t, he]
        omega
      -- p + ∑ x ∈ s, x = e + (p + ∑ x ∈ t, x)
      have hsum : p + ∑ x ∈ s, x = e + (p + ∑ x ∈ t, x) := by
        simp [t]
        have heq := Finset.sum_erase_add s (fun x => x) he
        linarith
      -- c = p + ∑ x ∈ t, x is in critVals p n L
      let c := p + ∑ x ∈ t, x
      have hc_mem : c ∈ critVals p n L := by
        rw [critVals]
        apply Finset.mem_image.mpr
        refine ⟨t, Finset.mem_filter.mpr ⟨?_, ht_card⟩, rfl⟩
        simp [Finset.mem_powerset]
        exact ht_sub_L
      -- p + ∑ x ∈ s, x = A * m + (B + c)
      have h_eq : p + ∑ x ∈ s, x = A * m + (B + c) := by
        simp [e, c] at hsum ⊢
        linarith
      rw [h_eq]
      exact hm_prime ⟨c, hc_mem⟩
    · -- e ∉ s: s ⊆ L.toFinset, so p + ∑ x ∈ s, x ∈ allVals p n L
      have hs_sub_L : s ⊆ L.toFinset := by
        intro x hx
        have hmem := hs.1 hx
        simp [List.mem_toFinset, List.toFinset_append] at hmem
        have hne : x ≠ e := fun h => he (h ▸ hx)
        rw [List.mem_toFinset]
        exact hmem.resolve_left hne
      have hv_mem : p + ∑ x ∈ s, x ∈ allVals p n L := by
        rw [allVals]
        apply Finset.mem_image.mpr
        refine ⟨s, Finset.mem_filter.mpr ⟨?_, hs.2⟩, rfl⟩
        simp [Finset.mem_powerset]
        exact hs_sub_L
      exact hg.primes _ hv_mem
  · -- disc: discipline at critical primes
    intro q hq u hu hbirthday
    simp only [List.length_append] at hu
    -- Case split on whether u < L.length (old entry) or u = L.length (new entry e)
    by_cases huL : u < L.length
    · -- Old entry: need q ∈ critVals p n L to use hg.disc
      by_cases hqL : q ∈ critVals p n L
      · -- q is an old critical prime
        have hstable := birth_stable p n L e hqL
        rw [hstable.1] at hbirthday
        have huL' : u < (L ++ [e]).length := by simp [List.length_append]; omega
        have helem : (L ++ [e]).get ⟨u, huL'⟩ = L.get ⟨u, huL⟩ := by
          simp [List.getElem_append_left huL]
        rw [helem, hstable.2.2]
        exact hg.disc q hqL u huL hbirthday
      · -- q is a newborn: birth q in L ++ [e] equals L.length + 1
        -- birth of q is L.length + 1, but u < L.length, contradicting hbirthday
        have hbirthday_bound : birth p n (L ++ [e]) q = L.length + 1 := by
          unfold birth
          apply Nat.le_antisymm
          · -- sInf ≤ L.length + 1
            apply Nat.sInf_le
            simp only [Set.mem_setOf_eq]
            have htake : (L ++ [e]).take (L.length + 1) = L ++ [e] := by simp
            rw [htake]
            exact hq
          · -- sInf ≥ L.length + 1
            have hhall : ∀ t, t ∈ {t | q ∈ critVals p n ((L ++ [e]).take t)} → L.length + 1 ≤ t := by
              intro t ht
              simp only [Set.mem_setOf_eq] at ht
              by_cases htL : t ≤ L.length
              · -- t ≤ L.length: (L ++ [e]).take t = L.take t, and q ∉ critVals p n L
                have htake : (L ++ [e]).take t = L.take t := List.take_append_of_le_length htL
                rw [htake] at ht
                have hsub : critVals p n (L.take t) ⊆ critVals p n L := by
                  have := critVals_take_mono p n L htL
                  simp [List.take_length] at this
                  exact this
                exfalso
                exact hqL (hsub ht)
              · -- t > L.length, so t ≥ L.length + 1
                omega
            have hmem : L.length + 1 ∈ {t | q ∈ critVals p n ((L ++ [e]).take t)} := by
              simp only [Set.mem_setOf_eq]
              have htake : (L ++ [e]).take (L.length + 1) = L ++ [e] := by simp
              rw [htake]
              exact hq
            exact le_csInf ⟨L.length + 1, hmem⟩ hhall
        omega
    · -- New entry at position u = L.length
      -- u = L.length since u < L.length + 1 and ¬u < L.length
      have hu_eq : u = L.length := by
        have : u < L.length + 1 := by simpa using hu
        omega
      -- Case split on whether q is old critical or newborn
      by_cases hqL : q ∈ critVals p n L
      · -- q is old critical: use birth_stable
        have hstable := birth_stable p n L e hqL
        have hu' : u < (L ++ [e]).length := by convert hu using 1; simp
        have hget : (L ++ [e]).get ⟨u, hu'⟩ = e := by simp [hu_eq]
        rw [hget, hstable.2.2]
        -- q is prime since q ∈ critVals p n L ⊆ allVals p n L
        have hq_prime : q.Prime := by
          have hall : q ∈ allVals p n L := by
            have hsub : critVals p n L ⊆ allVals p n L := by
              unfold critVals allVals
              intro x hx
              simp only [Finset.mem_image] at hx ⊢
              obtain ⟨s, hs, rfl⟩ := hx
              refine ⟨s, Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hs).1, ?_⟩, rfl⟩
              exact Nat.le_succ_of_le (Finset.mem_filter.mp hs).2
            exact hsub hqL
          exact hg.primes q hall
        -- q is tracked (since it's in critVals p n L and prime)
        have hq_tracked : q ∈ tracked p n L := by
          unfold tracked
          exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hqL, hq_prime⟩)
        have hq_dvd_A : q ∣ A := (hAfac q hq_prime).mpr hq_tracked
        -- Therefore e = A * m + B ≡ B ≡ res q (mod q)
        have hB_res := hBcrit q hq_tracked hqL
        have : A * m + B ≡ B [MOD q] := by
          have h1 : A * m ≡ 0 [MOD q] := Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_left hq_dvd_A m)
          simpa using h1.add_right B
        rw [Nat.ModEq] at this
        simp only [e]
        exact this.trans hB_res
      · -- q is newborn critical: birth = L.length + 1 > u, contradiction
        have hbirthday_eq : birth p n (L ++ [e]) q = L.length + 1 := by
          unfold birth
          apply Nat.le_antisymm
          · apply Nat.sInf_le
            simp only [Set.mem_setOf_eq]
            have htake : (L ++ [e]).take (L.length + 1) = L ++ [e] := by simp
            rw [htake]
            exact hq
          · have hhall : ∀ t, t ∈ {t | q ∈ critVals p n ((L ++ [e]).take t)} → L.length + 1 ≤ t := by
              intro t ht
              simp only [Set.mem_setOf_eq] at ht
              by_cases htL : t ≤ L.length
              · have htake : (L ++ [e]).take t = L.take t := List.take_append_of_le_length htL
                rw [htake] at ht
                have hsub : critVals p n (L.take t) ⊆ critVals p n L := by
                  have := critVals_take_mono p n L htL
                  simp [List.take_length] at this
                  exact this
                exfalso
                exact hqL (hsub ht)
              · omega
            have hmem : L.length + 1 ∈ {t | q ∈ critVals p n ((L ++ [e]).take t)} := by
              simp only [Set.mem_setOf_eq]
              have htake : (L ++ [e]).take (L.length + 1) = L ++ [e] := by simp
              rw [htake]
              exact hq
            exact le_csInf ⟨L.length + 1, hmem⟩ hhall
        omega
  · -- frozen: discipline at urgent primes
    intro u hu q hurg
    by_cases huL : u < L.length
    · -- u < L.length: take u (L ++ [e]) = take u L
      have htake : (L ++ [e]).take u = L.take u := List.take_append_of_le_length huL.le
      rw [htake] at hurg
      have hu' : u < (L ++ [e]).length := hu
      have hget : (L ++ [e]).get ⟨u, hu'⟩ = L.get ⟨u, huL⟩ := by simp [List.getElem_append_left huL]
      rw [hget]
      exact hg.frozen u huL q hurg
    · -- u = L.length: q is urgent at L, so q ∣ B and q ∣ A, hence q ∣ e
      have hu_eq : u = L.length := by simp [List.length_append] at hu; omega
      have htake : (L ++ [e]).take u = L := by simp [hu_eq]
      rw [htake] at hurg
      have hu' : u < (L ++ [e]).length := hu
      have hget : (L ++ [e]).get ⟨u, hu'⟩ = e := by simp [hu_eq]
      rw [hget]
      -- q is urgent at L, so q is tracked and q ∉ critVals p n L
      unfold Urgent at hurg
      have hq_prime := hurg.1
      have hq_not_crit := hurg.2.1
      have hq_tracked : q ∈ tracked p n L := by
        unfold tracked
        refine Finset.mem_union_right _ ?_
        refine Finset.mem_filter.mpr ⟨?_, hq_prime, hq_not_crit⟩
        simp only [Finset.mem_range]
        have : (critVals p n L).card ≥ 1 := by
          apply Finset.card_pos.mpr
          exact ⟨p, p_mem_critVals p n L⟩
        omega
      have hq_dvd_A : q ∣ A := (hAfac q hq_prime).mpr hq_tracked
      have hq_dvd_B : q ∣ B := hBurg q hq_tracked hq_not_crit
      exact Nat.dvd_add (dvd_mul_of_dvd_left hq_dvd_A m) hq_dvd_B
  · -- big: size condition
    intro u hu v hv
    by_cases huL : u < L.length
    · -- u < L.length: take u (L ++ [e]) = take u L
      have htake : (L ++ [e]).take u = L.take u := List.take_append_of_le_length huL.le
      rw [htake] at hv
      have hget : (L ++ [e]).get ⟨u, hu⟩ = L.get ⟨u, huL⟩ := by
        simp [List.getElem_append_left huL]
      rw [hget]
      exact hg.big u huL v hv
    · -- u = L.length: need v < e for v ∈ allVals p n L
      have hu_eq : u = L.length := by simp [List.length_append] at hu; omega
      have htake : (L ++ [e]).take u = L := by simp [hu_eq]
      rw [htake] at hv
      have hv_le_max : v ≤ (allVals p n L).max' hall_nonempty := Finset.le_max' _ _ hv
      have hget : (L ++ [e]).get ⟨u, hu⟩ = e := by simp [hu_eq]
      rw [hget]
      have h1 : (allVals p n L).max' hall_nonempty + 1 < A * m + B := lt_of_le_of_lt (le_max_left _ _) hm_large
      simp [e]
      linarith
  · -- room: room condition
    intro u hu
    by_cases huL : u < L.length
    · -- u < L.length: take u (L ++ [e]) = take u L
      have htake : (L ++ [e]).take u = L.take u := List.take_append_of_le_length huL.le
      rw [htake]
      have hget : (L ++ [e]).get ⟨u, hu⟩ = L.get ⟨u, huL⟩ := by simp [List.getElem_append_left huL]
      rw [hget]
      exact hg.room u huL
    · -- u = L.length
      have hu_eq : u = L.length := by simp [List.length_append] at hu; omega
      simp [hu_eq]
      have hle : (n + 1) * ((critVals p n L).card + (critVals p n L).card) + 1 ≤ bound := by
        simp [bound]; ring_nf; omega
      have : (n + 1) * ((critVals p n L).card + (critVals p n L).card) + 1 < A * m + B := lt_of_le_of_lt hle hm_large
      exact Nat.lt_of_succ_le this.le


/-- Iterate the step (choice along a recursion): a monotone family of
good lists, `history t` of length `t`, each extending the last. -/
noncomputable def history (hp : p.Prime) (hn : 1 ≤ n) (hnp : n + 2 ≤ p)
    (hDickson : DicksonConjecture) : ℕ → {L : List ℕ // Good p n L}
  | 0 => ⟨[], good_nil p n hp⟩
  | t + 1 =>
    let prev := history hp hn hnp hDickson t
    ⟨prev.1 ++ [Classical.choose (step p n hp hn hnp hDickson prev.1 prev.2)],
     Classical.choose_spec (step p n hp hn hnp hDickson prev.1 prev.2)⟩

/-- The target.  Set `e j := ` the entry appended at step `j`
(equivalently `(history (j+1)).1.get ⟨j, …⟩`; lengths are `t` by
induction).  Injectivity: entries strictly increase along the whole
construction (`mono` + `big` across steps).  Evenness: `2` is urgent
at every prefix (see `Urgent` docstring), so `frozen` gives
`2 ∣ e j`.  Primality of anchored ≤(n+1)-sums: a finset `s` of
indices with `s.card ≤ n + 1` is contained in `range m` for some `m`;
the corresponding values form a ≤(n+1)-subset of
`(history m).1.toFinset` (distinct by injectivity, sum over indices =
sum over values), so `p + ∑` lies in `allVals` of a good list. -/
theorem bounded_prime_finite_sums_sequence_exists'
    (hDickson : DicksonConjecture)
    (hp : p.Prime) (hn : 1 ≤ n) (hnp : n + 2 ≤ p) :
    ∃ e : ℕ → ℕ, Function.Injective e ∧
      (∀ j, Even (e j)) ∧
      ∀ s : Finset ℕ, s.card ≤ n + 1 →
        (p + ∑ j ∈ s, e j).Prime := by
  -- Define e j as the entry appended at step j
  let hist_len : ∀ t, (history p n hp hn hnp hDickson t).1.length = t := by
    intro t
    induction t <;> simp [history, *]
  let e : ℕ → ℕ := fun j => (history p n hp hn hnp hDickson (j + 1)).1.get ⟨j, by simp [hist_len]⟩
  -- Helper: history lists are prefixes of later ones
  have hist_prefix : ∀ t₁ t₂, t₁ ≤ t₂ → (history p n hp hn hnp hDickson t₁).1 = (history p n hp hn hnp hDickson t₂).1.take t₁ := by
    intro t₁ t₂ ht
    induction t₂ generalizing t₁ with
    | zero => cases ht; rfl
    | succ t₂ ih =>
      cases ht.eq_or_lt with
      | inl h => subst h; simp [hist_len]
      | inr h =>
        have ht₁ : t₁ ≤ t₂ := Nat.lt_succ_iff.mp h
        simp only [history]
        rw [List.take_append_of_le_length (by simp [hist_len, ht₁] : t₁ ≤ (history p n hp hn hnp hDickson t₂).1.length)]
        exact ih t₁ ht₁
  -- Helper: 2 is always urgent (since p ≥ 3, critVals contains no 2, and card ≥ 1)
  have two_urgent : ∀ t, Urgent p n ((history p n hp hn hnp hDickson t).1.take t) 2 := by
    intro t
    have htaketaket : (history p n hp hn hnp hDickson t).1.take t = (history p n hp hn hnp hDickson t).1 := by
      have := hist_len t
      simp [this]
    rw [htaketaket]
    refine ⟨Nat.prime_two, ?_, ?_⟩
    · -- 2 ∉ critVals p n L
      intro hx
      simp [critVals] at hx
      obtain ⟨s, _, hsum⟩ := hx
      -- p + sum = 2, but p ≥ 3, contradiction
      have hp3 : 3 ≤ p := by omega
      omega
    · -- 2 ≤ card + 1, i.e., card ≥ 1
      have hp_mem : p ∈ critVals p n (history p n hp hn hnp hDickson t).1 := p_mem_critVals p n _
      have hcard := Finset.card_pos.mpr ⟨p, hp_mem⟩
      linarith
  refine ⟨e, ?inj, ?even, ?prim⟩
  · -- Injectivity: entries are strictly increasing (Good.mono)
    intro i j hij
    -- Raise both to history (max i j + 1) using hist_prefix
    let m := max i j
    have hi_le_m : i ≤ m := le_max_left i j
    have hj_le_m : j ≤ m := le_max_right i j
    have hi_lt : i < (history p n hp hn hnp hDickson (m + 1)).1.length := by simp [hist_len]; omega
    have hj_lt : j < (history p n hp hn hnp hDickson (m + 1)).1.length := by simp [hist_len]; omega
    have h_ilen : (history p n hp hn hnp hDickson (i + 1)).1.length = i + 1 := hist_len _
    have h_mlen : (history p n hp hn hnp hDickson (m + 1)).1.length = m + 1 := hist_len _
    -- Key: (history (i+1)).1 is a prefix of (history (m+1)).1
    have hprefix : (history p n hp hn hnp hDickson (i + 1)).1 = (history p n hp hn hnp hDickson (m + 1)).1.take (i + 1) :=
      hist_prefix _ _ (by omega)
    have hi' : e i = (history p n hp hn hnp hDickson (m + 1)).1.get ⟨i, hi_lt⟩ := by
      simp only [e]
      simp [hprefix]
    have hprefix' : (history p n hp hn hnp hDickson (j + 1)).1 = (history p n hp hn hnp hDickson (m + 1)).1.take (j + 1) :=
      hist_prefix _ _ (by omega)
    have hj' : e j = (history p n hp hn hnp hDickson (m + 1)).1.get ⟨j, hj_lt⟩ := by
      simp only [e]
      simp [hprefix']
    rw [hi', hj'] at hij
    -- Use Good.mono: strictly increasing implies different indices give different values
    have hmono := (history p n hp hn hnp hDickson (m + 1)).2.mono
    -- Get is injective on a List.Nodup list
    have hnodup : List.Nodup (history p n hp hn hnp hDickson (m + 1)).1 := by
      rw [List.nodup_iff_pairwise_ne]
      apply List.Pairwise.imp (@fun (a b : ℕ) => ne_of_lt) hmono.pairwise
    have := hnodup.injective_get
    have heq := this hij
    simp at heq
    exact heq
  · -- Evenness: 2 is urgent at every prefix, so frozen gives 2 ∣ e j
    intro j
    have hlen : (history p n hp hn hnp hDickson (j + 1)).1.length = j + 1 := hist_len _
    have hj_lt : j < (history p n hp hn hnp hDickson (j + 1)).1.length := by omega
    have hprefix_j : (history p n hp hn hnp hDickson j).1 = (history p n hp hn hnp hDickson (j + 1)).1.take j :=
      hist_prefix _ _ (by omega)
    have hurg := two_urgent j
    rw [hprefix_j, List.take_take] at hurg
    simp at hurg
    have hgood := (history p n hp hn hnp hDickson (j + 1)).2
    have hdiv := hgood.frozen j hj_lt 2 hurg
    exact even_iff_two_dvd.mpr hdiv
  · -- Primality: sums are in allVals of a good list
    intro s hs_card
    -- Find m large enough that all indices in s are < m
    let m := s.sup id + 1
    -- All e j for j ∈ s are in (history m).1
    -- So p + ∑ is in allVals (history m).1
    have hs_le : ∀ j ∈ s, j < m := fun j hj => by
      simp only [m]
      exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hj)
    -- The values e j for j ∈ s are in (history m).1 (by hist_prefix)
    have he_in_hist : ∀ j ∈ s, e j ∈ (history p n hp hn hnp hDickson m).1 := by
      intro j hj
      have hj_lt_m : j < (history p n hp hn hnp hDickson m).1.length := by simp [hist_len]; exact hs_le j hj
      have hj1_lt_m : j + 1 ≤ m := Nat.succ_le_of_lt (hs_le j hj)
      have hprefix' : e j = (history p n hp hn hnp hDickson m).1.get ⟨j, hj_lt_m⟩ := by
        have hpre := hist_prefix (j + 1) m hj1_lt_m
        simp only [e]
        simp [hpre]
      rw [hprefix']
      exact List.mem_iff_get.mpr ⟨⟨j, hj_lt_m⟩, rfl⟩
    -- Injectivity of e (needed for cardinality and sum)
    have e_inj : Function.Injective e := by
      intro i j hij
      let m := max i j
      have hi_lt : i < (history p n hp hn hnp hDickson (m + 1)).1.length := by simp [hist_len]; omega
      have hj_lt : j < (history p n hp hn hnp hDickson (m + 1)).1.length := by simp [hist_len]; omega
      have hprefix : (history p n hp hn hnp hDickson (i + 1)).1 = (history p n hp hn hnp hDickson (m + 1)).1.take (i + 1) :=
        hist_prefix _ _ (by omega)
      have hi' : e i = (history p n hp hn hnp hDickson (m + 1)).1.get ⟨i, hi_lt⟩ := by
        simp only [e]
        simp [hprefix]
      have hprefix' : (history p n hp hn hnp hDickson (j + 1)).1 = (history p n hp hn hnp hDickson (m + 1)).1.take (j + 1) :=
        hist_prefix _ _ (by omega)
      have hj' : e j = (history p n hp hn hnp hDickson (m + 1)).1.get ⟨j, hj_lt⟩ := by
        simp only [e]
        simp [hprefix']
      rw [hi', hj'] at hij
      have hmono := (history p n hp hn hnp hDickson (m + 1)).2.mono
      have hnodup : List.Nodup (history p n hp hn hnp hDickson (m + 1)).1 := by
        rw [List.nodup_iff_pairwise_ne]
        apply List.Pairwise.imp (@fun (a b : ℕ) => ne_of_lt) hmono.pairwise
      have := hnodup.injective_get
      have heq := this hij
      simp at heq
      exact heq
    -- The sum p + ∑ j ∈ s, e j is in allVals (history m).1
    have hsum_in_allVals : p + ∑ j ∈ s, e j ∈ allVals p n (history p n hp hn hnp hDickson m).1 := by
      unfold allVals
      rw [Finset.mem_image]
      use s.image e
      constructor
      · rw [Finset.mem_filter, Finset.mem_powerset]
        constructor
        · intro x hx
          rw [List.mem_toFinset]
          obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
          exact he_in_hist j hj
        · exact le_trans (Finset.card_image_le) hs_card
      · simp [Finset.sum_image (fun a _ b _ hab => e_inj hab)]
    -- By Good.primes, all values in allVals are prime
    have hgood := (history p n hp hn hnp hDickson m).2
    exact hgood.primes _ hsum_in_allVals


end Construction
end DicksonSumsets

/-!
## Wiring

Once `bounded_prime_finite_sums_sequence_exists'` is proved, the sorry
in `MainTheorem.lean` becomes
`exact Construction.bounded_prime_finite_sums_sequence_exists' p n hDickson hp hn hnp`
(argument order per the final elaborated signature).
-/
