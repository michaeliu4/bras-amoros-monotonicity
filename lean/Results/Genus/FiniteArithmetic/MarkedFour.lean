import Results.Genus.FiniteArithmetic.CapacitySeries

/-!
# Original N and K capacity sources

`NWords n` consists of actual {2,3,4} words of weight n containing at least
two fours. An exact first-letter state decomposition proves the original
rational generating identity. Neither rational coefficients nor an external
table define this source language.
-/

namespace SubmittedGenus.FiniteArithmetic

open scoped BigOperators
open PowerSeries

abbrev alphabet234 : WeightedAlphabet where
  size := 3
  weight a := a.val + 2
  positive a := by omega

abbrev FourWords (n k : ℕ) :=
  {w : List (Fin 3) // (w.map alphabet234.weight).sum = n ∧ k ≤ w.count 2}

noncomputable instance fourWordsFintype (n k : ℕ) : Fintype (FourWords n k) :=
  ((List.finite_length_le (Fin 3) n).subset (by
    intro w hw
    exact (length_le_weight alphabet234 w).trans (le_of_eq hw.1))).fintype

def fourIndicator (a : Fin 3) : ℕ := if a = 2 then 1 else 0

theorem count_four_cons (a : Fin 3) (w : List (Fin 3)) :
    (a :: w).count 2 = w.count 2 + fourIndicator a := by
  simp [List.count_cons, fourIndicator]

def fourWordsConsEquiv (n k : ℕ) (hn : 0 < n) :
    FourWords n k ≃ Σ a : {a : Fin 3 // alphabet234.weight a ≤ n},
      FourWords (n - alphabet234.weight a.val) (k - fourIndicator a.val) where
  toFun w := by
    rcases w with ⟨w, hw, hk⟩
    cases w with
    | nil => simp at hw; omega
    | cons a t =>
      simp only [List.map_cons, List.sum_cons] at hw
      rw [count_four_cons] at hk
      change a.val + 2 + (t.map (fun a => a.val + 2)).sum = n at hw
      refine ⟨⟨a, by change a.val + 2 ≤ n; omega⟩, ⟨t, ?_, ?_⟩⟩
      · change (t.map (fun a => a.val + 2)).sum = n - (a.val + 2)
        omega
      · change k - fourIndicator a ≤ t.count 2
        omega
  invFun w := ⟨w.1.val :: w.2.val, by
    simp only [List.map_cons, List.sum_cons, w.2.property.1]
    exact Nat.add_sub_of_le w.1.property, by
    rw [count_four_cons]
    have := w.2.property.2
    omega⟩
  left_inv w := by
    rcases w with ⟨w, hw, hk⟩
    cases w with
    | nil => simp at hw; omega
    | cons a t => rfl
  right_inv w := by
    rcases w with ⟨⟨a, ha⟩, ⟨t, ht, hk⟩⟩
    rfl

instance fourWordsZeroIsEmpty (k : ℕ) : IsEmpty (FourWords 0 (k + 1)) where
  false w := by
    have h := length_le_weight alphabet234 w.val
    rw [w.property.1] at h
    have he : w.val = [] := List.length_eq_zero_iff.mp (by omega)
    have hk := w.property.2
    rw [he] at hk
    simp at hk

noncomputable def fourCount (n k : ℕ) : ℕ := Fintype.card (FourWords n k)

@[simp] theorem fourCount_zero (k : ℕ) : fourCount 0 (k + 1) = 0 := by
  exact Fintype.card_eq_zero

theorem fourCount_first_letter (n k : ℕ) (hn : 0 < n) :
    fourCount n k = ∑ a : {a : Fin 3 // alphabet234.weight a ≤ n},
      fourCount (n - alphabet234.weight a.val) (k - fourIndicator a.val) := by
  unfold fourCount
  rw [Fintype.card_congr (fourWordsConsEquiv n k hn), Fintype.card_sigma]

/-- The exact source recurrence has one branch for each possible first letter. -/
theorem fourCount_state_recurrence (n k : ℕ) :
    fourCount n (k + 1) =
      (if 2 ≤ n then fourCount (n - 2) (k + 1) else 0) +
      (if 3 ≤ n then fourCount (n - 3) (k + 1) else 0) +
      (if 4 ≤ n then fourCount (n - 4) k else 0) := by
  by_cases hn : n = 0
  · subst n
    simp
  · rw [fourCount_first_letter n (k + 1) (Nat.pos_of_ne_zero hn)]
    rw [← Finset.sum_subtype (Finset.univ.filter (fun a => alphabet234.weight a ≤ n))
      (by simp) (fun a => fourCount (n - alphabet234.weight a) ((k + 1) - fourIndicator a))]
    rw [Finset.sum_filter]
    simp only [Fin.sum_univ_succ]
    simp [fourIndicator, add_assoc]

noncomputable def fourSeries (k : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk (fun n => (fourCount n k : ℤ))

@[simp] theorem coeff_fourSeries (n k : ℕ) :
    coeff n (fourSeries k) = (fourCount n k : ℤ) := by
  simp [fourSeries]

def fourWordsZeroStateEquiv (n : ℕ) : FourWords n 0 ≃ ExactWords alphabet234 n where
  toFun w := ⟨w.val, w.property.1⟩
  invFun w := ⟨w.val, w.property, Nat.zero_le _⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem fourSeries_zero_state : fourSeries 0 = wordSeries alphabet234 := by
  apply PowerSeries.ext
  intro n
  simp only [coeff_fourSeries, coeff_wordSeries]
  congr 1
  letI : Fintype (ExactWords alphabet234 n) := exactWordsFintype alphabet234 n
  exact Fintype.card_congr (fourWordsZeroStateEquiv n)

theorem fourSeries_state_identity (k : ℕ) :
    (1 - (X : PowerSeries ℤ)^2 - X^3) * fourSeries (k + 1) = X^4 * fourSeries k := by
  apply PowerSeries.ext
  intro n
  simp only [sub_mul, one_mul, map_sub, coeff_X_pow_mul', coeff_fourSeries]
  have h := congrArg (fun x : ℕ => (x : ℤ)) (fourCount_state_recurrence n k)
  push_cast at h
  split_ifs at h ⊢ <;> omega

theorem alphabet234_polynomial : alphabetPolynomial alphabet234 =
    (X : PowerSeries ℤ)^2 + X^3 + X^4 := by
  change (∑ a : Fin 3, (X : PowerSeries ℤ) ^ (a.val + 2)) = _
  simp only [Fin.sum_univ_succ]
  norm_num
  ring

theorem fourSeries_zero_identity :
    (1 - (X : PowerSeries ℤ)^2 - X^3 - X^4) * fourSeries 0 = 1 := by
  rw [fourSeries_zero_state]
  have h := wordSeries_identity alphabet234
  rw [alphabet234_polynomial] at h
  simpa [sub_sub] using h

/-- Exactly the original numerator-eight source N. -/
abbrev NWords (n : ℕ) := FourWords n 2
noncomputable def capacityN : PowerSeries ℤ := fourSeries 2

theorem capacityN_source_coeff (n : ℕ) :
    coeff n capacityN = (Fintype.card (NWords n) : ℤ) := by
  simp [capacityN, fourCount]

/-- Original manuscript equation `cmb:N`, proved from actual word semantics. -/
theorem capacityN_source_identity :
    ((1 - (X : PowerSeries ℤ)^2 - X^3)^2 *
      (1 - X^2 - X^3 - X^4)) * capacityN = X^8 := by
  have h1 := fourSeries_state_identity 0
  have h2 := fourSeries_state_identity 1
  change (1 - (X : PowerSeries ℤ)^2 - X^3) * fourSeries 1 = X^4 * fourSeries 0 at h1
  change (1 - (X : PowerSeries ℤ)^2 - X^3) * fourSeries 2 = X^4 * fourSeries 1 at h2
  unfold capacityN
  calc
    _ = (1 - (X : PowerSeries ℤ)^2 - X^3 - X^4) * (1 - X^2 - X^3) *
        ((1 - X^2 - X^3) * fourSeries 2) := by ring
    _ = X^4 * (1 - (X : PowerSeries ℤ)^2 - X^3 - X^4) *
        ((1 - X^2 - X^3) * fourSeries 1) := by rw [h2]; ring
    _ = X^8 * ((1 - (X : PowerSeries ℤ)^2 - X^3 - X^4) * fourSeries 0) := by
      rw [h1]
      ring
    _ = X^8 := by rw [fourSeries_zero_identity, mul_one]

/-- Literal physical-digit encoding, with the original final 1 appended. -/
def encodeFinalOne {n : ℕ} (w : NWords n) : List ℕ :=
  w.val.map (fun a => a.val + 2) ++ [1]

theorem encodeFinalOne_injective (n : ℕ) :
    Function.Injective (encodeFinalOne (n := n)) := by
  intro a b h
  apply Subtype.ext
  have hi : Function.Injective (fun a : Fin 3 => a.val + 2) := by
    intro a b hab
    apply Fin.ext
    dsimp at hab
    omega
  exact List.map_injective_iff.mpr hi (List.append_cancel_right h)

/-- Actual final-one source words, expressed as the injective image of N. -/
abbrev KWords (n : ℕ) :=
  {w : List ℕ // 1 ≤ n ∧ w ∈ Set.range (encodeFinalOne (n := n - 1))}

noncomputable instance kWordsFintype (n : ℕ) : Fintype (KWords n) :=
  ((Set.finite_range (encodeFinalOne (n := n - 1))).subset (by
    intro w hw
    exact hw.2)).fintype

noncomputable def finalOneEquiv (n : ℕ) (hn : 1 ≤ n) : NWords (n - 1) ≃ KWords n :=
  Equiv.ofBijective (fun w => ⟨encodeFinalOne w, hn, ⟨w, rfl⟩⟩) (by
    constructor
    · intro a b h
      exact encodeFinalOne_injective _ (congrArg Subtype.val h)
    · rintro ⟨w, hw, v, hv⟩
      exact ⟨v, Subtype.ext hv⟩)

theorem kWords_weight (n : ℕ) (w : KWords n) : w.val.sum = n := by
  obtain ⟨v, hv⟩ := w.property.2
  rw [← hv]
  simp only [encodeFinalOne, List.sum_append, List.sum_cons, List.sum_nil, add_zero]
  have hs : (v.val.map (fun a => a.val + 2)).sum = n - 1 := v.property.1
  rw [hs]
  have := w.property.1
  omega

noncomputable def capacityK : PowerSeries ℤ := X * capacityN

theorem capacityK_source_coeff (n : ℕ) :
    coeff n capacityK = (Fintype.card (KWords n) : ℤ) := by
  unfold capacityK
  rw [← pow_one (X : PowerSeries ℤ), coeff_X_pow_mul']
  by_cases hn : 1 ≤ n
  · rw [if_pos hn, capacityN_source_coeff]
    exact congrArg (fun x : ℕ => (x : ℤ)) (Fintype.card_congr (finalOneEquiv n hn))
  · rw [if_neg hn]
    haveI : IsEmpty (KWords n) := ⟨fun w => hn w.property.1⟩
    simp

theorem capacityK_source_identity :
    ((1 - (X : PowerSeries ℤ)^2 - X^3)^2 *
      (1 - X^2 - X^3 - X^4)) * capacityK = X^9 := by
  unfold capacityK
  calc
    _ = X * (((1 - (X : PowerSeries ℤ)^2 - X^3)^2 *
      (1 - X^2 - X^3 - X^4)) * capacityN) := by ring
    _ = X^9 := by rw [capacityN_source_identity]; ring

/-- Common exact denominator of original N and K. -/
def nDenominator (n : ℕ) : ℤ :=
  if n = 0 then 1 else if n = 2 ∨ n = 3 ∨ n = 9 then -3 else
    if n = 4 then 2 else if n = 5 then 6 else if n = 6 then 4 else
      if n = 7 ∨ n = 10 then -1 else if n = 8 then -4 else 0

def nNumerator (n : ℕ) : ℤ := if n = 8 then 1 else 0

def kNumerator (n : ℕ) : ℤ := if n = 9 then 1 else 0

theorem nDenominator_coeff (n : ℕ) :
    coeff n (((1 - (X : PowerSeries ℤ)^2 - X^3)^2) *
      (1 - X^2 - X^3 - X^4)) = nDenominator n := by
  have he : (1 - (X : PowerSeries ℤ)^2 - X^3)^2 *
      (1 - X^2 - X^3 - X^4) =
      1 - 3 • X^2 - 3 • X^3 + 2 • X^4 + 6 • X^5 + 4 • X^6 - X^7 -
        4 • X^8 - 3 • X^9 - X^10 := by simp only [nsmul_eq_mul]; ring
  rw [he]
  simp only [map_add, map_sub, map_nsmul, coeff_one, coeff_X_pow]
  by_cases hn : n ≤ 10
  · interval_cases n <;> norm_num [nDenominator]
  · simp [nDenominator, show n ≠ 0 by omega, show n ≠ 2 by omega,
      show n ≠ 3 by omega, show n ≠ 4 by omega, show n ≠ 5 by omega,
      show n ≠ 6 by omega, show n ≠ 7 by omega, show n ≠ 8 by omega,
      show n ≠ 9 by omega, show n ≠ 10 by omega]

theorem capacityN_coefficients (n : ℕ) :
    coeff n capacityN = rationalCoeff nNumerator nDenominator n := by
  have h := source_coefficients_eq_recurrence ((X : PowerSeries ℤ)^8)
    ((1 - X^2 - X^3)^2 * (1 - X^2 - X^3 - X^4)) capacityN
    (by simp) capacityN_source_identity n
  change coeff n capacityN = rationalCoeff (fun i => if i = 8 then 1 else 0) nDenominator n
  simpa only [coeff_X_pow, nDenominator_coeff] using h

theorem capacityK_coefficients (n : ℕ) :
    coeff n capacityK = rationalCoeff kNumerator nDenominator n := by
  have h := source_coefficients_eq_recurrence ((X : PowerSeries ℤ)^9)
    ((1 - X^2 - X^3)^2 * (1 - X^2 - X^3 - X^4)) capacityK
    (by simp) capacityK_source_identity n
  change coeff n capacityK = rationalCoeff (fun i => if i = 9 then 1 else 0) nDenominator n
  simpa only [coeff_X_pow, nDenominator_coeff] using h

def nFirst31 : List ℤ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 3, 3, 7, 12, 20, 34,
   56, 90, 146, 230, 364, 568, 883, 1364, 2097, 3209, 4893,
   7432, 11256, 16996, 25600]

theorem nFirst31_valid : ValidPrefix nNumerator nDenominator nFirst31 := by
  decide

theorem nFirst31_source_correct (n : ℕ) (hn : n < 31) :
    nFirst31.getD n 0 = (Fintype.card (NWords n) : ℤ) := by
  rw [← capacityN_source_coeff, capacityN_coefficients]
  exact validPrefix_sound _ _ _ nFirst31_valid n hn

#print axioms fourCount_state_recurrence
#print axioms capacityN_source_coeff
#print axioms capacityN_source_identity
#print axioms capacityK_source_coeff
#print axioms capacityK_source_identity
#print axioms nFirst31_source_correct

end SubmittedGenus.FiniteArithmetic
