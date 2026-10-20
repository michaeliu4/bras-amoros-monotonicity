import Results.Genus.FiniteArithmetic

/-!
# Counted capacity-series source semantics

The source coefficients below count actual finite lists over a positive-weight
finite alphabet. They are not defined by the rational recurrence. The generic
head/tail equivalence is used to prove the generating-function identity first.
The original manuscript's C₀ counts words on {2,3}; it is the subtraction source
in the isolated-five capacity term J (submitted manuscript lines 391--397).
-/

namespace SubmittedGenus.FiniteArithmetic

open scoped BigOperators
open PowerSeries

structure WeightedAlphabet where
  size : ℕ
  weight : Fin size → ℕ
  positive : ∀ a, 0 < weight a

abbrev ExactWords (A : WeightedAlphabet) (n : ℕ) :=
  {w : List (Fin A.size) // (w.map A.weight).sum = n}

theorem length_le_weight (A : WeightedAlphabet) (w : List (Fin A.size)) :
    w.length ≤ (w.map A.weight).sum := by
  induction w with
  | nil => simp
  | cons a w ih =>
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    have := A.positive a
    omega

noncomputable instance exactWordsFintype (A : WeightedAlphabet) (n : ℕ) :
    Fintype (ExactWords A n) :=
  ((List.finite_length_le (Fin A.size) n).subset (by
    intro w hw
    exact (length_le_weight A w).trans (le_of_eq hw))).fintype

instance exactWordsZeroUnique (A : WeightedAlphabet) : Unique (ExactWords A 0) where
  default := ⟨[], by simp⟩
  uniq w := by
    apply Subtype.ext
    have h := length_le_weight A w.val
    rw [w.property] at h
    exact List.length_eq_zero_iff.mp (by omega)

/-- Exact first-letter decomposition of a nonempty positive-weight word. -/
def exactWordsConsEquiv (A : WeightedAlphabet) (n : ℕ) (hn : 0 < n) :
    ExactWords A n ≃ Σ a : {a : Fin A.size // A.weight a ≤ n},
      ExactWords A (n - A.weight a.val) where
  toFun w := by
    rcases w with ⟨w, hw⟩
    cases w with
    | nil => simp at hw; omega
    | cons a t =>
      simp only [List.map_cons, List.sum_cons] at hw
      refine ⟨⟨a, by omega⟩, ⟨t, ?_⟩⟩
      change (t.map A.weight).sum = n - A.weight a
      omega
  invFun w := ⟨w.1.val :: w.2.val, by
    simp only [List.map_cons, List.sum_cons, w.2.property]
    exact Nat.add_sub_of_le w.1.property⟩
  left_inv w := by
    rcases w with ⟨w, hw⟩
    cases w with
    | nil => simp at hw; omega
    | cons a t => rfl
  right_inv w := by
    rcases w with ⟨⟨a, ha⟩, ⟨t, ht⟩⟩
    rfl

noncomputable def wordCount (A : WeightedAlphabet) (n : ℕ) : ℕ :=
  Fintype.card (ExactWords A n)

@[simp] theorem wordCount_zero (A : WeightedAlphabet) : wordCount A 0 = 1 := by
  exact Fintype.card_unique

theorem wordCount_succ (A : WeightedAlphabet) (n : ℕ) (hn : 0 < n) :
    wordCount A n =
      ∑ a : {a : Fin A.size // A.weight a ≤ n}, wordCount A (n - A.weight a.val) := by
  unfold wordCount
  rw [Fintype.card_congr (exactWordsConsEquiv A n hn), Fintype.card_sigma]

/-- Semantic formal series: its coefficient is a cardinality of word lists. -/
noncomputable def wordSeries (A : WeightedAlphabet) : PowerSeries ℤ :=
  PowerSeries.mk (fun n => (wordCount A n : ℤ))

noncomputable def alphabetPolynomial (A : WeightedAlphabet) : PowerSeries ℤ :=
  ∑ a : Fin A.size, X ^ A.weight a

@[simp] theorem coeff_wordSeries (A : WeightedAlphabet) (n : ℕ) :
    coeff n (wordSeries A) = (wordCount A n : ℤ) := by
  simp [wordSeries]

/-- The actual-word generating function obeys the geometric-series equation. -/
theorem wordSeries_identity (A : WeightedAlphabet) :
    (1 - alphabetPolynomial A) * wordSeries A = 1 := by
  apply PowerSeries.ext
  intro n
  rw [sub_mul, one_mul, map_sub]
  rw [alphabetPolynomial, Finset.sum_mul, map_sum]
  simp only [coeff_wordSeries, coeff_X_pow_mul', coeff_one]
  by_cases hn : n = 0
  · subst n
    simp only [wordCount_zero, Nat.cast_one, ite_true]
    have hs : (∑ a : Fin A.size, if A.weight a ≤ 0 then
        (wordCount A (0 - A.weight a) : ℤ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro a ha
      have := A.positive a
      simp [show ¬ A.weight a ≤ 0 by omega]
    rw [hs]
    simp
  · rw [if_neg hn]
    have hs := wordCount_succ A n (Nat.pos_of_ne_zero hn)
    have hz : (wordCount A n : ℤ) =
        ∑ a : Fin A.size, if A.weight a ≤ n then
          (wordCount A (n - A.weight a) : ℤ) else 0 := by
      rw [hs, Nat.cast_sum]
      rw [← Finset.sum_filter]
      exact (Finset.sum_subtype (Finset.univ.filter (fun a => A.weight a ≤ n))
        (by simp) (fun a => (wordCount A (n - A.weight a) : ℤ))).symm
    rw [hz, sub_self]

/-- The alphabet {2,3}; letters are encoded by 0↦2 and 1↦3. -/
def alphabet23 : WeightedAlphabet where
  size := 2
  weight a := a.val + 2
  positive a := by omega

/-- Original submitted auxiliary capacity source C₀. -/
noncomputable def capacityC0 : PowerSeries ℤ := wordSeries alphabet23

theorem alphabet23_polynomial : alphabetPolynomial alphabet23 =
    (X : PowerSeries ℤ) ^ 2 + X ^ 3 := by
  change (∑ a : Fin 2, (X : PowerSeries ℤ) ^ (a.val + 2)) = _
  rw [Fin.sum_univ_two]
  norm_num

/-- Counted-source identity, before any finite coefficient acceptance. -/
theorem capacityC0_source_identity :
    (1 - (X : PowerSeries ℤ)^2 - X^3) * capacityC0 = 1 := by
  have h := wordSeries_identity alphabet23
  rw [alphabet23_polynomial] at h
  simpa [capacityC0, sub_sub] using h

/-- The manuscript denominator in executable integer coefficient form. -/
def c0Denominator (n : ℕ) : ℤ :=
  if n = 0 then 1 else if n = 2 ∨ n = 3 then -1 else 0

def c0Numerator (n : ℕ) : ℤ := if n = 0 then 1 else 0

theorem c0Denominator_coeff (n : ℕ) :
    coeff n (1 - (X : PowerSeries ℤ)^2 - X^3) = c0Denominator n := by
  simp only [map_sub, coeff_one, coeff_X_pow, c0Denominator]
  split_ifs <;> omega

theorem capacityC0_coefficients (n : ℕ) :
    coeff n capacityC0 = rationalCoeff c0Numerator c0Denominator n := by
  have h := source_coefficients_eq_recurrence 1
    (1 - (X : PowerSeries ℤ)^2 - X^3) capacityC0
    (by simp) capacityC0_source_identity n
  change coeff n capacityC0 = rationalCoeff (fun i => if i = 0 then 1 else 0) c0Denominator n
  simpa only [coeff_one, c0Denominator_coeff] using h

/-- Small acceptance is an actual kernel-checked recurrence certificate. -/
def c0First21 : List ℤ :=
  [1, 0, 1, 1, 1, 2, 2, 3, 4, 5, 7, 9, 12, 16, 21, 28, 37, 49, 65, 86, 114]

theorem c0First21_valid : ValidPrefix c0Numerator c0Denominator c0First21 := by
  decide

/-- The checked data are cardinalities of the original {2,3}-word source. -/
theorem c0First21_source_correct (n : ℕ) (hn : n < 21) :
    c0First21.getD n 0 = (wordCount alphabet23 n : ℤ) := by
  rw [← coeff_wordSeries, ← capacityC0, capacityC0_coefficients]
  exact validPrefix_sound _ _ _ c0First21_valid n hn


/-- The no-1 alphabet {2,3,4,5}, used in the original H majorant. -/
def alphabet2345 : WeightedAlphabet where
  size := 4
  weight a := a.val + 2
  positive a := by omega

def smallLetterIntoBig (a : Fin 2) : Fin 4 := ⟨a.val, by omega⟩

theorem smallLetterIntoBig_injective : Function.Injective smallLetterIntoBig := by
  intro a b h
  apply Fin.ext
  exact congrArg (fun x : Fin 4 => x.val) h

/-- Literal alphabet inclusion, preserving the actual list and its weight. -/
def smallWordIntoBig (n : ℕ) (w : ExactWords alphabet23 n) :
    ExactWords alphabet2345 n :=
  ⟨w.val.map smallLetterIntoBig, by simpa [List.map_map, alphabet23,
    alphabet2345, smallLetterIntoBig, Function.comp_def] using w.property⟩

theorem smallWordIntoBig_injective (n : ℕ) :
    Function.Injective (smallWordIntoBig n) := by
  intro a b h
  apply Subtype.ext
  exact List.map_injective_iff.mpr smallLetterIntoBig_injective (congrArg Subtype.val h)

/-- Decode a word known to use only the two small letters. -/
def shrinkSmall : (w : List (Fin 4)) → (∀ a ∈ w, a.val < 2) → List (Fin 2)
  | [], _ => []
  | a :: w, h => ⟨a.val, h a (by simp)⟩ ::
      shrinkSmall w (fun b hb => h b (by simp [hb]))

theorem small_map_shrink (w : List (Fin 4)) (h : ∀ a ∈ w, a.val < 2) :
    (shrinkSmall w h).map smallLetterIntoBig = w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    simp only [shrinkSmall, List.map_cons]
    congr 1
    exact ih _

theorem smallWordIntoBig_range_iff (n : ℕ) (w : ExactWords alphabet2345 n) :
    w ∈ Set.range (smallWordIntoBig n) ↔ ∀ a ∈ w.val, a.val < 2 := by
  constructor
  · rintro ⟨v, rfl⟩ a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact b.isLt
  · intro h
    have hw : ((shrinkSmall w.val h).map alphabet23.weight).sum = n := by
      have he := congrArg (fun l : List (Fin 4) => (l.map alphabet2345.weight).sum)
        (small_map_shrink w.val h)
      rw [w.property] at he
      simpa [List.map_map, alphabet23, alphabet2345, smallLetterIntoBig,
        Function.comp_def] using he
    refine ⟨⟨shrinkSmall w.val h, hw⟩, ?_⟩
    apply Subtype.ext
    exact small_map_shrink w.val h

/-- Absence from the small alphabet is exactly the presence of a 4 or a 5. -/
theorem not_smallWordIntoBig_iff (n : ℕ) (w : ExactWords alphabet2345 n) :
    ¬ w ∈ Set.range (smallWordIntoBig n) ↔
      ∃ a ∈ w.val, alphabet2345.weight a = 4 ∨ alphabet2345.weight a = 5 := by
  rw [smallWordIntoBig_range_iff]
  push Not
  constructor
  · rintro ⟨a, ha, hlarge⟩
    refine ⟨a, ha, ?_⟩
    have ha4 : a.val < 4 := a.isLt
    simp only [alphabet2345]
    omega
  · rintro ⟨a, ha, hlarge⟩
    refine ⟨a, ha, ?_⟩
    simp only [alphabet2345] at hlarge
    omega

/-- Actual words counted by H: words on {2,3,4,5} outside the embedded {2,3}
word language. In other words these words contain a 4 or a 5. -/
abbrev HWords (n : ℕ) :=
  {w : ExactWords alphabet2345 n // ¬ w ∈ Set.range (smallWordIntoBig n)}

noncomputable instance hWordsFintype (n : ℕ) : Fintype (HWords n) :=
  Fintype.ofFinite _

noncomputable def capacityH : PowerSeries ℤ :=
  wordSeries alphabet2345 - wordSeries alphabet23

/-- The signed algebraic difference is exactly a nonnegative source cardinality. -/
theorem capacityH_source_coeff (n : ℕ) :
    coeff n capacityH = (Fintype.card (HWords n) : ℤ) := by
  classical
  have hi := Fintype.card_le_of_injective (smallWordIntoBig n)
    (smallWordIntoBig_injective n)
  have hc : Fintype.card (Set.range (smallWordIntoBig n)) =
      Fintype.card (ExactWords alphabet23 n) :=
    (Fintype.card_congr (Equiv.ofInjective _ (smallWordIntoBig_injective n))).symm
  have hh : Fintype.card (HWords n) =
      Fintype.card (ExactWords alphabet2345 n) - Fintype.card (ExactWords alphabet23 n) := by
    rw [Fintype.card_subtype_compl, hc]
  rw [hh, Int.ofNat_sub hi]
  simp [capacityH, wordCount]

theorem alphabet2345_polynomial : alphabetPolynomial alphabet2345 =
    (X : PowerSeries ℤ)^2 + X^3 + X^4 + X^5 := by
  change (∑ a : Fin 4, (X : PowerSeries ℤ) ^ (a.val + 2)) = _
  simp only [Fin.sum_univ_succ]
  norm_num
  ring

/-- Original submitted H, with its exact two factors and numerator. -/
theorem capacityH_source_identity :
    ((1 - (X : PowerSeries ℤ)^2 - X^3) *
      (1 - X^2 - X^3 - X^4 - X^5)) * capacityH = X^4 + X^5 := by
  have hs := capacityC0_source_identity
  have hl := wordSeries_identity alphabet2345
  rw [alphabet2345_polynomial] at hl
  have hl' : (1 - (X : PowerSeries ℤ)^2 - X^3 - X^4 - X^5) *
      wordSeries alphabet2345 = 1 := by
    simpa [sub_sub] using hl
  calc
    _ = (1 - (X : PowerSeries ℤ)^2 - X^3) *
          ((1 - X^2 - X^3 - X^4 - X^5) * wordSeries alphabet2345) -
        (1 - X^2 - X^3 - X^4 - X^5) *
          ((1 - X^2 - X^3) * capacityC0) := by
      unfold capacityH capacityC0
      ring
    _ = (X : PowerSeries ℤ)^4 + X^5 := by rw [hl', hs]; ring

/-- Expanded denominator of original H; expansion is proved below. -/
def hDenominator (n : ℕ) : ℤ :=
  if n = 0 then 1 else if n = 2 ∨ n = 3 then -2 else
    if n = 5 ∨ n = 8 then 1 else if n = 6 ∨ n = 7 then 2 else 0

def hNumerator (n : ℕ) : ℤ := if n = 4 ∨ n = 5 then 1 else 0

theorem hDenominator_coeff (n : ℕ) :
    coeff n ((1 - (X : PowerSeries ℤ)^2 - X^3) *
      (1 - X^2 - X^3 - X^4 - X^5)) = hDenominator n := by
  have he : (1 - (X : PowerSeries ℤ)^2 - X^3) *
      (1 - X^2 - X^3 - X^4 - X^5) =
      1 - (X^2 + X^2) - (X^3 + X^3) + X^5 + (X^6 + X^6) + (X^7 + X^7) + X^8 := by ring
  rw [he]
  simp only [map_add, map_sub, coeff_one, coeff_X_pow, hDenominator]
  split_ifs <;> omega

theorem hNumerator_coeff (n : ℕ) :
    coeff n ((X : PowerSeries ℤ)^4 + X^5) = hNumerator n := by
  simp only [map_add, coeff_X_pow, hNumerator]
  split_ifs <;> omega

theorem capacityH_coefficients (n : ℕ) :
    coeff n capacityH = rationalCoeff hNumerator hDenominator n := by
  have h := source_coefficients_eq_recurrence ((X : PowerSeries ℤ)^4 + X^5)
    ((1 - X^2 - X^3) * (1 - X^2 - X^3 - X^4 - X^5)) capacityH
    (by simp) capacityH_source_identity n
  simpa only [hNumerator_coeff, hDenominator_coeff] using h

/-- An intentionally small, independently accepted prefix. It is not the full
capacity check through degree 1500 or any of the paper's 836 comparisons. -/
def hFirst31 : List ℤ :=
  [0, 0, 0, 0, 1, 1, 2, 4, 6, 11, 17, 28, 45, 71, 113, 177,
   278, 434, 676, 1051, 1630, 2525, 3905, 6033, 9311, 14358,
   22125, 34072, 52443, 80682, 124079]

theorem hFirst31_valid : ValidPrefix hNumerator hDenominator hFirst31 := by
  decide

/-- A perturbed source coefficient is rejected by the same exact checker. -/
theorem hFirst31_corruption_rejected :
    ¬ ValidPrefix hNumerator hDenominator (hFirst31.set 12 46) := by
  decide

/-- End-to-end finite acceptance: each checked integer counts the actual
original no-1 depth-four-or-five word source. -/
theorem hFirst31_source_correct (n : ℕ) (hn : n < 31) :
    hFirst31.getD n 0 = (Fintype.card (HWords n) : ℤ) := by
  rw [← capacityH_source_coeff, capacityH_coefficients]
  exact validPrefix_sound _ _ _ hFirst31_valid n hn

#print axioms rationalCoeff_sound
#print axioms rationalCoeff_unique
#print axioms validPrefix_sound
#print axioms capacityC0_source_identity
#print axioms capacityH_source_identity
#print axioms hFirst31_valid
#print axioms hFirst31_source_correct

end SubmittedGenus.FiniteArithmetic
