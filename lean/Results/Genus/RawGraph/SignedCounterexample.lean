import Results.Genus.RawGraph
import Mathlib.Tactic.IntervalCases
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# The original signed-correction counterexample

At fixed pivots (r,p)=(1,2), the raw series has coefficients F7=0,F8=1,F9=0.
Thus the coefficient of z^9 in (1-z-z^2)F is -1. This verifies the submitted
warning that the fixed-pivot correction is signed, directly from raw sources.
-/

namespace SubmittedGenus.RawGraph.SignedCounterexample

private def onlyWord : Fin 2 → Fin 5 := ![4, 4]

private theorem source_three (x : Fin 2 → Fin 5) :
    RawAdmissible 1 2 4 (boundedWord (m := 3) (a := 4) x) ↔ x = onlyWord := by
  have h : RawAdmissible 1 2 4 (boundedWord (m := 3) (a := 4) x) ↔
      (x 0).val = 4 ∧ (x 1).val = 4 := by
    simp [RawAdmissible, Parameters, Alphabet, Ordinary, Carried, IsPivot,
      physical, boundedWord, Fin.forall_fin_succ]
    omega
  rw [h]
  constructor
  · rintro ⟨h0, h1⟩
    funext i
    fin_cases i <;> apply Fin.ext <;> assumption
  · rintro rfl
    simp [onlyWord]

/-- The multiplicity-three source consists of the two fixed pivots only. -/
theorem raw_three : rawPolynomial 3 1 2 4 = (Polynomial.X : Polynomial ℕ) ^ 8 := by
  classical
  unfold rawPolynomial
  rw [Finset.sum_eq_single onlyWord]
  · simp [source_three, genus, boundedWord, onlyWord, Fin.sum_univ_succ]
  · intro x _ hx
    simp [source_three, hx]
  · simp

/-- Coefficients outside the submitted elementary multiplicity support vanish. -/
theorem coeff_zero_of_multiplicity {m r p g : ℕ} (hg : g < m + 5) :
    (rawPolynomial m r p 4).coeff g = 0 := by
  rw [rawPolynomial_coeff]
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨_, hx, he⟩ := Finset.mem_filter.mp hx
  have hs := cap_four_genus_multiplicity hx
  omega

/-- Uniform source evaluation at all multiplicities through genus9. -/
theorem coefficient_small (m g : ℕ) (hg : g ≤ 9) :
    (rawPolynomial m 1 2 4).coeff g = if m = 3 ∧ g = 8 then 1 else 0 := by
  by_cases hm : 5 ≤ m
  · rw [coeff_zero_of_multiplicity (by omega)]
    simp [show m ≠ 3 by omega]
  · have hm' : m < 5 := by omega
    interval_cases m
    · rw [rawPolynomial_invalid (by decide)]
      simp
    · rw [rawPolynomial_invalid (by decide)]
      simp
    · rw [rawPolynomial_invalid (by decide)]
      simp
    · simp [raw_three, Polynomial.coeff_X_pow]
    · simp [fixture_rawPolynomial, Polynomial.coeff_X_pow, show g ≠ 10 by omega,
        show g ≠ 11 by omega]

/-- A coefficient of the formal fixed-pivot sum. Support proves that every
omitted multiplicity contributes zero, so this finite definition is complete. -/
noncomputable def fixedPivotCoeff (r p g : ℕ) : ℕ :=
  ∑ m ∈ Finset.range (g + 1), (rawPolynomial m r p 4).coeff g

theorem omitted_multiplicity_zero {r p g m : ℕ} (hm : g + 1 ≤ m) :
    (rawPolynomial m r p 4).coeff g = 0 :=
  coeff_zero_of_multiplicity (by omega)

@[simp] theorem fixedPivotCoeff_seven : fixedPivotCoeff 1 2 7 = 0 := by
  simp [fixedPivotCoeff, coefficient_small _ _ (by decide : 7 ≤ 9)]

@[simp] theorem fixedPivotCoeff_eight : fixedPivotCoeff 1 2 8 = 1 := by
  simp [fixedPivotCoeff, coefficient_small _ _ (by decide : 8 ≤ 9)]

@[simp] theorem fixedPivotCoeff_nine : fixedPivotCoeff 1 2 9 = 0 := by
  simp [fixedPivotCoeff, coefficient_small _ _ (by decide : 9 ≤ 9)]

noncomputable def fixedPivotSeries (r p : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk (fun g => (fixedPivotCoeff r p g : ℤ))

/-- Source-exact negative corrected coefficient from the original paper. -/
theorem corrected_coefficient_nine :
    PowerSeries.coeff 9 ((1 - PowerSeries.X - PowerSeries.X ^ 2) * fixedPivotSeries 1 2) =
      (-1 : ℤ) := by
  rw [sub_mul, sub_mul, one_mul]
  simp [PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_succ_X_mul,
    fixedPivotSeries, PowerSeries.coeff_mk]

end SubmittedGenus.RawGraph.SignedCounterexample
