import Results.Genus.FiniteArithmetic.DeepPopulation
import Results.Genus.FiniteArithmetic.ReservedPopulation
import Results.Genus.FiniteArithmetic.IsolatedFiveBridge
import Results.Genus.FiniteArithmetic.RationalM

set_option synthInstance.maxSize 1000

namespace SubmittedGenus.FiniteArithmetic

open OriginalSources PowerSeries

/-- The exact original W, with independent source semantics for all four terms. -/
noncomputable def capacityW : PowerSeries ℤ := capacityM + capacityH + IsolatedFive.capacityJ + capacityK

abbrev WSource := Graded.Sum MSource (Graded.Sum HWords (Graded.Sum IsolatedFive.JSource KWords))

theorem capacityW_source_identity : capacityW = Graded.series WSource := by
  unfold capacityW WSource
  rw [Graded.sum_series MSource (Graded.Sum HWords (Graded.Sum IsolatedFive.JSource KWords)),
    Graded.sum_series HWords (Graded.Sum IsolatedFive.JSource KWords),
    Graded.sum_series IsolatedFive.JSource KWords]
  have hh : Graded.series HWords = capacityH := by
    ext n
    rw [Graded.coeff_series, capacityH_source_coeff]
  have hk : Graded.series KWords = capacityK := by
    ext n
    rw [Graded.coeff_series, capacityK_source_coeff]
  rw [hh, hk]
  change capacityM + capacityH + IsolatedFive.capacityJ + capacityK =
    capacityM + (capacityH + (IsolatedFive.capacityJ + capacityK))
  ring

@[simp] theorem capacityW_source_coeff (g : ℕ) :
    coeff g capacityW = (Fintype.card (WSource g) : ℤ) := by
  rw [capacityW_source_identity, Graded.coeff_series]

/-- The manuscript's original majorant lemma, on actual ordered source classes. -/
theorem original_population_le_W (g : ℕ) :
    (Fintype.card (SourceClass g .D) : ℤ) + Fintype.card (SourceClass g .I) +
      Fintype.card (SourceClass g .B) ≤ coeff g capacityW := by
  have hd := source_D_coeff_le g
  have hi := IsolatedFive.source_I_coeff_le g
  have hb := source_B_coeff_le g
  simp only [capacityW, map_add] at *
  omega

/-- Once an exact W coefficient bound is accepted, it supplies the only
population premise required by the genuine joint D/I allocation. -/
theorem original_binary_capacity_of_W (g : ℕ)
    (hw : coeff g capacityW ≤ (Nat.fib g : ℤ)) :
    Fintype.card (SourceClass g .D) + Fintype.card (SourceClass g .I) +
      Fintype.card (SourceClass g .B) ≤ Nat.fib g := by
  have h := (original_population_le_W g).trans hw
  exact_mod_cast h

noncomputable def hPolynomialDenominator : PowerSeries ℤ :=
  (1 - X^2 - X^3) * (1 - X^2 - X^3 - X^4 - X^5)
noncomputable def hPolynomialNumerator : PowerSeries ℤ := X^4 + X^5
noncomputable def jPolynomialDenominator : PowerSeries ℤ :=
  (1 - 2 * X^5 - X^6) * (1 - X^2 - X^3) * (1 - 3 * X^4 - 2 * X^5 - X^6)
noncomputable def jPolynomialNumerator : PowerSeries ℤ := 2 * X^12 + 4 * X^14 + 2 * X^15
noncomputable def kPolynomialDenominator : PowerSeries ℤ :=
  (1 - X^2 - X^3)^2 * (1 - X^2 - X^3 - X^4)

noncomputable def wPolynomialDenominator : PowerSeries ℤ :=
  mDenominator * hPolynomialDenominator * jPolynomialDenominator * kPolynomialDenominator
noncomputable def wPolynomialNumerator : PowerSeries ℤ :=
  mNumerator * hPolynomialDenominator * jPolynomialDenominator * kPolynomialDenominator +
  hPolynomialNumerator * mDenominator * jPolynomialDenominator * kPolynomialDenominator +
  jPolynomialNumerator * mDenominator * hPolynomialDenominator * kPolynomialDenominator +
  X^9 * mDenominator * hPolynomialDenominator * jPolynomialDenominator

/-- A single exact polynomial recurrence for the source-correct original W. -/
theorem capacityW_polynomial_identity : wPolynomialDenominator * capacityW = wPolynomialNumerator := by
  have hm := capacityM_polynomial_identity
  have hh : hPolynomialDenominator * capacityH = hPolynomialNumerator := capacityH_source_identity
  have hj : jPolynomialDenominator * IsolatedFive.capacityJ = jPolynomialNumerator := by
    simpa [jPolynomialDenominator, jPolynomialNumerator, nsmul_eq_mul] using
      IsolatedFive.capacityJ_source_identity
  have hk : kPolynomialDenominator * capacityK = (X : PowerSeries ℤ)^9 := capacityK_source_identity
  unfold wPolynomialDenominator wPolynomialNumerator capacityW
  calc
    _ = (mDenominator * capacityM) * hPolynomialDenominator * jPolynomialDenominator * kPolynomialDenominator +
      (hPolynomialDenominator * capacityH) * mDenominator * jPolynomialDenominator * kPolynomialDenominator +
      (jPolynomialDenominator * IsolatedFive.capacityJ) * mDenominator * hPolynomialDenominator * kPolynomialDenominator +
      (kPolynomialDenominator * capacityK) * mDenominator * hPolynomialDenominator * jPolynomialDenominator := by ring
    _ = _ := by rw [hm, hh, hj, hk]

#print axioms original_population_le_W
#print axioms original_binary_capacity_of_W
#print axioms capacityW_polynomial_identity

end SubmittedGenus.FiniteArithmetic
