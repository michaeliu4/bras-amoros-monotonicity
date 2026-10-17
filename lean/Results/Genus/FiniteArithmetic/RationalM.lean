import Results.Genus.FiniteArithmetic.HighDepthSource

namespace SubmittedGenus.FiniteArithmetic

open PowerSeries Reflection

noncomputable def tailDenominator : PowerSeries ℤ :=
  (1 - X)^2 - 7 * X^8 + 6 * X^9
noncomputable def tailNumerator : PowerSeries ℤ :=
  X^9 * (1 - X) * (1 - X + X^4)^2

/-- Clearing the two exact geometric sources yields a polynomial block relation. -/
theorem tail_block_polynomial_identity :
    tailDenominator * OriginalTail.blockSeries = (1 - X) * (1 - X + X^4) := by
  have hb := OriginalTail.pairSeries_identity
  have hc := Geometric.digitSeries_identity 4
  have ht := OriginalTail.blockSeries_identity
  have he : tailDenominator = (1 - (X : PowerSeries ℤ))^2 * (1 - OriginalTail.pairSeries) := by
    unfold tailDenominator
    rw [mul_sub, mul_one, hb]
    simp only [nsmul_eq_mul]
    ring
  rw [he, mul_assoc, ht]
  calc
    _ = (1 - (X : PowerSeries ℤ)) * ((1 - X) + (1 - X) * Geometric.digitSeries 4) := by ring
    _ = _ := by rw [hc]

/-- Polynomial rational identity for the complete original unbounded M tail. -/
theorem capacityMTail_polynomial_identity :
    tailDenominator^2 * OriginalTail.capacityMTail = tailNumerator := by
  rw [OriginalTail.capacityMTail_factorization]
  calc
    _ = Geometric.digitSeries 9 * (tailDenominator * OriginalTail.blockSeries)^2 := by ring
    _ = Geometric.digitSeries 9 * ((1 - X) * (1 - X + X^4))^2 := by
      rw [tail_block_polynomial_identity]
    _ = ((1 - X) * Geometric.digitSeries 9) * (1 - X) * (1 - X + X^4)^2 := by ring
    _ = tailNumerator := by rw [Geometric.digitSeries_identity]; rfl

noncomputable def factorDenominator (k : ℕ) : PowerSeries ℤ := 1 - pairPolynomial k k
noncomputable def factorNumerator (k : ℕ) : PowerSeries ℤ := 1 + centerPolynomial k k

noncomputable def mDenominator : PowerSeries ℤ :=
  factorDenominator 5 * factorDenominator 6 * factorDenominator 7 * factorDenominator 8 * tailDenominator^2

noncomputable def mNumerator : PowerSeries ℤ :=
  X^6 * factorNumerator 6 * factorNumerator 5 * factorDenominator 7 * factorDenominator 8 * tailDenominator^2 +
  X^7 * factorNumerator 7 * factorNumerator 6 * factorDenominator 5 * factorDenominator 8 * tailDenominator^2 +
  X^8 * factorNumerator 8 * factorNumerator 7 * factorDenominator 5 * factorDenominator 6 * tailDenominator^2 +
  tailNumerator * factorDenominator 5 * factorDenominator 6 * factorDenominator 7 * factorDenominator 8

/-- All original M terms are combined without assuming a coefficient table. -/
theorem capacityM_polynomial_identity : mDenominator * capacityM = mNumerator := by
  have h5 := capacityFactor_source_identity 5
  have h6 := capacityFactor_source_identity 6
  have h7 := capacityFactor_source_identity 7
  have h8 := capacityFactor_source_identity 8
  change factorDenominator 5 * capacityFactor 5 = factorNumerator 5 at h5
  change factorDenominator 6 * capacityFactor 6 = factorNumerator 6 at h6
  change factorDenominator 7 * capacityFactor 7 = factorNumerator 7 at h7
  change factorDenominator 8 * capacityFactor 8 = factorNumerator 8 at h8
  rw [capacityM_source_identity]
  unfold mDenominator mNumerator
  calc
    _ = (X : PowerSeries ℤ)^6 * (factorDenominator 6 * capacityFactor 6) *
        (factorDenominator 5 * capacityFactor 5) * factorDenominator 7 * factorDenominator 8 * tailDenominator^2 +
      X^7 * (factorDenominator 7 * capacityFactor 7) * (factorDenominator 6 * capacityFactor 6) *
        factorDenominator 5 * factorDenominator 8 * tailDenominator^2 +
      X^8 * (factorDenominator 8 * capacityFactor 8) * (factorDenominator 7 * capacityFactor 7) *
        factorDenominator 5 * factorDenominator 6 * tailDenominator^2 +
      (tailDenominator^2 * OriginalTail.capacityMTail) * factorDenominator 5 * factorDenominator 6 *
        factorDenominator 7 * factorDenominator 8 := by ring
    _ = _ := by rw [h5, h6, h7, h8, capacityMTail_polynomial_identity]

#print axioms capacityMTail_polynomial_identity
#print axioms capacityM_polynomial_identity

end SubmittedGenus.FiniteArithmetic
