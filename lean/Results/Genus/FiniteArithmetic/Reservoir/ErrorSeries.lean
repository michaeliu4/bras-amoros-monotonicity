import Results.Genus.FiniteArithmetic.Reservoir.CandidateSeries
import Results.Genus.FiniteArithmetic.Reservoir.MarkedSeries

namespace SubmittedGenus.FiniteArithmetic.Reservoir

open PowerSeries
noncomputable section

/-- Original nonnegative error series and the retained early-family gain. -/
def safeErrorSeries : PowerSeries ℤ := (1+X)*(1+X^2)^2*wUV unitDecoration 0
def earlyErrorSeries : PowerSeries ℤ := X^4*(1+X+X^2)*wU unitDecoration 0*wUU unitDecoration 0
def earlyGainSeries : PowerSeries ℤ := X^9*(2+2*X+X^2)*wU unitDecoration 0*wUU unitDecoration 0

theorem safeErrorSeries_identity : (1-v)*safeErrorSeries = (1+X)*(1+X^2)^2 := by
  have h := wUV_identity unitDecoration 0
  simp only [pow_zero,mul_one] at h
  unfold safeErrorSeries
  calc
    _ = (1+X)*(1+X^2)^2*((1-v)*wUV unitDecoration 0) := by ring
    _ = _ := by rw [h,mul_one]

theorem earlyErrorSeries_identity : ((1-u)*(1-u^2))*earlyErrorSeries = X^4*(1+X+X^2) := by
  have hU := wU_identity unitDecoration 0
  have hUU := wUU_identity unitDecoration 0
  simp only [pow_zero,mul_one] at hU hUU
  unfold earlyErrorSeries
  calc
    _ = X^4*(1+X+X^2)*((1-u)*wU unitDecoration 0)*((1-u^2)*wUU unitDecoration 0) := by ring
    _ = _ := by rw [hU,hUU]; ring

theorem earlyGainSeries_identity : ((1-u)*(1-u^2))*earlyGainSeries = X^9*(2+2*X+X^2) := by
  have hU := wU_identity unitDecoration 0
  have hUU := wUU_identity unitDecoration 0
  simp only [pow_zero,mul_one] at hU hUU
  unfold earlyGainSeries
  calc
    _ = X^9*(2+2*X+X^2)*((1-u)*wU unitDecoration 0)*((1-u^2)*wUU unitDecoration 0) := by ring
    _ = _ := by rw [hU,hUU]; ring

/-- Exact source identity behind the first original Fibonacci main term. -/
theorem safe_candidate_error_identity : safeCandidateSeries + safeErrorSeries = binaryTailSeries := by
  have hne : (1-v)*(1-c) ≠ (0 : PowerSeries ℤ) := by
    intro h
    have hh := congrArg constantCoeff h
    norm_num [v,u,s,c] at hh
  apply mul_left_cancel₀ hne
  calc
    _ = (1-v)*((1-c)*safeCandidateSeries) + (1-c)*((1-v)*safeErrorSeries) := by ring
    _ = X*((1-v)*safeSeries)+(1-c)*((1+X)*(1+X^2)^2) := by
      rw [safeCandidateSeries_identity,safeErrorSeries_identity]; ring
    _ = 1-v := by rw [safeSeries_identity]; unfold v u s c; ring
    _ = (1-v)*((1-c)*binaryTailSeries) := by rw [binaryTailSeries_identity,mul_one]
    _ = _ := by ring

/-- Exact early-family identity retains the additional nonnegative gain. -/
theorem early_candidate_error_identity :
    earlyCandidateSeries + earlyErrorSeries = X^4*binaryTailSeries + earlyGainSeries := by
  have hne : ((1-u)*(1-u^2))*(1-c) ≠ (0 : PowerSeries ℤ) := by
    intro h
    have hh := congrArg constantCoeff h
    norm_num [u,c] at hh
  apply mul_left_cancel₀ hne
  calc
    _ = ((1-u)*(1-u^2))*((1-c)*earlyCandidateSeries) +
      (1-c)*(((1-u)*(1-u^2))*earlyErrorSeries) := by ring
    _ = X*(((1-u)*(1-u^2))*earlySeries)+(1-c)*(X^4*(1+X+X^2)) := by
      rw [earlyCandidateSeries_identity,earlyErrorSeries_identity]; ring
    _ = X^4*((1-u)*(1-u^2)) + (1-c)*(X^9*(2+2*X+X^2)) := by
      rw [earlySeries_identity]; unfold u c; ring
    _ = X^4*((1-u)*(1-u^2))*((1-c)*binaryTailSeries) +
      (1-c)*(((1-u)*(1-u^2))*earlyGainSeries) := by
      rw [binaryTailSeries_identity,earlyGainSeries_identity,mul_one]
    _ = _ := by ring

#print axioms safe_candidate_error_identity
#print axioms early_candidate_error_identity
end
end SubmittedGenus.FiniteArithmetic.Reservoir
