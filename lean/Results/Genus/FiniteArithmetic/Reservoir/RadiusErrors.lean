import Results.Genus.FiniteArithmetic.Reservoir.RadiusValues

namespace SubmittedGenus.FiniteArithmetic.Reservoir
open PowerSeries Analytic
noncomputable section
set_option maxHeartbeats 2000000

def safeErrorValue : ℝ := (1+radius)*(1+radius^2)^2/(1-vValueAt)
def earlyErrorValue : ℝ := radius^4*(1+radius+radius^2)/(1-uValueAt)/(1-uValueAt^2)
def failureBlockValue : ℝ := (1+radius^2)/(1-2*radius^3-radius^4)

theorem safeError_evaluates : PositiveEval radius safeErrorSeries safeErrorValue := by
  have hx : PositiveEval radius (X : PowerSeries ℤ) radius := by simpa using positiveEval_xpow radius 1
  have h0 := wUV_evaluates unitDecoration 1 unit_decoration_evaluates (Or.inl rfl) 0 (by omega)
  have h := (((positiveEval_one radius).add radius_nonneg hx).mul radius_nonneg
    (((positiveEval_one radius).add radius_nonneg (positiveEval_xpow radius 2)).pow radius_nonneg 2)).mul radius_nonneg h0
  simpa only [safeErrorSeries,safeErrorValue,one_pow,mul_one,div_eq_mul_inv,one_mul] using h

theorem earlyError_evaluates : PositiveEval radius earlyErrorSeries earlyErrorValue := by
  have hx : PositiveEval radius (X : PowerSeries ℤ) radius := by simpa using positiveEval_xpow radius 1
  have hU := wU_evaluates unitDecoration 1 unit_decoration_evaluates (Or.inl rfl) 0 (by omega)
  have hUU := wUU_evaluates unitDecoration 1 unit_decoration_evaluates (Or.inl rfl) 0 (by omega)
  have h := (((positiveEval_xpow radius 4).mul radius_nonneg
    (((positiveEval_one radius).add radius_nonneg hx).add radius_nonneg (positiveEval_xpow radius 2))).mul
      radius_nonneg hU).mul radius_nonneg hUU
  simpa only [earlyErrorSeries,earlyErrorValue,one_pow,mul_one,div_eq_mul_inv,one_mul] using h

theorem failureBlock_evaluates : PositiveEval radius failureBlockSeries failureBlockValue := by
  have ha := (positiveEval_one radius).add radius_nonneg (positiveEval_xpow radius 2)
  have hb := ((positiveEval_nat radius 2).mul radius_nonneg (positiveEval_xpow radius 3)).add
    radius_nonneg (positiveEval_xpow radius 4)
  have he : (1-(2*X^3+X^4))*failureBlockSeries = 1+X^2 := by
    convert failureBlockSeries_identity using 1 <;> ring
  have h := ha.geometric radius_nonneg hb (by norm_num [radius]) he (by
    intro n
    change 0 ≤ coeff n (Graded.series (Reflection.Blocks failureSystem))
    rw [Graded.coeff_series]
    positivity)
  convert h using 1 <;> unfold failureBlockValue <;> congr 1 <;> ring

/-- Exact rational values of the original marked-failure operator. Their
identification with actual failure masses requires the separately proved
source identity and convergence; these definitions are not such assumptions. -/
def safeFailureValue : ℝ := radius*((safeMarkedValue 1-safeMarkedValue cValueAt)/(1-cValueAt)+
  failureBlockValue*safeMarkedValue cValueAt)
def earlyFailureValue : ℝ := radius*((earlyMarkedValue 1-earlyMarkedValue cValueAt)/(1-cValueAt)+
  failureBlockValue*earlyMarkedValue cValueAt)
def totalErrorValue : ℝ := safeErrorValue+earlyErrorValue+safeFailureValue+earlyFailureValue

/-- The original exact rational arithmetic check, kept separate from all
source identifications and convergence obligations. -/
theorem totalErrorValue_lt_seventy_eight : totalErrorValue < 78 := by
  norm_num [totalErrorValue,safeErrorValue,earlyErrorValue,safeFailureValue,earlyFailureValue,
    failureBlockValue,safeMarkedValue,earlyMarkedValue,safeValue,earlyValue,
    radius,uValueAt,sValueAt,vValueAt,cValueAt]

#print axioms failureBlock_evaluates
#print axioms totalErrorValue_lt_seventy_eight
end
end SubmittedGenus.FiniteArithmetic.Reservoir
