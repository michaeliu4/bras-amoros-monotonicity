import Results.Genus.FiniteArithmetic.Reservoir.FailureAnalysis

namespace SubmittedGenus.FiniteArithmetic.Reservoir
open PowerSeries Analytic
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Evaluate the actual marked-failure population only after the positive
kernel argument has supplied convergence. -/
theorem actualFailure_evaluates {C : Type} (F : OriginalReservoir.PrefixFamily C)
    {A B : ℝ} (h1 : PositiveEval radius (markedPrefixSeries F 1) A)
    (hc : PositiveEval radius (markedPrefixSeries F c) B) :
    PositiveEval radius (actualFailureSeries F)
      (radius*((A-B)/(1-cValueAt)+failureBlockValue*B)) := by
  have hu := actualFailure_summable F hc.summable
  have hx : PositiveEval radius (X : PowerSeries ℤ) radius := by simpa using positiveEval_xpow radius 1
  have hq := (positiveEval_one radius).summable.sub c_evaluates.summable radius_nonneg
  have hd := h1.summable.sub hc.summable radius_nonneg
  have hxd := hx.summable.mul hd radius_nonneg
  have hqx := hq.mul hx.summable radius_nonneg
  have hqxa := hqx.mul failureBlock_evaluates.summable radius_nonneg
  have hqxac := hqxa.mul hc.summable radius_nonneg
  have hqv : massAt radius (1-c)=1-cValueAt := by
    rw [massAt_sub radius_nonneg (positiveEval_one radius).summable c_evaluates.summable,
      massAt_one,c_evaluates.value]
  have hv := congrArg (massAt radius) (failure_operator_identity F)
  rw [massAt_mul radius_nonneg hq hu,massAt_add radius_nonneg hxd hqxac,
    massAt_mul radius_nonneg hx.summable hd,
    massAt_sub radius_nonneg h1.summable hc.summable,
    massAt_mul radius_nonneg hqxa hc.summable,
    massAt_mul radius_nonneg hqx failureBlock_evaluates.summable,
    massAt_mul radius_nonneg hq hx.summable,
    hqv,hx.value,h1.value,hc.value,failureBlock_evaluates.value] at hv
  refine ⟨hu,?_,?_⟩
  · intro n; rw [actualFailureSeries_coeff]; positivity
  · have hne : 1-cValueAt≠0 := by norm_num [cValueAt,radius]
    have hsol : massAt radius (actualFailureSeries F)=
        (radius*(A-B)+(1-cValueAt)*radius*failureBlockValue*B)/(1-cValueAt) := by
      apply (eq_div_iff hne).mpr
      nlinarith [hv]
    rw [hsol]
    field_simp

#print axioms actualFailure_evaluates
end
end SubmittedGenus.FiniteArithmetic.Reservoir
