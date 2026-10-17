import Results.Genus.TailComparison.Scalar

/-! Additional exact displays at the submitted 836/837 join (paper2542–2549).
These strengthen the recorded arithmetic coverage; the main tail theorem does
not require the failure claim at836 or the two printed margin thresholds. -/
namespace SubmittedGenus.TailComparison

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2000

lemma capacityRatio_lt_limit (g : ℕ) : capacityRatio g < 1427/500 := by
  have hp : 0 < 50*rStar^2/((63/100)*rStar)^g := by unfold rStar; positivity
  unfold capacityRatio
  linarith

lemma xi_836_gt : (2875/1000:ℝ) < xi 836 := by
  norm_num [xi,qbar,sStar,z4,z5]

/-- The submitted scalar test actually fails at836, despite finite coverage. -/
theorem scalar_failure_836 : capacityRatio 836 < xi 836 :=
  (capacityRatio_lt_limit 836).trans ((by norm_num : (1427/500:ℝ)<2875/1000).trans xi_836_gt)

/-- The exact absolute margin printed after the finite comparison. -/
theorem joining_absolute_margin : (34104510/10^10:ℝ) < capacityRatio 837-xi 837 := by
  linarith [xi_837_lt,joining_decimal_lt_capacity_837]

/-- The exact relative margin printed after the finite comparison. -/
theorem joining_relative_margin :
    (11949783/10^10:ℝ) < (capacityRatio 837-xi 837)/capacityRatio 837 := by
  have hc : 0 < capacityRatio 837 :=
    (by norm_num : (0:ℝ)<2853985748250/1000000000000).trans joining_decimal_lt_capacity_837
  apply (lt_div_iff₀ hc).mpr
  linarith [xi_837_lt,joining_decimal_lt_capacity_837]

end SubmittedGenus.TailComparison
