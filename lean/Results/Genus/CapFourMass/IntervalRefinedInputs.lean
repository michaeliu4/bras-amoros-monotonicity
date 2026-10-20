import Results.Genus.CapFourMass.IntervalInputs

namespace SubmittedGenus.CapFourMass.Interval

/-- Finer enclosure of the same actual positive carry root, from its exact quadratic. -/
def lambdaRefined : Box := ⟨5284616434944188519738346999093497,5284616434944188519738346999093498⟩
def feedbackRefined : Box := ⟨5321803735088961165708832057447461,5321803735088961165708832057447462⟩

theorem lambdaRefined_contains : Contains lambdaRefined lam := by
  have hq:=lam_quadratic
  have hp:=lam_pos
  norm_num [carryA,carryB,radius] at hq
  norm_num [Contains,lambdaRefined,unit]
  constructor <;> nlinarith

theorem feedbackRefined_contains : Contains feedbackRefined feedbackT := by
  norm_num [Contains,feedbackRefined,unit,feedbackT,feedbackGamma,feedbackBeta,
    LocalWeights.delta,LocalWeights.epsilon,LocalWeights.s,LocalWeights.a,LocalWeights.b,radius]

end SubmittedGenus.CapFourMass.Interval
