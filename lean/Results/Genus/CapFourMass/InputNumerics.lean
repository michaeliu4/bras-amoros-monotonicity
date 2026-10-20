import Results.Genus.CapFourMass.Normalization

/-!
# Submitted interval input enclosures and outward rounding

The root input enclosure is proved from the exact quadratic equation. The
three output-unit-to-decimal comparisons below only verify the paper's stated
outward rounding; they do not claim to verify the source graph evaluations.
-/
noncomputable section
namespace SubmittedGenus.CapFourMass

def intervalUnit : ℝ := 72057594037927936

lemma lambda_input_interval :
    73338785529844359/intervalUnit ≤ lam ∧ lam ≤ 73338785529844360/intervalUnit := by
  have hq := lam_quadratic
  have hp := lam_pos
  norm_num [carryA,carryB,radius] at hq
  norm_num [intervalUnit]
  constructor <;> nlinarith

lemma T_input_interval :
    73854862990399022/intervalUnit ≤ feedbackT ∧ feedbackT ≤ 73854862990399023/intervalUnit :=
  feedbackT_interval

def purePrefixUnits : ℝ := 101235082714477743831/intervalUnit
def shortPrefixUnits : ℝ := 3738038979785516612/intervalUnit
def mixedPrefixUnits : ℝ := 36617965435406954/intervalUnit

def purePrefixCeiling : ℝ := 1404918996618068/1000000000000
def shortPrefixCeiling : ℝ := 51875711778803/1000000000000
def mixedPrefixCeiling : ℝ := 508176354267/1000000000000
def shortTailCeiling : ℝ := 116098136035634/1000000000000
def mixedTailCeiling : ℝ := 446302688776606/1000000000000
def pureTailCeiling : ℝ := 3745874303725/1000000000000

lemma prefix_outward_rounding : purePrefixUnits < purePrefixCeiling ∧
    shortPrefixUnits < shortPrefixCeiling ∧ mixedPrefixUnits < mixedPrefixCeiling := by
  norm_num [purePrefixUnits,shortPrefixUnits,mixedPrefixUnits,intervalUnit,
    purePrefixCeiling,shortPrefixCeiling,mixedPrefixCeiling]

/-- Final arithmetic of the six manuscript ceilings, separate from the
still-required source theorems that establish each ceiling. -/
lemma six_ceilings_lt_2024 :
    purePrefixCeiling+shortPrefixCeiling+mixedPrefixCeiling+
      shortTailCeiling+mixedTailCeiling+pureTailCeiling < 2024 := by
  norm_num [purePrefixCeiling,shortPrefixCeiling,mixedPrefixCeiling,
    shortTailCeiling,mixedTailCeiling,pureTailCeiling]

end SubmittedGenus.CapFourMass
