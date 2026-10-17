import Results.Genus.CapFourMass.IntervalCore
import Results.Genus.CapFourMass.InputNumerics

namespace SubmittedGenus.CapFourMass.Interval

/-- Exact rescaling of the submitted 2^56 root enclosure into 2^112 units. -/
def lambdaInput : Box :=
  ⟨73338785529844359*72057594037927936,73338785529844360*72057594037927936⟩
def feedbackInput : Box :=
  ⟨73854862990399022*72057594037927936,73854862990399023*72057594037927936⟩
def normalizerInput : Box :=
  ⟨70651823329321825*72057594037927936,70651823329321825*72057594037927936⟩

theorem lambdaInput_contains : Contains lambdaInput lam := by
  have h := lambda_input_interval
  norm_num [intervalUnit] at h
  norm_num [Contains,lambdaInput,unit]
  constructor <;> linarith

theorem feedbackInput_contains : Contains feedbackInput feedbackT := by
  have h := T_input_interval
  norm_num [intervalUnit] at h
  norm_num [Contains,feedbackInput,unit]
  constructor <;> linarith

theorem normalizerInput_contains : Contains normalizerInput normalizer := by
  norm_num [Contains,normalizerInput,normalizer,unit]

end SubmittedGenus.CapFourMass.Interval
