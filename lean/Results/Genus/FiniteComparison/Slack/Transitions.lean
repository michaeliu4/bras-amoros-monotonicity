import Results.Genus.FiniteComparison.Slack.Acceptance
namespace SubmittedGenus.FiniteComparison.Slack
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

/-- Strict denominator-cleared bounds certify the displayed downward
six-decimal truncation, rather than a floating-point approximation. -/
def Transition (g lower:ℕ) : Prop :=
  (lower:ℤ)*(Nat.fastFib g:ℤ)<1000000*delta g ∧
  1000000*delta g<(lower+1:ℤ)*(Nat.fastFib g:ℤ)
instance (g l:ℕ) : Decidable (Transition g l) := inferInstanceAs (Decidable (_∧_))
theorem transition_300 : Transition 300 871878 := by decide
theorem transition_301 : Transition 301 683638 := by decide
theorem transition_603 : Transition 603 872080 := by decide
theorem transition_604 : Transition 604 650368 := by decide
theorem transition_605 : Transition 605 513344 := by decide
theorem transition_836 : Transition 836 513474 := by decide

theorem five_before_switch : upperFive 300=capFiveTable 300 := rfl
theorem five_after_switch : upperFive 301=113*1000^301/633^301 := rfl
theorem four_before_switch : upperFour 603=capFourTable 603 := rfl
theorem four_after_switch : upperFour 604=capFourTable 604+221715*Nat.fastFib 604/1000000 := rfl
end SubmittedGenus.FiniteComparison.Slack
