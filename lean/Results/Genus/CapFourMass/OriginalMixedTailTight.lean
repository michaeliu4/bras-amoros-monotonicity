import Results.Genus.CapFourMass.IntervalMixedAcceptance

/-! Tighter outward rounding of the unchanged original mixed tail at 100.
This adds no premise, source representation, or truncation change. -/
namespace SubmittedGenus.CapFourMass.Interval
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

theorem original_mixed_tail_tight_accepts :
    acceptsUpper (TailSyntax.mixed 100) 446302688776605197 1000000000000000=true := by
  decide +kernel

theorem original_mixed_tail_tight :
    mixedTailExpression 100 ≤ (446302688776605197 : ℝ)/1000000000000000 := by
  have h := acceptsUpper_sound original_mixed_tail_tight_accepts
  rw [closedReal,TailSyntax.mixed_real] at h
  simpa only [Int.cast_ofNat] using h

theorem original_mixed_tail_margin :
    mixedTailExpression 100 + (803 : ℝ)/1000000000000000 ≤ mixedTailCeiling := by
  have h := original_mixed_tail_tight
  unfold mixedTailCeiling
  linarith

theorem original_mixed_tail_lt : mixedTailExpression 100 < mixedTailCeiling := by
  have h := original_mixed_tail_margin
  linarith

#print axioms original_mixed_tail_tight_accepts
#print axioms original_mixed_tail_tight
#print axioms original_mixed_tail_margin
#print axioms original_mixed_tail_lt
end SubmittedGenus.CapFourMass.Interval
