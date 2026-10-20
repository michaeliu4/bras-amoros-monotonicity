import Results.Genus.CapFourMass.IntervalTailSyntax
import Results.Genus.CapFourMass.InputNumerics

namespace SubmittedGenus.CapFourMass.Interval
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

theorem original_mixed_tail_accepts :
    acceptsUpper (TailSyntax.mixed 100) 446302688776606 1000000000000=true := by decide +kernel

/-- Actual original omitted mixed source tail, evaluated from its finite-prefix expression. -/
theorem original_mixed_tail_le : mixedTailExpression 100≤mixedTailCeiling := by
  have h := acceptsUpper_sound original_mixed_tail_accepts
  rw [closedReal,TailSyntax.mixed_real] at h
  simpa only [mixedTailCeiling,Int.cast_ofNat] using h

#print axioms original_mixed_tail_accepts
#print axioms original_mixed_tail_le
end SubmittedGenus.CapFourMass.Interval
