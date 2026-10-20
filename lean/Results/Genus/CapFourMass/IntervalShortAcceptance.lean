import Results.Genus.CapFourMass.IntervalTailSyntax
import Results.Genus.CapFourMass.InputNumerics

namespace SubmittedGenus.CapFourMass.Interval
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem original_short_tail_accepts :
    acceptsUpper (TailSyntax.short 100) 116098136035634 1000000000000=true := by decide +kernel

/-- Actual original omitted short source tail, evaluated from its finite-prefix expression. -/
theorem original_short_tail_le : shortTailExpression 100≤shortTailCeiling := by
  have h := acceptsUpper_sound original_short_tail_accepts
  rw [closedReal,TailSyntax.short_real] at h
  simpa only [shortTailCeiling,Int.cast_ofNat] using h

#print axioms original_short_tail_accepts
#print axioms original_short_tail_le
end SubmittedGenus.CapFourMass.Interval
