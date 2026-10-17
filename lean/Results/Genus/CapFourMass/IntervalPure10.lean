import Results.Genus.CapFourMass.IntervalPurePieces

namespace SubmittedGenus.CapFourMass.Interval
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

/-- Kernel acceptance of one complete original P=400 parity class. -/
theorem pure_10_accepts : acceptsUpper (pureTerm 400 1 0) 934478555991093 1000000000000000=true := by decide +kernel

theorem pure_10_le : closedReal (pureTerm 400 1 0)≤(934478555991093:ℝ)/1000000000000000 := by
  have h := acceptsUpper_sound pure_10_accepts
  norm_num only [Int.cast_ofNat] at h ⊢
  exact h

#print axioms pure_10_accepts
#print axioms pure_10_le
end SubmittedGenus.CapFourMass.Interval
