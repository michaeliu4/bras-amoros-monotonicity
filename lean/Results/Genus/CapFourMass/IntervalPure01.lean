import Results.Genus.CapFourMass.IntervalPurePieces

namespace SubmittedGenus.CapFourMass.Interval
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

/-- Kernel acceptance of one complete original P=400 parity class. -/
theorem pure_01_accepts : acceptsUpper (pureTerm 400 0 1) 937559633222279 1000000000000000=true := by decide +kernel

theorem pure_01_le : closedReal (pureTerm 400 0 1)≤(937559633222279:ℝ)/1000000000000000 := by
  have h := acceptsUpper_sound pure_01_accepts
  norm_num only [Int.cast_ofNat] at h ⊢
  exact h

#print axioms pure_01_accepts
#print axioms pure_01_le
end SubmittedGenus.CapFourMass.Interval
