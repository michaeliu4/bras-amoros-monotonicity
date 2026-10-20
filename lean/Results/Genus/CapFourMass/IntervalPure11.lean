import Results.Genus.CapFourMass.IntervalPurePieces

namespace SubmittedGenus.CapFourMass.Interval
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

/-- Kernel acceptance of one complete original P=400 parity class. -/
theorem pure_11_accepts : acceptsUpper (pureTerm 400 1 1) 977996362023659 1000000000000000=true := by decide +kernel

theorem pure_11_le : closedReal (pureTerm 400 1 1)≤(977996362023659:ℝ)/1000000000000000 := by
  have h := acceptsUpper_sound pure_11_accepts
  norm_num only [Int.cast_ofNat] at h ⊢
  exact h

#print axioms pure_11_accepts
#print axioms pure_11_le
end SubmittedGenus.CapFourMass.Interval
