import Results.Genus.CapFourMass.IntervalPure00
import Results.Genus.CapFourMass.IntervalPure01
import Results.Genus.CapFourMass.IntervalPure10
import Results.Genus.CapFourMass.IntervalPure11
import Results.Genus.CapFourMass.InputNumerics

namespace SubmittedGenus.CapFourMass.Interval

/-- All four actual P=400 parity-class computations passed the kernel checker. -/
theorem original_pure_tail_accepts :
    acceptsUpper (pureTerm 400 0 0) 895839752487738 1000000000000000=true ∧
    acceptsUpper (pureTerm 400 0 1) 937559633222279 1000000000000000=true ∧
    acceptsUpper (pureTerm 400 1 0) 934478555991093 1000000000000000=true ∧
    acceptsUpper (pureTerm 400 1 1) 977996362023659 1000000000000000=true :=
  ⟨pure_00_accepts,pure_01_accepts,pure_10_accepts,pure_11_accepts⟩

/-- Exact addition of the four source classes proves the original decimal ceiling. -/
theorem original_pure_tail_le : pureTailExpression 400≤pureTailCeiling := by
  have he : pureTailExpression 400=closedReal (TailSyntax.pure 400) :=
    (TailSyntax.pure_real (fun _ => 0) 400).symm
  rw [he,pure_eq_four]
  have h00:=pure_00_le
  have h01:=pure_01_le
  have h10:=pure_10_le
  have h11:=pure_11_le
  unfold pureTailCeiling
  linarith

#print axioms original_pure_tail_accepts
#print axioms original_pure_tail_le
end SubmittedGenus.CapFourMass.Interval
