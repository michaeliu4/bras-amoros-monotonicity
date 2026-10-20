import Results.Genus.CapFourMass.IntervalPureAcceptance

/-! Literal strictness of the submitted pure-tail table row, from the already
kernel-accepted four original parity terms. No new certificate assumption. -/
namespace SubmittedGenus.CapFourMass.Interval

 theorem original_pure_tail_tight :
    pureTailExpression 400 ≤ (3745874303724769 : ℝ) / 1000000000000000 := by
  have he : pureTailExpression 400 = closedReal (TailSyntax.pure 400) :=
    (TailSyntax.pure_real (fun _ => 0) 400).symm
  rw [he, pure_eq_four]
  have h00 := pure_00_le
  have h01 := pure_01_le
  have h10 := pure_10_le
  have h11 := pure_11_le
  linarith

 theorem original_pure_tail_margin :
    pureTailExpression 400 + (231 : ℝ) / 1000000000000000 ≤ pureTailCeiling := by
  have h := original_pure_tail_tight
  unfold pureTailCeiling
  linarith

 theorem original_pure_tail_lt : pureTailExpression 400 < pureTailCeiling := by
  have h := original_pure_tail_margin
  linarith

#print axioms original_pure_tail_tight
#print axioms original_pure_tail_margin
#print axioms original_pure_tail_lt
end SubmittedGenus.CapFourMass.Interval
