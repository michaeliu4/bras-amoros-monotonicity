import Results.Genus.CapFourMass.IntervalShortAcceptance
import Results.Genus.CapFourMass.IntervalMixedAcceptance
import Results.Genus.CapFourMass.OriginalPureTailStrict

/-! A non-dyadic decimal upper endpoint cannot equal an integer interval bound.
This derives strict manuscript tail rows from existing accepted certificates,
without rerunning their interval evaluation or assuming a numerical margin. -/
namespace SubmittedGenus.CapFourMass.Interval

 theorem acceptsUpper_strict_of_not_dvd {e : Expr} {n d : ℤ}
    (h : acceptsUpper e n d = true) (hnd : ¬ d ∣ n * unit) :
    closedReal e < (n : ℝ) / (d : ℝ) := by
  unfold acceptsUpper at h
  cases he : closedEval e with
  | none => simp [he] at h
  | some b =>
    simp only [he, decide_eq_true_eq] at h
    have hd : (0 : ℝ) < d := by exact_mod_cast h.1
    have hne : b.hi * d ≠ n * unit := by
      intro eq
      exact hnd ⟨b.hi, by simpa only [mul_comm] using eq.symm⟩
    have hi : (b.hi : ℝ) * (d : ℝ) < (n : ℝ) * (unit : ℝ) := by
      exact_mod_cast lt_of_le_of_ne h.2 hne
    have hh := (closedEval_sound e he).2
    apply (lt_div_iff₀ hd).mpr
    have hm := mul_le_mul_of_nonneg_right hh hd.le
    nlinarith only [hm, hi, unit_pos]

 theorem original_short_tail_lt_of_nondyadic : shortTailExpression 100 < shortTailCeiling := by
  have h := acceptsUpper_strict_of_not_dvd original_short_tail_accepts
    (by norm_num [unit])
  rw [closedReal, TailSyntax.short_real] at h
  simpa only [shortTailCeiling, Int.cast_ofNat] using h

 theorem original_mixed_tail_lt_of_nondyadic : mixedTailExpression 100 < mixedTailCeiling := by
  have h := acceptsUpper_strict_of_not_dvd original_mixed_tail_accepts
    (by norm_num [unit])
  rw [closedReal, TailSyntax.mixed_real] at h
  simpa only [mixedTailCeiling, Int.cast_ofNat] using h

#print axioms acceptsUpper_strict_of_not_dvd
#print axioms original_short_tail_lt_of_nondyadic
#print axioms original_mixed_tail_lt_of_nondyadic
end SubmittedGenus.CapFourMass.Interval
