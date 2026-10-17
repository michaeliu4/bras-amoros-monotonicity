import Results.Genus.GoldenTail.FiniteBound

/-! Absolute convergence of the original nonnegative omitted-pivot majorant. -/
namespace SubmittedGenus.GoldenTail
open scoped BigOperators
noncomputable section

def omittedMultiplierRow (p : ℕ) : ℝ :=
  if 300<p then ∑ r ∈ Finset.Ico 1 p,coefficientMultiplier r p else 0

lemma omittedMultiplierRow_nonneg (p : ℕ) : 0≤omittedMultiplierRow p := by
  unfold omittedMultiplierRow
  split_ifs
  · exact Finset.sum_nonneg (fun r _ => coefficientMultiplier_nonneg r p)
  · rfl

lemma omittedMultiplierRow_sum_range (N : ℕ) :
    (∑ p ∈ Finset.range N,omittedMultiplierRow p)=
      ∑ p ∈ Finset.Ico 301 N,∑ r ∈ Finset.Ico 1 p,coefficientMultiplier r p := by
  unfold omittedMultiplierRow
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext p
    simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_Ico]
    omega
  · intro p _; rfl

/-- The complete original omitted-pivot multiplier is genuinely summable. -/
theorem omittedMultiplierRow_summable : Summable omittedMultiplierRow := by
  apply summable_of_sum_range_le omittedMultiplierRow_nonneg
  intro N
  rw [omittedMultiplierRow_sum_range]
  exact omitted_multiplier_sum_le N

/-- The same literal rational ceiling bounds the whole convergent sum. -/
theorem omittedMultiplierRow_tsum_le :
    (∑' p,omittedMultiplierRow p)≤(221715 : ℝ)/1000000 := by
  apply omittedMultiplierRow_summable.tsum_le_of_sum_range_le
  intro N
  rw [omittedMultiplierRow_sum_range]
  exact omitted_multiplier_sum_le N

/-- Absolute convergence is obtained without changing any signed source
contraction: only its proved nonnegative coefficient majorant is summed. -/
theorem omittedMultiplierRow_abs_summable : Summable (fun p => |omittedMultiplierRow p|) := by
  simpa only [abs_of_nonneg (omittedMultiplierRow_nonneg _)] using omittedMultiplierRow_summable

end
end SubmittedGenus.GoldenTail
