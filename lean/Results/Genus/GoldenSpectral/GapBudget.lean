import Results.Genus.GoldenSpectral.RunCharges

/-! Original scalar conversion from a proved paid-run count to χ^(d−16).
The integer exponent retains the submitted meaning even for small gaps. -/
noncomputable section
namespace SubmittedGenus.GoldenSpectral
lemma gapDecay_pos : 0<gapDecay := by norm_num [gapDecay]
lemma gapDecay_lt_one : gapDecay<1 := by norm_num [gapDecay]

lemma paidCost_pow_le_gap (j : ℕ) : paidCost^j ≤ gapDecay^(2*j) := by
  have h:=pow_le_pow_left₀ paidCost_pos.le paidCost_lt_gap.le j
  simpa only [←pow_mul] using h

/-- The natural truncated exponent is a useful stronger bound for d<16. -/
theorem paid_count_gap_bound (d j : ℕ) (hcount : d ≤ 2*j+16) :
    paidCost^j ≤ gapDecay^(d-16) :=
  (paidCost_pow_le_gap j).trans
    (pow_le_pow_of_le_one gapDecay_pos.le gapDecay_lt_one.le (by omega))

/-- Exact original exponent, with no implicit d≥16 assumption. -/
theorem paid_count_original_gap_bound (d j : ℕ) (hcount : d ≤ 2*j+16) :
    paidCost^j ≤ gapDecay^((d:ℤ)-16) := by
  have he : (d:ℤ)-16 ≤ ((2*j:ℕ):ℤ) := by omega
  have hh:=zpow_le_zpow_right_of_le_one₀ gapDecay_pos gapDecay_lt_one.le he
  rw [zpow_natCast] at hh
  exact (paidCost_pow_le_gap j).trans hh

end SubmittedGenus.GoldenSpectral
