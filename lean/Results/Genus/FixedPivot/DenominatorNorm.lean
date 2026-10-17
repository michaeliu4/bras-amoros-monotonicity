import Results.Genus.FixedPivot.MixedNorm
import Results.Genus.FixedPivot.PolynomialInverse

/-! Complete norms for the original mixed denominator, with all reciprocal tails. -/
noncomputable section
namespace SubmittedGenus.FixedPivot
open scoped BigOperators
open InverseCertificates WeightedSeries
local notation "Xr" => (Polynomial.X : Polynomial ℝ)

lemma mixedA_lt_one {j : ℕ} (hj : 1 ≤ j) : mixedA u j < 1 := by
  by_cases h1 : j=1
  · simpa [h1] using mixedA_one_lt_one
  · have he : j=j-2+2 := by omega
    rw [he]
    exact mixed_tail_term_lt_one _

lemma mixedPair_constant {d j : ℕ} (hd : 0 < d) (hj : 0 < j) :
    (mixedPair Xr d j).coeff 0=1 := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  simp [mixedPair,carryC,zero_pow (Nat.ne_of_gt hd),zero_pow (Nat.ne_of_gt hj)]

/-- Each original paired reciprocal is absolutely summable, including its tail. -/
theorem mixedPair_inverse_norm {d j : ℕ} (hj0 : 1 ≤ j) (hj : 2*j+1 ≤ d) :
    PolynomialInverseSummable q (mixedPair Xr d j) ∧
      polynomialInverseNorm q (mixedPair Xr d j) ≤ (1-mixedA u j)⁻¹ := by
  have hc := mixedPair_constant (d := d) (j := j) (by omega) (by omega)
  simpa only [one_div] using polynomial_inverse_of_residual q_nonneg (mixedPair Xr d j)
    (by rw [hc]; norm_num) (mixedPair_residual_le_a d j hj) (mixedA_lt_one hj0)

lemma central_constant {k : ℕ} (hk : 1 ≤ k) : (1-(carryC Xr)^k).coeff 0=1 := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  simp [carryC,zero_pow (show k≠0 by omega)]

lemma central_residual_norm {k : ℕ} (hk : 1 ≤ k) :
    polynomialNorm q (1-(1-(carryC Xr)^k)) ≤ u := by
  rw [show 1-(1-(carryC Xr)^k)=(carryC Xr)^k by ring]
  exact (carryC_pow_norm_le k).trans (by
    simpa using pow_le_pow_of_le_one u_nonneg u_lt_one.le hk)

lemma central_norm {k : ℕ} (hk : 1 ≤ k) : polynomialNorm q (1-(carryC Xr)^k) ≤ 1+u := by
  have hh : polynomialNorm q ((carryC Xr)^k) ≤ u :=
    (carryC_pow_norm_le k).trans (by
      simpa using pow_le_pow_of_le_one u_nonneg u_lt_one.le hk)
  exact (polynomialNorm_sub_le q_nonneg 1 _).trans (by
    rw [polynomialNorm_one]
    exact add_le_add le_rfl hh)

lemma central_inverse_norm {k : ℕ} (hk : 1 ≤ k) :
    PolynomialInverseSummable q (1-(carryC Xr)^k) ∧
      polynomialInverseNorm q (1-(carryC Xr)^k) ≤ (1-u)⁻¹ := by
  simpa only [one_div] using polynomial_inverse_of_residual q_nonneg (1-(carryC Xr)^k)
    (by rw [central_constant hk]; norm_num) (central_residual_norm hk) u_lt_one

/-- Uniform product estimate over every initial segment j=1,...,n. -/
lemma all_mixed_majorant_product (n : ℕ) :
    (∏ j ∈ Finset.range n, (1+mixedA u (j+1))) ≤
      (1+mixedA u 1)/(1-mixedTail u) := by
  cases n with
  | zero =>
    simp only [Finset.range_zero,Finset.prod_empty]
    apply (le_div_iff₀ (sub_pos.mpr mixedTail_lt_one)).2
    have ha := mixedA_nonneg u_nonneg 1
    have ht := mixedTail_nonneg u_nonneg u_lt_one
    nlinarith
  | succ n =>
    rw [show n+1=1+n by omega,Finset.prod_range_add]
    simp only [Finset.prod_range_one,Nat.zero_add]
    have hh : (∏ j ∈ Finset.range n, (1+mixedA u (1+j+1))) ≤ 1/(1-mixedTail u) := by
      simpa only [show ∀ j : ℕ, 1+j+1=j+2 by omega] using mixed_tail_product (Finset.range n)
    calc
      _ ≤ (1+mixedA u 1)*(1/(1-mixedTail u)) :=
        mul_le_mul_of_nonneg_left hh (by linarith [mixedA_nonneg u_nonneg 1])
      _ = _ := by ring

lemma all_mixed_majorant_inverse_product (n : ℕ) :
    (∏ j ∈ Finset.range n, (1-mixedA u (j+1))⁻¹) ≤
      1/((1-mixedA u 1)*(1-mixedTail u)) := by
  cases n with
  | zero =>
    simp only [Finset.range_zero,Finset.prod_empty]
    have ha := mixedA_nonneg u_nonneg 1
    have ht := mixedTail_nonneg u_nonneg u_lt_one
    have hp : 0 < (1-mixedA u 1)*(1-mixedTail u) :=
      mul_pos (sub_pos.mpr mixedA_one_lt_one) (sub_pos.mpr mixedTail_lt_one)
    apply (le_div_iff₀ hp).2
    nlinarith [mul_nonneg ha (sub_nonneg.mpr mixedTail_lt_one.le)]
  | succ n =>
    rw [show n+1=1+n by omega,Finset.prod_range_add]
    simp only [Finset.prod_range_one,Nat.zero_add]
    have hh : (∏ j ∈ Finset.range n, (1-mixedA u (1+j+1))⁻¹) ≤ 1/(1-mixedTail u) := by
      simpa only [show ∀ j : ℕ, 1+j+1=j+2 by omega] using mixed_tail_inverse_product (Finset.range n)
    calc
      _ ≤ (1-mixedA u 1)⁻¹*(1/(1-mixedTail u)) :=
        mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr (sub_nonneg.mpr mixedA_one_lt_one.le))
      _ = _ := by simp [div_eq_mul_inv,mul_inv_rev]; ring

/-- The optional central factor in the original R_d. -/
def centralDenominator (d : ℕ) : Polynomial ℝ :=
  if Even d then 1-(carryC Xr)^(d/2) else 1

lemma centralDenominator_norm {d : ℕ} (hd : 0 < d) :
    polynomialNorm q (centralDenominator d) ≤ 1+u := by
  unfold centralDenominator
  split_ifs with he
  · apply central_norm
    have hmod := Nat.even_iff.mp he
    omega
  · rw [polynomialNorm_one]
    linarith [u_nonneg]

lemma centralDenominator_inverse {d : ℕ} (hd : 0 < d) :
    PolynomialInverseSummable q (centralDenominator d) ∧
      polynomialInverseNorm q (centralDenominator d) ≤ (1-u)⁻¹ := by
  unfold centralDenominator
  split_ifs with he
  · apply central_inverse_norm
    have hmod := Nat.even_iff.mp he
    omega
  · refine ⟨polynomialInverseSummable_one q, ?_⟩
    rw [polynomialInverseNorm_one,← one_div]
    apply (le_div_iff₀ (sub_pos.mpr u_lt_one)).2
    linarith [u_nonneg]

lemma paired_range_bound {d j : ℕ} (hj : j ∈ Finset.range ((d-1)/2)) :
    2*(j+1)+1 ≤ d := by
  have h := Finset.mem_range.mp hj
  omega

lemma mixedDenominator_eq_parts (d : ℕ) :
    mixedDenominator Xr d =
      (∏ j ∈ Finset.range ((d-1)/2), mixedPair Xr d (j+1))*centralDenominator d := rfl

/-- The full mixed denominator has the exact original uniform bound10/3. -/
theorem mixedDenominator_norm {d : ℕ} (hd : 0 < d) :
    polynomialNorm q (mixedDenominator Xr d) < 10/3 := by
  let n := (d-1)/2
  have hp : polynomialNorm q (∏ j ∈ Finset.range n, mixedPair Xr d (j+1)) ≤
      (1+mixedA u 1)/(1-mixedTail u) := by
    calc
      _ ≤ ∏ j ∈ Finset.range n, polynomialNorm q (mixedPair Xr d (j+1)) :=
        polynomialNorm_prod_le q_nonneg _ _
      _ ≤ ∏ j ∈ Finset.range n, (1+mixedA u (j+1)) := by
        apply Finset.prod_le_prod
        · intro j _
          exact polynomialNorm_nonneg q_nonneg _
        · intro j hj
          exact mixedPair_norm_le _ _ (paired_range_bound hj)
      _ ≤ _ := all_mixed_majorant_product n
  rw [mixedDenominator_eq_parts]
  calc
    _ ≤ polynomialNorm q (∏ j ∈ Finset.range n, mixedPair Xr d (j+1))*
        polynomialNorm q (centralDenominator d) := polynomialNorm_mul_le q_nonneg _ _
    _ ≤ ((1+mixedA u 1)/(1-mixedTail u))*(1+u) :=
      mul_le_mul hp (centralDenominator_norm hd) (polynomialNorm_nonneg q_nonneg _)
        (by have ha := mixedA_nonneg u_nonneg 1; have ht := sub_pos.mpr mixedTail_lt_one; positivity)
    _ = (1+u)*(1+mixedA u 1)/(1-mixedTail u) := by ring
    _ < 10/3 := mixed_norm_scalar

/-- Full inverse bound6 includes all infinitely many reciprocal coefficients. -/
theorem mixedDenominator_inverse_norm {d : ℕ} (hd : 0 < d) :
    PolynomialInverseSummable q (mixedDenominator Xr d) ∧
      polynomialInverseNorm q (mixedDenominator Xr d) < 6 := by
  let n := (d-1)/2
  have hs : ∀ j ∈ Finset.range n, PolynomialInverseSummable q (mixedPair Xr d (j+1)) := by
    intro j hj
    exact (mixedPair_inverse_norm (by omega) (paired_range_bound hj)).1
  have hprod := PolynomialInverseSummable.prod q_nonneg (Finset.range n) _ hs
  have hcenter := centralDenominator_inverse hd
  have hp : polynomialInverseNorm q (∏ j ∈ Finset.range n, mixedPair Xr d (j+1)) ≤
      1/((1-mixedA u 1)*(1-mixedTail u)) := by
    calc
      _ ≤ ∏ j ∈ Finset.range n, polynomialInverseNorm q (mixedPair Xr d (j+1)) :=
        polynomialInverseNorm_prod_le q_nonneg _ _ hs
      _ ≤ ∏ j ∈ Finset.range n, (1-mixedA u (j+1))⁻¹ := by
        apply Finset.prod_le_prod
        · intro j _
          exact polynomialInverseNorm_nonneg q_nonneg _
        · intro j hj
          exact (mixedPair_inverse_norm (by omega) (paired_range_bound hj)).2
      _ ≤ _ := all_mixed_majorant_inverse_product n
  rw [mixedDenominator_eq_parts]
  refine ⟨hprod.mul q_nonneg hcenter.1, ?_⟩
  calc
    _ ≤ polynomialInverseNorm q (∏ j ∈ Finset.range n, mixedPair Xr d (j+1))*
        polynomialInverseNorm q (centralDenominator d) :=
      polynomialInverseNorm_mul_le q_nonneg hprod hcenter.1
    _ ≤ (1/((1-mixedA u 1)*(1-mixedTail u)))*(1-u)⁻¹ :=
      mul_le_mul hp hcenter.2 (polynomialInverseNorm_nonneg q_nonneg _)
        (by have ha:=sub_pos.mpr mixedA_one_lt_one; have ht:=sub_pos.mpr mixedTail_lt_one; positivity)
    _ = 1/((1-u)*(1-mixedA u 1)*(1-mixedTail u)) := by
      simp [div_eq_mul_inv,mul_inv_rev]
      ring
    _ < 6 := mixed_inverse_scalar

end SubmittedGenus.FixedPivot
