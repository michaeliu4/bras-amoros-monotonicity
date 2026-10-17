import Results.Genus.InverseCertificates.Golden

/-! The original mixed-factor scalar majorants and their finite-product inequality.
This file does not identify any particular graph polynomial with a mixed factor. -/
noncomputable section
open scoped BigOperators
namespace SubmittedGenus.InverseCertificates

def u : ℝ := q ^ 2

def mixedA (x : ℝ) (j : ℕ) : ℝ := x^j + x^(j+1) + x^(2*j+1)

def mixedTail (x : ℝ) : ℝ := (1+x)*x^2/(1-x) + x^5/(1-x^2)

lemma u_nonneg : 0 ≤ u := sq_nonneg q

lemma u_upper : u ≤ 191 / 500 := by
  have h := pow_le_pow_left₀ q_nonneg q_upper 2
  norm_num at h
  dsimp [u]
  linarith

lemma u_lt_one : u < 1 := by linarith [u_upper]

lemma mixedA_nonneg {x : ℝ} (hx : 0 ≤ x) (j : ℕ) : 0 ≤ mixedA x j := by
  unfold mixedA
  positivity

lemma mixedA_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (j : ℕ) :
    mixedA x j ≤ mixedA y j :=
  add_le_add (add_le_add (pow_le_pow_left₀ hx hxy j)
    (pow_le_pow_left₀ hx hxy (j+1))) (pow_le_pow_left₀ hx hxy (2*j+1))

lemma mixedA_one_bound : mixedA u 1 < 73 / 125 := by
  have h := mixedA_mono u_nonneg u_upper 1
  norm_num [mixedA] at h ⊢
  linarith

lemma mixedTail_nonneg {x : ℝ} (hx : 0 ≤ x) (hx1 : x < 1) : 0 ≤ mixedTail x := by
  have hx2 : x^2 < 1 := by nlinarith
  unfold mixedTail
  positivity

lemma mixedTail_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y < 1) :
    mixedTail x ≤ mixedTail y := by
  have hy0 : 0 ≤ y := hx.trans hxy
  have hy2 : y^2 < 1 := by nlinarith
  have hp2 := pow_le_pow_left₀ hx hxy 2
  have hp5 := pow_le_pow_left₀ hx hxy 5
  unfold mixedTail
  apply add_le_add
  · apply div_le_div₀ (by positivity)
      (mul_le_mul (by linarith) hp2 (sq_nonneg x) (by positivity))
      (by linarith) (by linarith)
  · exact div_le_div₀ (pow_nonneg hy0 5) hp5 (by linarith) (by linarith)

lemma mixedTail_bound : mixedTail u < 42 / 125 := by
  have h := mixedTail_mono u_nonneg u_upper (show (191 / 500 : ℝ) < 1 by norm_num)
  norm_num [mixedTail] at h ⊢
  linarith

lemma mixedA_one_lt_one : mixedA u 1 < 1 := by linarith [mixedA_one_bound]
lemma mixedTail_lt_one : mixedTail u < 1 := by linarith [mixedTail_bound]

/-- Positive denominator bounds are established before dividing. -/
theorem mixed_norm_scalar : (1+u)*(1+mixedA u 1)/(1-mixedTail u) < 10 / 3 := by
  have hn := mixedA_nonneg u_nonneg 1
  have hT := mixedTail_nonneg u_nonneg u_lt_one
  have hnum : (1+u)*(1+mixedA u 1) ≤ (1+(191/500 : ℝ))*(1+73/125) := by
    exact mul_le_mul (by linarith [u_upper]) (by linarith [mixedA_one_bound])
      (by linarith) (by norm_num)
  apply (div_lt_iff₀ (by linarith [mixedTail_bound])).2
  nlinarith [mixedTail_bound]

/-- The original reciprocal mixed scalar estimate, with all divisor signs proved. -/
theorem mixed_inverse_scalar :
    1 / ((1-u)*(1-mixedA u 1)*(1-mixedTail u)) < 6 := by
  have hu : 0 < 1-u := by linarith [u_upper]
  have ha : 0 < 1-mixedA u 1 := by linarith [mixedA_one_bound]
  have ht : 0 < 1-mixedTail u := by linarith [mixedTail_bound]
  have hmul : ((1-(191/500 : ℝ))*(1-73/125))*(1-42/125) ≤
      (1-u)*(1-mixedA u 1)*(1-mixedTail u) := by
    apply mul_le_mul
    · exact mul_le_mul (by linarith [u_upper]) (by linarith [mixedA_one_bound])
        (by norm_num) hu.le
    · linarith [mixedTail_bound]
    · norm_num
    · exact (mul_pos hu ha).le
  apply (div_lt_iff₀ (mul_pos (mul_pos hu ha) ht)).2
  nlinarith

/-- The tail formula sums all j≥2, rather than bounding a finite fixture. -/
theorem mixed_tail_sum {x : ℝ} (hx : 0 ≤ x) (hx1 : x < 1) :
    Summable (fun n => mixedA x (n+2)) ∧
      (∑' n, mixedA x (n+2)) = mixedTail x := by
  have hxabs : |x| < 1 := by rwa [abs_of_nonneg hx]
  have hx2 : |x^2| < 1 := by rw [abs_of_nonneg (sq_nonneg x)]; nlinarith
  have hs := summable_geometric_of_abs_lt_one hxabs
  have hs2 := summable_geometric_of_abs_lt_one hx2
  have heq : (fun n => mixedA x (n+2)) =
      (fun n => ((1+x)*x^2)*x^n + x^5*(x^2)^n) := by
    funext n
    simp [mixedA, Nat.mul_add, pow_add, pow_mul]
    ring
  rw [heq]
  refine ⟨(hs.mul_left _).add (hs2.mul_left _), ?_⟩
  rw [(hs.mul_left _).tsum_add (hs2.mul_left _), tsum_mul_left, tsum_mul_left,
    tsum_geometric_of_abs_lt_one hxabs, tsum_geometric_of_abs_lt_one hx2]
  simp [mixedTail, div_eq_mul_inv]

/-- The finite product inequality used in the submitted argument. -/
theorem one_sub_sum_le_prod {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (ha1 : ∀ i ∈ s, a i ≤ 1) :
    1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1-a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hai := ha i (Finset.mem_insert_self i s)
    have hai1 := ha1 i (Finset.mem_insert_self i s)
    have has : ∀ j ∈ s, 0 ≤ a j := fun j hj => ha j (Finset.mem_insert_of_mem hj)
    have has1 : ∀ j ∈ s, a j ≤ 1 := fun j hj => ha1 j (Finset.mem_insert_of_mem hj)
    have hsum : 0 ≤ ∑ j ∈ s, a j := Finset.sum_nonneg has
    have hprod := mul_le_mul_of_nonneg_left (ih has has1) (sub_nonneg.mpr hai1)
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    nlinarith [mul_nonneg hai hsum]

/-- Positive-factor products are controlled by the same finite deficit. -/
theorem prod_one_add_le_inverse_deficit {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (ha1 : ∀ i ∈ s, a i ≤ 1)
    (hs : ∑ i ∈ s, a i < 1) :
    (∏ i ∈ s, (1+a i)) ≤ 1 / (1-∑ i ∈ s, a i) := by
  have hplus : 0 ≤ ∏ i ∈ s, (1+a i) :=
    Finset.prod_nonneg (fun i hi => by linarith [ha i hi])
  have hpair : (∏ i ∈ s, (1+a i)) * (∏ i ∈ s, (1-a i)) ≤ 1 := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_le_one
    · intro i hi
      exact mul_nonneg (by linarith [ha i hi]) (by linarith [ha1 i hi])
    · intro i hi
      nlinarith [sq_nonneg (a i)]
  apply (le_div_iff₀ (sub_pos.mpr hs)).2
  exact (mul_le_mul_of_nonneg_left (one_sub_sum_le_prod s a ha ha1) hplus).trans hpair

lemma mixed_tail_finite_sum (s : Finset ℕ) :
    ∑ j ∈ s, mixedA u (j+2) ≤ mixedTail u := by
  obtain ⟨hs, heq⟩ := mixed_tail_sum u_nonneg u_lt_one
  exact heq ▸ hs.sum_le_tsum s (fun j _ => mixedA_nonneg u_nonneg _)

lemma mixed_tail_term_lt_one (j : ℕ) : mixedA u (j+2) < 1 := by
  have h := mixed_tail_finite_sum {j}
  simpa using h.trans_lt mixedTail_lt_one

/-- Every finite set of paired-tail factors obeys the same bound. -/
theorem mixed_tail_product (s : Finset ℕ) :
    (∏ j ∈ s, (1+mixedA u (j+2))) ≤ 1 / (1-mixedTail u) := by
  have hs := mixed_tail_finite_sum s
  have hb := prod_one_add_le_inverse_deficit s (fun j => mixedA u (j+2))
    (fun j _ => mixedA_nonneg u_nonneg _) (fun j _ => (mixed_tail_term_lt_one j).le)
    (hs.trans_lt mixedTail_lt_one)
  exact hb.trans (one_div_le_one_div_of_le (sub_pos.mpr mixedTail_lt_one) (by linarith))

/-- Inverse tail products use the actual positive product denominator. -/
theorem mixed_tail_inverse_product (s : Finset ℕ) :
    (∏ j ∈ s, (1-mixedA u (j+2))⁻¹) ≤ 1 / (1-mixedTail u) := by
  have hs := mixed_tail_finite_sum s
  have hp := one_sub_sum_le_prod s (fun j => mixedA u (j+2))
    (fun j _ => mixedA_nonneg u_nonneg _) (fun j _ => (mixed_tail_term_lt_one j).le)
  rw [Finset.prod_inv_distrib, ← one_div]
  apply one_div_le_one_div_of_le (sub_pos.mpr mixedTail_lt_one)
  linarith

end SubmittedGenus.InverseCertificates
