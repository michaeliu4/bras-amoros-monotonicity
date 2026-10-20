import Results.Genus.CapFourMass.TailExpressions

/-! The omitted-pivot rational functions are the actual original pivot coefficient series. -/
noncomputable section
open scoped BigOperators
namespace SubmittedGenus.CapFourMass

def TailIndex.pivot (i : TailIndex) : ParityPivot := ⟨i.1.1,i.1.2,i.2.1,i.2.2⟩
def TailIndex.gap (i : TailIndex) : ℕ := i.pivot.p-i.pivot.r

def omittedPivotCoefficient (P : ℕ) (i : TailIndex) : ℝ :=
  if P < i.pivot.p then
    lambdaBound^(2*i.pivot.p)*eta^(i.pivot.a+i.pivot.b)*sigma^(i.pivot.b-i.pivot.r)
  else 0

lemma omittedPivotCoefficient_nonneg (P : ℕ) (i : TailIndex) :
    0 ≤ omittedPivotCoefficient P i := by
  unfold omittedPivotCoefficient
  split_ifs
  · exact mul_nonneg (mul_nonneg (pow_nonneg lambdaBound_pos.le _) (pow_nonneg eta_bounds.1.le _))
      (pow_nonneg sigma_bounds.1.le _)
  · rfl

lemma parity_gap_power (q : ParityPivot) {x : ℝ} (hx : 0<x) :
    x^(q.p-q.r)=x^((q.v.val:ℤ)-(q.u.val:ℤ))*x^(2*q.b)/x^(2*q.a) := by
  have hg : ((q.p-q.r:ℕ):ℤ)=(q.v.val:ℤ)-(q.u.val:ℤ)+((2*q.b:ℕ):ℤ)-((2*q.a:ℕ):ℤ) := by
    have hh:=q.toPivot.property.2
    change q.r<q.p at hh
    dsimp [ParityPivot.p,ParityPivot.r] at *
    omega
  rw [← zpow_natCast x (q.p-q.r),hg,zpow_sub₀ (ne_of_gt hx),zpow_add₀ (ne_of_gt hx)]
  simp only [zpow_natCast]

lemma parity_mixed_power (q : ParityPivot) {x : ℝ} (hx : 0<x) :
    lambdaBound^(2*(q.v.val+1))*x^((q.v.val:ℤ)-(q.u.val:ℤ))*
      (mixedA x)^q.a*(mixedB x)^q.b =
      lambdaBound^(2*q.p)*eta^(q.a+q.b)*x^(q.p-q.r) := by
  rw [parity_gap_power q hx]
  have hp : 2*q.p=2*(q.v.val+1)+4*q.b := by dsimp [ParityPivot.p]; ring
  rw [hp,pow_add,pow_add]
  simp only [mixedA,mixedB,div_pow,mul_pow,← pow_mul]
  ring

/-- Exact source coefficient identity asserted immediately after (mass:G). -/
theorem GtailTerm_eq_pivot (P : ℕ) {x : ℝ} (hx : 0<x) (i : TailIndex) :
    GtailTerm P x i=omittedPivotCoefficient P i*x^(i.gap) := by
  have hpow:=parity_mixed_power i.pivot hx
  unfold GtailTerm omittedParityTerm omittedPivotCoefficient
  change lambdaBound^(2*(i.pivot.v.val+1))*x^((i.pivot.v.val:ℤ)-(i.pivot.u.val:ℤ))*
    (if P < i.pivot.p then parityTerm (mixedA x) (mixedB x) sigma (i.pivot.u.val+1)
      (parityOffset i.pivot.u i.pivot.v) i.pivot.a i.pivot.j else 0)=_
  by_cases hp : P < i.pivot.p
  · rw [if_pos hp,if_pos hp]
    change lambdaBound^(2*(i.pivot.v.val+1))*x^((i.pivot.v.val:ℤ)-(i.pivot.u.val:ℤ))*
      ((mixedA x)^i.pivot.a*(mixedB x)^i.pivot.b*sigma^(i.pivot.b-i.pivot.r))=_
    calc
      _ = (lambdaBound^(2*(i.pivot.v.val+1))*x^((i.pivot.v.val:ℤ)-(i.pivot.u.val:ℤ))*
        (mixedA x)^i.pivot.a*(mixedB x)^i.pivot.b)*sigma^(i.pivot.b-i.pivot.r) := by ring
      _ = _ := by rw [hpow]; dsimp only [TailIndex.gap]; ring
  · simp only [if_neg hp,mul_zero,zero_mul]

/-- Each rational evaluation is the convergent original coefficient generating series. -/
theorem Gtail_pivot_hasSum (P : ℕ) {x : ℝ} (hx : 0<x)
    (hconv : convergenceDomain (mixedA x) (mixedB x)) :
    HasSum (fun i : TailIndex => omittedPivotCoefficient P i*x^i.gap) (Gtail P x) := by
  have he : GtailTerm P x=(fun i : TailIndex => omittedPivotCoefficient P i*x^i.gap) :=
    funext (GtailTerm_eq_pivot P hx)
  rw [← he]
  exact Gtail_hasSum P hx hconv

/-- The original mixed omitted-pivot inequality, including convergence of the
series being bounded and all three actual rational evaluations. -/
theorem mixed_omitted_pivot_sum (P : ℕ) :
    Summable (fun i : TailIndex => omittedPivotCoefficient P i*tBound^i.gap*
      mixedFactor mixedJ negativeSquare i.gap) ∧
    mixedTailConstant*(∑' i : TailIndex,omittedPivotCoefficient P i*tBound^i.gap*
      mixedFactor mixedJ negativeSquare i.gap) ≤ mixedTailExpression P := by
  have ht : 0<tBound := lt_trans zero_lt_one tBound_gt_one
  have h0:=Gtail_pivot_hasSum P ht mixed_convergence_zero
  have h1:=Gtail_pivot_hasSum P (mul_pos ht mixedJ_bounds.1) mixed_convergence_one
  have h2:=Gtail_pivot_hasSum P (mul_pos ht (pow_pos mixedJ_bounds.1 2)) mixed_convergence_two
  have hh:=infinite_three_evaluation (omittedPivotCoefficient P) TailIndex.gap
    (omittedPivotCoefficient_nonneg P) ht.le mixedJ_bounds.1.le mixedJ_bounds.2
    negativeSquare_bounds.1.le negativeSquare_bounds.2 h0.summable
  refine ⟨hh.1,?_⟩
  have hC : 0≤mixedTailConstant := by
    unfold mixedTailConstant
    have hT : 0≤feedbackT := div_nonneg feedbackGamma_bounds.1.le feedbackBeta_bounds.1.le
    exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg radius_pos.le _)
      (le_of_lt (lt_trans zero_lt_one alphabetMass_gt_one))) (by linarith [lambdaBound_pos])) hT)
      (mul_nonneg (sq_nonneg _) eta_bounds.1.le)
  have h:=mul_le_mul_of_nonneg_left hh.2 hC
  rw [h0.tsum_eq,h1.tsum_eq,h2.tsum_eq] at h
  exact h.trans_eq (by unfold mixedTailExpression; ring)

end SubmittedGenus.CapFourMass
