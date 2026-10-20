import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Tactic

/-!
# The submitted three-evaluation mixed-tail inequality

This is an actual infinite-series comparison. Summability of the original
nonnegative generating function implies summability of the mixed expression;
no subtraction of divergent series or assumed final majorant is used.
-/
noncomputable section
open scoped BigOperators
namespace SubmittedGenus.CapFourMass

/-- The exact retained numerator in the mixed progression denominator. -/
def mixedFactor (J c : ℝ) (d : ℕ) : ℝ :=
  (1-J^d)/((1-J)*(1-c*J^d))

lemma reciprocal_three_bound {c X : ℝ} (hc : 0 ≤ c) (hc1 : c < 1)
    (hX : 0 ≤ X) (hX1 : X ≤ 1) :
    1/(1-c*X) ≤ 1+c*X/(1-c) := by
  have hcX : c*X ≤ c := mul_le_of_le_one_right hc hX1
  have hd1 : 0 < 1-c := sub_pos.mpr hc1
  have hdX : 0 < 1-c*X := by linarith
  apply (div_le_iff₀ hdX).mpr
  have hsmall : 0 ≤ c^2*X*(1-X) := by positivity
  apply (mul_le_mul_iff_left₀ hd1).mp
  field_simp
  nlinarith

lemma mixedFactor_nonneg {J c : ℝ} (hJ : 0 ≤ J) (hJ1 : J < 1)
    (hc : 0 ≤ c) (hc1 : c < 1) (d : ℕ) : 0 ≤ mixedFactor J c d := by
  have hpow : J^d ≤ 1 := pow_le_one₀ hJ hJ1.le
  have hcX : c*J^d ≤ c := mul_le_of_le_one_right hc hpow
  exact div_nonneg (sub_nonneg.mpr hpow)
    (mul_nonneg (sub_pos.mpr hJ1).le (by linarith))

lemma mixedFactor_three {J c : ℝ} (hJ : 0 ≤ J) (hJ1 : J < 1)
    (hc : 0 ≤ c) (hc1 : c < 1) (d : ℕ) :
    mixedFactor J c d ≤
      ((1-J^d)+c/(1-c)*(J^d-(J^2)^d))/(1-J) := by
  have hpow : J^d ≤ 1 := pow_le_one₀ hJ hJ1.le
  have hrec := reciprocal_three_bound hc hc1 (pow_nonneg hJ d) hpow
  have hfac : 0 ≤ (1-J^d)/(1-J) :=
    div_nonneg (sub_nonneg.mpr hpow) (sub_pos.mpr hJ1).le
  have hh := mul_le_mul_of_nonneg_left hrec hfac
  have hden : 1-c ≠ 0 := ne_of_gt (sub_pos.mpr hc1)
  have hJden : 1-J ≠ 0 := ne_of_gt (sub_pos.mpr hJ1)
  have he : ((1-J^d)/(1-J))*(1+c*J^d/(1-c)) =
      ((1-J^d)+c/(1-c)*(J^d-(J^2)^d))/(1-J) := by
    rw [← pow_mul,Nat.mul_comm 2 d,pow_mul,pow_two (J^d)]
    field_simp
    <;> ring
  rw [he] at hh
  simpa only [mixedFactor,div_mul_eq_div_mul_one_div] using hh

lemma mixedFactor_uniform {J c : ℝ} (hJ : 0 ≤ J) (hJ1 : J < 1)
    (hc : 0 ≤ c) (hc1 : c < 1) (d : ℕ) :
    mixedFactor J c d ≤ 1/((1-J)*(1-c)) := by
  have hpow : J^d ≤ 1 := pow_le_one₀ hJ hJ1.le
  have hcX : c*J^d ≤ c := mul_le_of_le_one_right hc hpow
  have hden : 0 < (1-J)*(1-c) := mul_pos (sub_pos.mpr hJ1) (sub_pos.mpr hc1)
  unfold mixedFactor
  apply div_le_div₀ (by norm_num : (0:ℝ) ≤ 1) (by linarith [pow_nonneg hJ d]) hden
  exact mul_le_mul_of_nonneg_left (by linarith) (sub_pos.mpr hJ1).le

/-- Finite form permits arbitrary nonnegative source weights and carry gaps. -/
theorem finite_three_evaluation {ι : Type*} (s : Finset ι) (a : ι → ℝ) (d : ι → ℕ)
    {x J c : ℝ} (ha : ∀ i ∈ s, 0 ≤ a i) (hx : 0 ≤ x)
    (hJ : 0 ≤ J) (hJ1 : J < 1) (hc : 0 ≤ c) (hc1 : c < 1) :
    (∑ i ∈ s, a i*x^(d i)*mixedFactor J c (d i)) ≤
      ((∑ i ∈ s, a i*x^(d i))-(∑ i ∈ s, a i*(x*J)^(d i))+
        c/(1-c)*((∑ i ∈ s, a i*(x*J)^(d i))-
          (∑ i ∈ s, a i*(x*J^2)^(d i))))/(1-J) := by
  calc
    _ ≤ ∑ i ∈ s, a i*x^(d i)*
        (((1-J^(d i))+c/(1-c)*(J^(d i)-(J^2)^(d i)))/(1-J)) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (mixedFactor_three hJ hJ1 hc hc1 (d i))
        (mul_nonneg (ha i hi) (pow_nonneg hx _))
    _ = _ := by
      simp only [mul_pow,Finset.mul_sum,Finset.sum_div,← Finset.sum_add_distrib,
        ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-- The exact infinite version of (mass:three-evaluation), including the
summability conclusion needed before using its numerical evaluations. -/
theorem infinite_three_evaluation {ι : Type*} (a : ι → ℝ) (d : ι → ℕ)
    {x J c : ℝ} (ha : ∀ i, 0 ≤ a i) (hx : 0 ≤ x)
    (hJ : 0 ≤ J) (hJ1 : J < 1) (hc : 0 ≤ c) (hc1 : c < 1)
    (hs : Summable (fun i => a i*x^(d i))) :
    Summable (fun i => a i*x^(d i)*mixedFactor J c (d i)) ∧
    (∑' i, a i*x^(d i)*mixedFactor J c (d i)) ≤
      ((∑' i, a i*x^(d i))-(∑' i, a i*(x*J)^(d i))+
        c/(1-c)*((∑' i, a i*(x*J)^(d i))-
          (∑' i, a i*(x*J^2)^(d i))))/(1-J) := by
  have hJ2 : J^2 ≤ 1 := pow_le_one₀ hJ hJ1.le
  have hfirst : Summable (fun i => a i*(x*J)^(d i)) := by
    apply hs.of_norm_bounded
    intro i
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (ha i)
      (pow_nonneg (mul_nonneg hx hJ) _))]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg hx hJ)
      (mul_le_of_le_one_right hx hJ1.le) _) (ha i)
  have hsecond : Summable (fun i => a i*(x*J^2)^(d i)) := by
    apply hs.of_norm_bounded
    intro i
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (ha i)
      (pow_nonneg (mul_nonneg hx (sq_nonneg _)) _))]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg hx (sq_nonneg _))
      (mul_le_of_le_one_right hx hJ2) _) (ha i)
  have hmix : Summable (fun i => a i*x^(d i)*mixedFactor J c (d i)) := by
    apply (hs.mul_right (1/((1-J)*(1-c)))).of_norm_bounded
    intro i
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (mul_nonneg (ha i) (pow_nonneg hx _))
      (mixedFactor_nonneg hJ hJ1 hc hc1 _))]
    exact mul_le_mul_of_nonneg_left (mixedFactor_uniform hJ hJ1 hc hc1 _)
      (mul_nonneg (ha i) (pow_nonneg hx _))
  refine ⟨hmix, ?_⟩
  have hupper := ((hs.sub hfirst).add ((hfirst.sub hsecond).mul_left (c/(1-c)))).div_const (1-J)
  have he (i : ι) :
      a i*x^(d i)*(((1-J^(d i))+c/(1-c)*(J^(d i)-(J^2)^(d i)))/(1-J)) =
      (a i*x^(d i)-a i*(x*J)^(d i)+
        c/(1-c)*(a i*(x*J)^(d i)-a i*(x*J^2)^(d i)))/(1-J) := by
    simp only [mul_pow]
    ring
  have hpoint (i : ι) : a i*x^(d i)*mixedFactor J c (d i) ≤
      (a i*x^(d i)-a i*(x*J)^(d i)+
        c/(1-c)*(a i*(x*J)^(d i)-a i*(x*J^2)^(d i)))/(1-J) := by
    rw [← he]
    exact mul_le_mul_of_nonneg_left (mixedFactor_three hJ hJ1 hc hc1 _)
      (mul_nonneg (ha i) (pow_nonneg hx _))
  have hh := hmix.tsum_le_tsum hpoint hupper
  simpa only [tsum_div_const,Summable.tsum_add (hs.sub hfirst) ((hfirst.sub hsecond).mul_left _),
    Summable.tsum_sub hs hfirst,tsum_mul_left,Summable.tsum_sub hfirst hsecond] using hh

end SubmittedGenus.CapFourMass
