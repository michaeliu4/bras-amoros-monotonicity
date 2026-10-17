import Results.Genus.TailComparison.Scalar
import Mathlib.NumberTheory.Real.GoldenRatio

/-!
# Binet bridge for the submitted genus comparison

The residual and capacity hypotheses below are deliberately explicit. Binet's
formula is the existing mathlib theorem for `Nat.fib`; no replacement sequence
or unverified asymptotic estimate is assumed.
-/
noncomputable section
namespace SubmittedGenus.TailComparison

lemma inverse_goldenRatio_lt_qbar : Real.goldenRatio⁻¹ < qbar := by
  have hid : Real.goldenRatio⁻¹ ^ 2 + Real.goldenRatio⁻¹ = 1 := by
    rw [Real.inv_goldenRatio]
    nlinarith [Real.goldenConj_sq]
  have hrat : 1 < qbar ^ 2 + qbar := by norm_num [qbar]
  by_contra h
  have hle : qbar ≤ Real.goldenRatio⁻¹ := le_of_not_gt h
  have hsq := pow_le_pow_left₀ qbar_pos.le hle 2
  linarith

lemma sqrt_five_lt_sStar : Real.sqrt 5 < sStar := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have hn := Real.sqrt_nonneg (5 : ℝ)
  have hr : 5 < sStar ^ 2 := by norm_num [sStar]
  nlinarith [sStar_pos]

lemma one_lt_goldenRatio_mul_qbar : 1 < Real.goldenRatio * qbar := by
  calc
    1 = Real.goldenRatio * Real.goldenRatio⁻¹ :=
      (mul_inv_cancel₀ Real.goldenRatio_ne_zero).symm
    _ < Real.goldenRatio * qbar :=
      mul_lt_mul_of_pos_left inverse_goldenRatio_lt_qbar Real.goldenRatio_pos

lemma goldenConj_pow_le_qbar_pow (g : ℕ) : Real.goldenConj ^ g ≤ qbar ^ g := by
  calc
    Real.goldenConj ^ g ≤ |Real.goldenConj ^ g| := le_abs_self _
    _ = Real.goldenRatio⁻¹ ^ g := by
      rw [abs_pow, abs_of_neg Real.goldenConj_neg, ← Real.inv_goldenRatio]
    _ ≤ qbar ^ g := pow_le_pow_left₀ (inv_pos.mpr Real.goldenRatio_pos).le
      inverse_goldenRatio_lt_qbar.le g

/-- The submitted parity-uniform lower denominator, proved using Binet's formula. -/
theorem fibonacci_lower_bound (g : ℕ) :
    (1 - qbar ^ (2 * g)) / (sStar * qbar ^ g) ≤ (Nat.fib g : ℝ) := by
  have hsq : Real.sqrt (5 : ℝ) ≠ 0 := by positivity
  have hbinet : (Nat.fib g : ℝ) * Real.sqrt 5 =
      Real.goldenRatio ^ g - Real.goldenConj ^ g :=
    (eq_div_iff hsq).mp (Real.coe_fib_eq g)
  have hphi : 1 ≤ Real.goldenRatio ^ g * qbar ^ g := by
    rw [← mul_pow]
    exact one_le_pow₀ one_lt_goldenRatio_mul_qbar.le
  have hpsi := mul_le_mul_of_nonneg_right (goldenConj_pow_le_qbar_pow g)
    (pow_nonneg qbar_pos.le g)
  have hqpow : qbar ^ (2 * g) = qbar ^ g * qbar ^ g := by rw [two_mul, pow_add]
  apply (div_le_iff₀ (mul_pos sStar_pos (pow_pos qbar_pos g))).mpr
  calc
    1 - qbar ^ (2 * g) ≤
        ((Nat.fib g : ℝ) * Real.sqrt 5) * qbar ^ g := by
      rw [hbinet, hqpow, sub_mul]
      linarith
    _ ≤ ((Nat.fib g : ℝ) * sStar) * qbar ^ g := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left sqrt_five_lt_sStar.le (Nat.cast_nonneg _))
        (pow_nonneg qbar_pos.le _)
    _ = (Nat.fib g : ℝ) * (sStar * qbar ^ g) := mul_assoc _ _ _

lemma fibonacci_pos {g : ℕ} (hg : 0 < g) : 0 < (Nat.fib g : ℝ) := by
  exact_mod_cast Nat.fib_pos.mpr hg

lemma residualMajorant_pos (g : ℕ) : 0 < residualMajorant g := by
  unfold residualMajorant
  exact add_pos (div_pos (by norm_num) (pow_pos z4_pos _))
    (div_pos (by norm_num) (pow_pos z5_pos _))

/-- The submitted residual-mass estimate implies its exact Binet ratio majorant. -/
theorem residual_ratio_lt_xi {g : ℕ} (hg : 0 < g) {E : ℝ}
    (hresidual : E < residualMajorant g) : E / (Nat.fib g : ℝ) < xi g := by
  have hlower : 0 < (1 - qbar ^ (2 * g)) / (sStar * qbar ^ g) :=
    div_pos (denominator_pos hg) (mul_pos sStar_pos (pow_pos qbar_pos _))
  calc
    E / (Nat.fib g : ℝ) < residualMajorant g / (Nat.fib g : ℝ) :=
      div_lt_div_of_pos_right hresidual (fibonacci_pos hg)
    _ ≤ residualMajorant g / ((1 - qbar ^ (2 * g)) / (sStar * qbar ^ g)) :=
      div_le_div_of_nonneg_left (residualMajorant_pos g).le hlower (fibonacci_lower_bound g)
    _ = xi g := by
      unfold residualMajorant xi
      rw [div_pow, div_pow]
      field_simp

/-- Proposition `mass:tail`, retaining precisely its two earlier analytic hypotheses. -/
theorem mass_tail {g : ℕ} (hg : 837 ≤ g) {E L : ℝ}
    (hresidual : E < 2024 / z4 ^ g + 113 / z5 ^ g)
    (hcapacity : 1 - 50 * rStar ^ 2 / ((63 / 100) * rStar) ^ g + 927 / 500 ≤
      L / (Nat.fib g : ℝ)) : E < L := by
  have hgpos : 0 < g := by omega
  have hC : capacityRatio g ≤ L / (Nat.fib g : ℝ) := by
    unfold capacityRatio
    linarith
  have hr : E / (Nat.fib g : ℝ) < L / (Nat.fib g : ℝ) :=
    (residual_ratio_lt_xi hgpos hresidual).trans_le ((xi_lt_capacityRatio hg).le.trans hC)
  exact (div_lt_div_iff_of_pos_right (fibonacci_pos hgpos)).mp hr

/-- Natural-cardinality specialization: the population and capacity estimates
remain named hypotheses, and the conclusion is a strict comparison of counts. -/
theorem mass_tail_counts {g E L : ℕ} (hg : 837 ≤ g)
    (hresidual : (E : ℝ) < 2024 / z4 ^ g + 113 / z5 ^ g)
    (hcapacity : 1 - 50 * rStar ^ 2 / ((63 / 100) * rStar) ^ g + 927 / 500 ≤
      (L : ℝ) / (Nat.fib g : ℝ)) : E < L := by
  exact_mod_cast mass_tail hg hresidual hcapacity

end SubmittedGenus.TailComparison
