import Mathlib.Tactic

/-!
# The original submitted paper's scalar comparison at genus 837

Source: `submitted-manuscript-e04fb276.tex`, proposition `mass:tail`, lines 2362–2412.
All numerical constants and the joining genus are those of the submitted paper.
The endpoint computations below are kernel-checked rational arithmetic. The final
application explicitly takes the manuscript's residual-mass and unused-capacity
estimates as hypotheses: this file does not claim their combinatorial derivation.
-/

noncomputable section
namespace SubmittedGenus.TailComparison

/-- The submitted upper approximation to the inverse golden ratio. -/
def qbar : ℝ := 309017 / 500000
/-- The submitted upper approximation to the square root of five. -/
def sStar : ℝ := 223607 / 100000
/-- The submitted lower approximation to the golden ratio in the capacity bound. -/
def rStar : ℝ := 809 / 500
/-- Radius for the depth-four residual population. -/
def z4 : ℝ := 1247 / 2000
/-- Radius for the unique-five residual population. -/
def z5 : ℝ := 633 / 1000

def xi (g : ℕ) : ℝ :=
  sStar * (2024 * (qbar / z4) ^ g + 113 * (qbar / z5) ^ g) /
    (1 - qbar ^ (2 * g))

def capacityRatio (g : ℕ) : ℝ :=
  1 + 927 / 500 - 50 * rStar ^ 2 / ((63 / 100) * rStar) ^ g

def residualMajorant (g : ℕ) : ℝ := 2024 / z4 ^ g + 113 / z5 ^ g

lemma qbar_pos : 0 < qbar := by norm_num [qbar]
lemma qbar_lt_one : qbar < 1 := by norm_num [qbar]
lemma sStar_pos : 0 < sStar := by norm_num [sStar]
lemma z4_pos : 0 < z4 := by norm_num [z4]
lemma z5_pos : 0 < z5 := by norm_num [z5]
lemma qbar_lt_z4 : qbar < z4 := by norm_num [qbar, z4]
lemma qbar_lt_z5 : qbar < z5 := by norm_num [qbar, z5]
lemma capacity_base_gt_one : 1 < (63 / 100 : ℝ) * rStar := by norm_num [rStar]

lemma denominator_pos {g : ℕ} (hg : 0 < g) : 0 < 1 - qbar ^ (2 * g) := by
  apply sub_pos.mpr
  exact pow_lt_one₀ qbar_pos.le qbar_lt_one (by omega)

lemma xi_nonneg (g : ℕ) : 0 ≤
    sStar * (2024 * (qbar / z4) ^ g + 113 * (qbar / z5) ^ g) := by
  unfold sStar qbar z4 z5
  positivity

/-- Increasing genus only lowers the submitted residual ratio majorant. -/
theorem xi_antitone {g h : ℕ} (hg : 0 < g) (hgh : g ≤ h) : xi h ≤ xi g := by
  have h4 : (qbar / z4) ^ h ≤ (qbar / z4) ^ g :=
    pow_le_pow_of_le_one (div_nonneg qbar_pos.le z4_pos.le)
      (le_of_lt ((div_lt_one z4_pos).mpr qbar_lt_z4)) hgh
  have h5 : (qbar / z5) ^ h ≤ (qbar / z5) ^ g :=
    pow_le_pow_of_le_one (div_nonneg qbar_pos.le z5_pos.le)
      (le_of_lt ((div_lt_one z5_pos).mpr qbar_lt_z5)) hgh
  have hq : qbar ^ (2 * h) ≤ qbar ^ (2 * g) :=
    pow_le_pow_of_le_one qbar_pos.le qbar_lt_one.le (by omega)
  unfold xi
  apply div_le_div₀ (xi_nonneg g) _ (denominator_pos hg) (by linarith)
  exact mul_le_mul_of_nonneg_left (by linarith) sStar_pos.le

/-- Increasing genus only raises the submitted capacity ratio minorant. -/
theorem capacityRatio_monotone {g h : ℕ} (hgh : g ≤ h) :
    capacityRatio g ≤ capacityRatio h := by
  have hp := pow_le_pow_right₀ capacity_base_gt_one.le hgh
  have hb : 0 < ((63 / 100 : ℝ) * rStar) ^ g :=
    pow_pos (lt_trans (by norm_num) capacity_base_gt_one) _
  have he := div_le_div_of_nonneg_left (show 0 ≤ 50 * rStar ^ 2 by positivity) hb hp
  unfold capacityRatio
  linarith

-- `norm_num` constructs proof terms; no native evaluation is admitted as evidence.
set_option exponentiation.threshold 2000 in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- Exact first endpoint of the submitted decimal chain. -/
theorem xi_837_lt : xi 837 < 2850575297189 / 1000000000000 := by
  norm_num [xi, qbar, sStar, z4, z5]

/-- The two displayed decimals are exact rationals. -/
theorem joining_decimals_lt :
    (2850575297189 / 1000000000000 : ℝ) < 2853985748250 / 1000000000000 := by
  norm_num

set_option exponentiation.threshold 2000 in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- Exact final endpoint of the submitted decimal chain. -/
theorem joining_decimal_lt_capacity_837 :
    (2853985748250 / 1000000000000 : ℝ) < capacityRatio 837 := by
  norm_num [capacityRatio, rStar]

/-- The original scalar comparison, continued from precisely genus 837. -/
theorem xi_lt_capacityRatio {g : ℕ} (hg : 837 ≤ g) : xi g < capacityRatio g :=
  lt_of_le_of_lt (xi_antitone (by norm_num) hg)
    (lt_of_lt_of_le (lt_trans (lt_trans xi_837_lt joining_decimals_lt)
      joining_decimal_lt_capacity_837) (capacityRatio_monotone hg))

end SubmittedGenus.TailComparison
