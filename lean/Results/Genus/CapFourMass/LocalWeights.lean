import Results.Genus.CapFourMass.GadgetCompletion
import Results.Genus.CapFiveMass.Numerics
import Mathlib.Tactic.FieldSimp

namespace SubmittedGenus.CapFourMass.LocalWeights
open scoped BigOperators
noncomputable section

def a (z : ℝ) := z
def b (z : ℝ) := z^2+z^3
def s (z : ℝ) := a z+b z

def spinWeight (z : ℝ) (v : Fin 3) : ℝ := z^(v.val+1)
def leafWeight (z : ℝ) (c : Fin 3) : ℝ :=
  ∑ v : Fin 3, if 3 ≤ (c.val+1)+(v.val+1) then spinWeight z v else 0

def starWeight (z : ℝ) : ℝ :=
  ∑ c : Fin 3, spinWeight z c * (leafWeight z c)^2

def highWeight (z : ℝ) : ℝ :=
  ∑ v : Fin 3, if 2 ≤ v.val+1 then spinWeight z v else 0

theorem spin_sum (z : ℝ) : (∑ v : Fin 3, spinWeight z v) = s z := by
  simp [spinWeight, Fin.sum_univ_succ, s, a, b]

theorem highWeight_eq (z : ℝ) : highWeight z = b z := by
  norm_num [highWeight, spinWeight, Fin.sum_univ_succ, b]

theorem starWeight_eq (z : ℝ) : starWeight z = a z*(b z)^2+b z*(s z)^2 := by
  norm_num [starWeight, leafWeight, spinWeight, Fin.sum_univ_succ, a, b, s]
  ring

def epsilon (z : ℝ) := a z*b z*z^3 / (s z*(a z*b z+(s z)^2))
def delta (z : ℝ) := epsilon z/(1+z)^2

theorem b_pos {z : ℝ} (hz : 0 < z) : 0 < b z := by unfold b; positivity
theorem s_pos {z : ℝ} (hz : 0 < z) : 0 < s z := by unfold s a; have := b_pos hz; positivity

theorem starWeight_pos {z : ℝ} (hz : 0 < z) : 0 < starWeight z := by
  rw [starWeight_eq]
  have := b_pos hz
  unfold a
  positivity

/-- Exact four-distinct-vertex failure ratio. -/
theorem four_failure_ratio {z : ℝ} (hz : 0 < z) :
    z*z^3*(highWeight z)^2 / (s z * starWeight z) = epsilon z := by
  rw [highWeight_eq, starWeight_eq]
  have hb := ne_of_gt (b_pos hz)
  have hs := ne_of_gt (s_pos hz)
  have hbp := b_pos hz
  have hp : a z*b z+(s z)^2 ≠ 0 := by unfold a; positivity
  unfold epsilon a
  field_simp

/-- Identifying the target with one leaf only improves the failure ratio. -/
theorem shared_failure_ratio_ge {z : ℝ} (hz : 0 < z) :
    epsilon z ≤ z*z^3*highWeight z / starWeight z := by
  rw [highWeight_eq, starWeight_eq]
  have hb := b_pos hz
  have hs := s_pos hz
  have hstar := starWeight_pos hz
  rw [starWeight_eq] at hstar
  unfold epsilon a at *
  apply (div_le_div_iff₀ (by positivity) hstar).mpr
  have hz3 : 0 ≤ z^3 := by positivity
  dsimp [s, a] at *
  have hnon : 0 ≤ z^5*b z*(z*b z+(z+b z)^2) := by positivity
  nlinarith only [hnon]

/-- Exact postponed four-vertex weight ratio. -/
theorem postponed_four_ratio {z : ℝ} (hz : 0 < z) :
    z^8/(s z*starWeight z) = delta z := by
  rw [starWeight_eq]
  unfold delta epsilon s a b
  have hz' : z ≠ 0 := ne_of_gt hz
  field_simp

theorem epsilon_pos {z : ℝ} (hz : 0 < z) : 0 < epsilon z := by
  have hb := b_pos hz
  have hs := s_pos hz
  unfold epsilon a
  positivity

theorem epsilon_lt_one {z : ℝ} (hz : 0 < z) : epsilon z < 1 := by
  have hb := b_pos hz
  have hs := s_pos hz
  have hden : 0 < s z*(a z*b z+(s z)^2) := by unfold a; positivity
  unfold epsilon
  apply (div_lt_one hden).mpr
  have hz3s : z^3 < s z := by unfold s a b; nlinarith [sq_nonneg z]
  have hab : 0 < a z*b z := by unfold a; positivity
  have hfirst := mul_lt_mul_of_pos_left hz3s hab
  have hs3 : 0 < (s z)^3 := pow_pos hs 3
  nlinarith only [hfirst,hs3]

theorem delta_pos {z : ℝ} (hz : 0 < z) : 0 < delta z := by
  unfold delta
  have := epsilon_pos hz
  positivity

theorem delta_le_epsilon {z : ℝ} (hz : 0 < z) : delta z ≤ epsilon z := by
  unfold delta
  apply div_le_self (le_of_lt (epsilon_pos hz))
  nlinarith [sq_nonneg z]

theorem delta_lt_one {z : ℝ} (hz : 0 < z) : delta z < 1 :=
  lt_of_le_of_lt (delta_le_epsilon hz) (epsilon_lt_one hz)

theorem postponed_shared_ratio_ge {z : ℝ} (hz : 0 < z) :
    delta z ≤ z^6/starWeight z := by
  rw [← postponed_four_ratio hz]
  have hs := s_pos hz
  have hstar := starWeight_pos hz
  apply (div_le_div_iff₀ (mul_pos hs hstar) hstar).mpr
  have hs2 : 0 ≤ s z-z^2 := by unfold s a b; nlinarith [pow_pos hz 3]
  have hh : 0 ≤ z^6*(s z-z^2)*starWeight z := by positivity
  nlinarith only [hh]

end
end SubmittedGenus.CapFourMass.LocalWeights
