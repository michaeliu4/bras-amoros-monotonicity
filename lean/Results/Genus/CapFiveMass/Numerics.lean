import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact arithmetic of the submitted multiple-five mass estimate

The radius and all three constants are exactly those of submitted manuscript
blob e04fb276e8ceed829059cf724ead1e18e8bc9e9f, lines 1655--1683.
The fourth traces below enumerate all four actual matrix-state indices.
No numerical approximation or opaque external certificate is used.
-/

noncomputable section
open scoped BigOperators
namespace SubmittedGenus.CapFiveMass

def radius : ℝ := 633 / 1000
def strongBound : ℝ := 876716 / 1000000
def carryBound : ℝ := 982645 / 1000000
def rootUpper : ℝ := 928171 / 1000000

def alphabetMass (t : ℕ) (z : ℝ) : ℝ := ∑ i : Fin t, z ^ (i.val + 1)

def strongEndpoint (z : ℝ) : ℝ := z ^ 3 + z ^ 4 + z ^ 5
def carryEndpoint (z : ℝ) : ℝ := z ^ 2 + z ^ 3 + z ^ 4

/-- The cyclic four-state polynomial of the actual threshold matrix D_t.
Physical states run from 1 through t, including the boundary state t. -/
def fourthTrace (t : ℕ) (z : ℝ) : ℝ :=
  ∑ i : Fin t, ∑ j : Fin t, ∑ k : Fin t, ∑ l : Fin t,
    if t ≤ (i.val + 1) + (j.val + 1) ∧ t ≤ (j.val + 1) + (k.val + 1) ∧
       t ≤ (k.val + 1) + (l.val + 1) ∧ t ≤ (l.val + 1) + (i.val + 1)
    then z ^ ((i.val + 1) + (j.val + 1) + (k.val + 1) + (l.val + 1)) else 0

lemma radius_bounds : 0 < radius ∧ radius < 1 := by norm_num [radius]
lemma norm_bound_order : 0 < strongBound ∧ strongBound < carryBound ∧ carryBound < 1 := by
  norm_num [strongBound, carryBound]
lemma alphabet_five_ge_carry : carryBound ≤ alphabetMass 5 radius := by
  norm_num [carryBound, alphabetMass, radius, Fin.sum_univ_succ]
lemma strong_endpoint_le : strongEndpoint radius ≤ strongBound := by
  norm_num [strongEndpoint, radius, strongBound]
lemma carry_endpoint_le : carryEndpoint radius ≤ carryBound := by
  norm_num [carryEndpoint, radius, carryBound]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
lemma fourthTrace_five_lt : fourthTrace 5 radius < strongBound ^ 4 := by
  norm_num [fourthTrace, radius, strongBound, Fin.sum_univ_succ]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
lemma fourthTrace_four_lt : fourthTrace 4 radius < carryBound ^ 4 := by
  norm_num [fourthTrace, radius, carryBound, Fin.sum_univ_succ]

lemma root_square_bounds : (1 / 2 : ℝ) ^ 2 < strongBound * carryBound ∧
    strongBound * carryBound < rootUpper ^ 2 ∧ rootUpper < 1 := by
  norm_num [strongBound, carryBound, rootUpper]

lemma root_bounds : (1 / 2 : ℝ) < Real.sqrt (strongBound * carryBound) ∧
    Real.sqrt (strongBound * carryBound) < rootUpper ∧ rootUpper < 1 := by
  have hn : 0 ≤ strongBound * carryBound := by
    exact mul_nonneg norm_bound_order.1.le (norm_bound_order.1.trans norm_bound_order.2.1).le
  have hs := Real.sq_sqrt hn
  have hz := Real.sqrt_nonneg (strongBound * carryBound)
  have h := root_square_bounds
  have ht : 0 < rootUpper := by norm_num [rootUpper]
  exact ⟨by nlinarith, by nlinarith, h.2.2⟩

/-- The final displayed rational upper estimate. The strict 113 comparison
uses full exact fractions, not the printed decimal approximation. -/
def rationalMajorant : ℝ :=
  radius ^ 10 * alphabetMass 5 radius /
    (rootUpper * (1 - rootUpper) * (1 - strongBound) * (1 - carryBound))

lemma rationalMajorant_lt_113 : rationalMajorant < 113 := by
  norm_num [rationalMajorant, radius, alphabetMass, strongBound, carryBound,
    rootUpper, Fin.sum_univ_succ]

lemma rationalMajorant_lt_printed : rationalMajorant < 112194409824952 / (10 : ℝ) ^ 12 := by
  norm_num [rationalMajorant, radius, alphabetMass, strongBound, carryBound,
    rootUpper, Fin.sum_univ_succ]

/-- Exact scalar monotonicity used to replace sqrt(a_5*b_4) by tau. -/
lemma reciprocal_root_mono {x y : ℝ} (hx : (1 / 2 : ℝ) < x)
    (hxy : x ≤ y) (hy : y < 1) : 1 / (x * (1 - x)) ≤ 1 / (y * (1 - y)) := by
  have hy0 : 0 < y := by linarith
  have hx0 : 0 < x := by linarith
  have hx1 : x < 1 := hxy.trans_lt hy
  apply one_div_le_one_div_of_le (mul_pos hy0 (sub_pos.mpr hy))
  have hh : 0 ≤ (y - x) * (x + y - 1) := mul_nonneg (sub_nonneg.mpr hxy) (by linarith)
  nlinarith

/-- The exact denominator containing the square root is bounded before any
source summation is invoked. -/
def rootMajorant : ℝ :=
  radius ^ 10 * alphabetMass 5 radius /
    (Real.sqrt (strongBound * carryBound) * (1 - Real.sqrt (strongBound * carryBound)) *
      (1 - strongBound) * (1 - carryBound))

lemma rootMajorant_le_rational : rootMajorant ≤ rationalMajorant := by
  have hroot := root_bounds
  have hb := norm_bound_order
  have hx0 : 0 < Real.sqrt (strongBound * carryBound) := by linarith
  have ht0 : 0 < rootUpper := hx0.trans hroot.2.1
  have hx1 : Real.sqrt (strongBound * carryBound) < 1 := hroot.2.1.trans hroot.2.2
  have hab : 0 < (1 - strongBound) * (1 - carryBound) :=
    mul_pos (sub_pos.mpr (hb.2.1.trans hb.2.2)) (sub_pos.mpr hb.2.2)
  have hden : rootUpper * (1 - rootUpper) ≤
      Real.sqrt (strongBound * carryBound) * (1 - Real.sqrt (strongBound * carryBound)) := by
    have hh : 0 ≤ (rootUpper - Real.sqrt (strongBound * carryBound)) *
        (Real.sqrt (strongBound * carryBound) + rootUpper - 1) :=
      mul_nonneg (sub_nonneg.mpr hroot.2.1.le) (by linarith)
    nlinarith
  have hpos : 0 < rootUpper * (1 - rootUpper) * (1 - strongBound) * (1 - carryBound) := by
    have h := mul_pos (mul_pos ht0 (sub_pos.mpr hroot.2.2)) hab
    simpa [mul_assoc] using h
  apply div_le_div_of_nonneg_left ?_ hpos ?_
  · exact mul_nonneg (pow_nonneg radius_bounds.1.le _) (Finset.sum_nonneg fun _ _ =>
      pow_nonneg radius_bounds.1.le _)
  · change rootUpper * (1 - rootUpper) * (1 - strongBound) * (1 - carryBound) ≤ _
    simpa [mul_assoc] using mul_le_mul_of_nonneg_right hden hab.le

lemma rootMajorant_lt_113 : rootMajorant < 113 :=
  rootMajorant_le_rational.trans_lt rationalMajorant_lt_113

end SubmittedGenus.CapFiveMass
