import Results.Genus.CapFiveMass.Numerics
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Complete geometric majorant of the submitted multiple-five estimate

The three nonnegative indices are exactly r=1+i, p=2+i+j,
m=3+i+j+l. The inverse square-root prefactor retains the r=1,p=2
boundary, whose manuscript exponent r+p-4 is -1, not natural zero.
-/

noncomputable section
open scoped BigOperators
namespace SubmittedGenus.CapFiveMass

def mixedRoot : ℝ := Real.sqrt (strongBound * carryBound)

def geometricTerm (q : ℕ × ℕ × ℕ) : ℝ :=
  (radius ^ 10 * alphabetMass 5 radius / mixedRoot) *
    (strongBound ^ q.1 * (mixedRoot ^ q.2.1 * carryBound ^ q.2.2))

lemma mixedRoot_pos : 0 < mixedRoot := by
  have := root_bounds.1
  dsimp [mixedRoot]
  linarith

lemma mixedRoot_lt_one : mixedRoot < 1 := root_bounds.2.1.trans root_bounds.2.2

lemma geometricTerm_nonneg (q : ℕ × ℕ × ℕ) : 0 ≤ geometricTerm q := by
  have hs : 0 ≤ alphabetMass 5 radius := Finset.sum_nonneg fun _ _ => pow_nonneg radius_bounds.1.le _
  exact mul_nonneg (div_nonneg (mul_nonneg (pow_nonneg radius_bounds.1.le _) hs) mixedRoot_pos.le)
    (mul_nonneg (pow_nonneg norm_bound_order.1.le _) (mul_nonneg (pow_nonneg mixedRoot_pos.le _)
      (pow_nonneg (norm_bound_order.1.trans norm_bound_order.2.1).le _)))

/-- The full three-dimensional geometric sum converges to the exact
square-root expression in the submitted paper. -/
lemma geometric_hasSum : HasSum geometricTerm rootMajorant := by
  have ha := hasSum_geometric_of_lt_one norm_bound_order.1.le (norm_bound_order.2.1.trans norm_bound_order.2.2)
  have hx := hasSum_geometric_of_lt_one mixedRoot_pos.le mixedRoot_lt_one
  have hb := hasSum_geometric_of_lt_one (norm_bound_order.1.trans norm_bound_order.2.1).le norm_bound_order.2.2
  have hxb := hx.mul hb (hx.summable.mul_of_nonneg hb.summable
    (fun _ => pow_nonneg mixedRoot_pos.le _)
    (fun _ => pow_nonneg (norm_bound_order.1.trans norm_bound_order.2.1).le _))
  have hall := ha.mul hxb (ha.summable.mul_of_nonneg hxb.summable
    (fun _ => pow_nonneg norm_bound_order.1.le _)
    (fun _ => mul_nonneg (pow_nonneg mixedRoot_pos.le _)
      (pow_nonneg (norm_bound_order.1.trans norm_bound_order.2.1).le _)))
  have h := hall.mul_left (radius ^ 10 * alphabetMass 5 radius / mixedRoot)
  have he : radius ^ 10 * alphabetMass 5 radius / mixedRoot *
      ((1 - strongBound)⁻¹ * ((1 - mixedRoot)⁻¹ * (1 - carryBound)⁻¹)) = rootMajorant := by
    unfold rootMajorant mixedRoot
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [he] at h
  exact h

lemma geometric_summable : Summable geometricTerm := geometric_hasSum.summable
lemma geometric_tsum : (∑' q, geometricTerm q) = rootMajorant := geometric_hasSum.tsum_eq
lemma geometric_tsum_lt_113 : (∑' q, geometricTerm q) < 113 := by
  rw [geometric_tsum]
  exact rootMajorant_lt_113

/-- Every finite set of actual parameter triples obeys the same strict
113 scalar ceiling, with no limiting or enumeration assumption. -/
lemma geometric_finset_lt_113 (s : Finset (ℕ × ℕ × ℕ)) :
    (∑ q ∈ s, geometricTerm q) < 113 :=
  (geometric_summable.sum_le_tsum s (fun q _ => geometricTerm_nonneg q)).trans_lt geometric_tsum_lt_113

end SubmittedGenus.CapFiveMass
