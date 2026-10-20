import Results.Genus.FixedPivot.CoefficientDegree

/-! Degree bounds for the exact original progression denominator. -/
namespace SubmittedGenus.FixedPivot
open Polynomial
open scoped BigOperators
noncomputable section

lemma progressionPair_natDegree (b c : Polynomial ℚ) (d j : ℕ) :
    (progressionPair b c d j).natDegree≤2 := by
  unfold progressionPair
  apply (natDegree_add_le _ _).trans
  apply max_le
  · apply (natDegree_sub_le _ _).trans
    apply max_le
    · simp
    · apply (natDegree_C_mul_le _ _).trans
      simp
  · apply (natDegree_C_mul_le _ _).trans
    simp

/-- Q_d has exactly at most d+1 progression coefficients, as its source mode count requires. -/
theorem rationalSourceQ_natDegree (d : ℕ) : (rationalSourceQ d).natDegree≤d+1 := by
  unfold rationalSourceQ progressionPolynomial
  apply natDegree_mul_le.trans
  have hp : (∏ j∈Finset.range ((d+1)/2),progressionPair (carryB (X : Polynomial ℚ)) (carryC X) d j).natDegree≤
      2*((d+1)/2) := by
    apply (natDegree_prod_le _ _).trans
    calc
      _ ≤ ∑ _j ∈ Finset.range ((d+1)/2),2 := Finset.sum_le_sum (fun j _ => progressionPair_natDegree _ _ _ _)
      _ = _ := by simp [Nat.mul_comm]
  split_ifs with he
  · have hl : (1-C ((carryC (X : Polynomial ℚ))^(d/2))*X).natDegree≤1 := by
      apply (natDegree_sub_le _ _).trans
      apply max_le
      · simp
      · apply (natDegree_C_mul_le _ _).trans
        simp
    obtain ⟨k,hk⟩:=he
    omega
  · simp only [natDegree_one,add_zero]
    omega

/-- Specializing the progression variable to1 gives degree at most3*d*(d+1). -/
theorem rationalSourceQ_eval_one_natDegree (d : ℕ) :
    (Polynomial.eval 1 (rationalSourceQ d)).natDegree≤3*d*(d+1) := by
  rw [Polynomial.eval_eq_sum_range]
  apply natDegree_sum_le_of_forall_le
  intro j hj
  have hj':=Finset.mem_range.mp hj
  have hq:=rationalSourceQ_natDegree d
  have hc:=rationalSourceQ_coefficientDegree d j
  simp only [one_pow,mul_one]
  nlinarith

end
end SubmittedGenus.FixedPivot
