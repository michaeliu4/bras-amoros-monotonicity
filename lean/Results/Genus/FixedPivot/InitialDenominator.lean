import Results.Genus.FixedPivot.PolynomialRationality

/-! Identification of the assembled initial denominator with E_d R_d. -/
namespace SubmittedGenus.FixedPivot
open Polynomial
open scoped BigOperators
noncomputable section

lemma progressionPair_eval_one {R : Type*} [CommRing R] (b c : R) (d j : ℕ) :
    Polynomial.eval 1 (progressionPair b c d j)=1-c^j*traceSum b c (d-2*j)+c^d := by
  simp only [progressionPair,eval_add,eval_sub,eval_one,eval_mul,eval_C,eval_X,eval_pow,
    one_pow,mul_one]

lemma progressionPolynomial_eval_one {R : Type*} [CommRing R] (z : R) {d : ℕ} (hd : 0<d) :
    Polynomial.eval 1 (progressionPolynomial (carryB z) (carryC z) d)=
      pureDenominator z d*mixedDenominator z d := by
  rw [progressionPolynomial,eval_mul]
  have hp : Polynomial.eval 1 (∏ j∈Finset.range ((d+1)/2),
      progressionPair (carryB z) (carryC z) d j)=
      ∏ j∈Finset.range ((d+1)/2),mixedPair z d j := by
    rw [Polynomial.eval_prod]
    apply Finset.prod_congr rfl
    intro j _
    exact progressionPair_eval_one _ _ _ _
  rw [hp,show (d+1)/2=(d-1)/2+1 by omega,Finset.prod_range_succ']
  have hz : mixedPair z d 0=pureDenominator z d := by
    simp only [mixedPair,pureDenominator,pow_zero,mul_zero,Nat.sub_zero,one_mul]
  rw [hz]
  unfold mixedDenominator
  split_ifs <;> simp only [eval_sub,eval_one,eval_mul,eval_C,eval_X,mul_one] <;> ring

lemma rationalSourceQ_eval_one {d : ℕ} (hd : 0<d) :
    Polynomial.eval (1 : Polynomial ℚ) (rationalSourceQ d)=
      pureDenominator (X : Polynomial ℚ) d*mixedDenominator X d :=
  progressionPolynomial_eval_one X hd

end
end SubmittedGenus.FixedPivot
