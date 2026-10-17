import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.BigOperators

/-! Fixed-degree reflection of a finite product, including vanishing rates.
No source graph or spectral localization is needed for this algebraic identity. -/
namespace SubmittedGenus.FixedPivot
open Polynomial
open scoped BigOperators
noncomputable section
variable {R I : Type*} [CommRing R]

lemma linearDenominator_natDegree_le (rate : R) : (1-C rate*X).natDegree≤1 := by
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · simp
  · apply Polynomial.natDegree_mul_le.trans
    simpa only [Polynomial.natDegree_C,zero_add] using (Polynomial.natDegree_X_le (R:=R))

lemma linearProduct_natDegree (s : Finset I) (rate : I→R) :
    (∏ i∈s,(1-C (rate i)*X)).natDegree≤s.card := by
  apply (Polynomial.natDegree_prod_le _ _).trans
  calc
    _ ≤ ∑ _i∈s,1 := Finset.sum_le_sum (fun i _=>linearDenominator_natDegree_le (rate i))
    _ = _ := by simp

lemma reflect_linearProduct [DecidableEq I] (s : Finset I) (rate : I→R) :
    (∏ i∈s,(1-C (rate i)*X)).reflect s.card=∏ i∈s,(X-C (rate i)) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    simp only [Finset.card_insert_of_notMem ha,Finset.prod_insert ha]
    rw [Nat.add_comm s.card 1,Polynomial.reflect_mul _ _
      (linearDenominator_natDegree_le (rate a)) (linearProduct_natDegree s rate),ih]
    simp only [Polynomial.reflect_sub,Polynomial.reflect_one,pow_one,Polynomial.reflect_C_mul,
      Polynomial.reflect_one_X,mul_one]

end
end SubmittedGenus.FixedPivot
