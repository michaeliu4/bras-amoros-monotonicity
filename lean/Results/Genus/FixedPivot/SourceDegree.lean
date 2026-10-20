import Results.Genus.FixedPivot.PureDivisor
import Mathlib.Algebra.Polynomial.Degree.Domain

/-! Exact original E_d and L_d degrees, and the algebraic numerator-degree descent. -/
noncomputable section
namespace SubmittedGenus.FixedPivot
open Polynomial

lemma carryB_natDegree : (carryB (X : Polynomial ℚ)).natDegree=3 := by
  unfold carryB
  compute_degree!

lemma carryC_natDegree : (carryC (X : Polynomial ℚ)).natDegree=4 := by
  unfold carryC
  compute_degree!

/-- The original Newton-sum coefficient-degree estimate. -/
theorem traceSum_natDegree_le (n : ℕ) :
    (traceSum (carryB (X : Polynomial ℚ)) (carryC X) n).natDegree ≤ 3*n := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num [traceSum]
  | one => simpa [traceSum,carryB_natDegree]
  | more n ih ih1 =>
    rw [traceSum_rec]
    apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · apply Polynomial.natDegree_mul_le.trans
      rw [carryB_natDegree]
      omega
    · apply Polynomial.natDegree_mul_le.trans
      rw [carryC_natDegree]
      omega

lemma sourceE_ne_zero {d : ℕ} (hd : 0<d) : sourceE d≠0 := by
  intro h
  have he:=sourceE_zero hd
  rw [h] at he
  simp at he

/-- The leading c^d term cannot cancel: its degree4d exceeds the trace bound3d. -/
theorem sourceE_natDegree {d : ℕ} (hd : 0<d) : (sourceE d).natDegree=4*d := by
  have htrace:=traceSum_natDegree_le d
  have hsmall : (1-traceSum (carryB (X : Polynomial ℚ)) (carryC X) d).natDegree ≤ 3*d := by
    apply (Polynomial.natDegree_sub_le _ _).trans
    simp only [Polynomial.natDegree_one,zero_le,max_eq_right]
    exact htrace
  have hc : ((carryC (X : Polynomial ℚ))^d).natDegree=4*d := by
    rw [Polynomial.natDegree_pow,carryC_natDegree]
    omega
  unfold sourceE pureDenominator
  rw [Polynomial.natDegree_add_eq_right_of_natDegree_lt (by rw [hc]; omega),hc]

lemma sourceTau_positive (d : ℕ) : 0<sourceTau d := by
  unfold sourceTau
  split_ifs <;> omega

lemma sourceTau_le_two (d : ℕ) : sourceTau d≤2 := by
  unfold sourceTau
  split_ifs <;> omega

lemma sourceTau_le {d : ℕ} (hd : 0<d) : sourceTau d≤d :=
  Nat.le_of_dvd hd (sourceTau_dvd d)

lemma sourceL_ne_zero {d : ℕ} (hd : 0<d) : sourceL d≠0 := by
  intro h
  have he:=sourceE_factor_sourceL d
  rw [h,mul_zero] at he
  exact sourceE_ne_zero hd he

/-- Cancelling L_d removes exactly4(d−tau) degrees, with multiplicity. -/
theorem sourceL_natDegree {d : ℕ} (hd : 0<d) :
    (sourceL d).natDegree=4*(d-sourceTau d) := by
  have he:=sourceE_factor_sourceL d
  have hn:=congrArg Polynomial.natDegree he
  rw [sourceE_natDegree hd,Polynomial.natDegree_mul
    (sourceE_ne_zero (sourceTau_positive d)) (sourceL_ne_zero hd),
    sourceE_natDegree (sourceTau_positive d)] at hn
  have ht:=sourceTau_le hd
  omega

/-- Original numerator-degree arithmetic after actual divisibility has been established.
The premise names the polynomial numerator and its source initial-data degree bound;
it does not assert that an arbitrary raw F has this representation. -/
theorem original_numerator_degree_descent {r p d : ℕ} (hrp : r<p) (hd : d=p-r)
    (N A : Polynomial ℚ) (hcancel : N=sourceL d*A)
    (hN : N.natDegree ≤ 3*d^2+3*d+6*p+r-2) :
    A.natDegree ≤ 3*d^2+7*p+6 := by
  have hdpos : 0<d := by omega
  by_cases hA : A=0
  · simp [hA]
  · have hdegree:=congrArg Polynomial.natDegree hcancel
    rw [Polynomial.natDegree_mul (sourceL_ne_zero hdpos) hA,sourceL_natDegree hdpos] at hdegree
    have ht:=sourceTau_le hdpos
    have ht2:=sourceTau_le_two d
    have hrd : r+d=p := by omega
    omega

end SubmittedGenus.FixedPivot
