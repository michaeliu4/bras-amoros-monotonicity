import Results.Genus.FixedPivot.CorrectedIdentity

/-! The sharper numerator-degree assertion in the original submitted display,
retaining the exact degree removed by L_d before taking tau≤2. -/
namespace SubmittedGenus.FixedPivot
open Polynomial
noncomputable section

/-- Additive form avoids any ambiguity about truncated natural subtraction. -/
theorem original_numerator_degree_sharp_add {r p d : ℕ} (hrp : r<p) (hd : d=p-r)
    (N A : Polynomial ℚ) (hcancel : N=sourceL d*A)
    (hN : N.natDegree≤3*d^2+3*d+6*p+r-2) :
    A.natDegree+2*d+2≤3*d^2+7*p+4*sourceTau d := by
  have hdpos : 0<d := by omega
  have ht:=sourceTau_le hdpos
  have htpos:=sourceTau_positive d
  have hrd : r+d=p := by omega
  by_cases hA : A=0
  · simp only [hA,Polynomial.natDegree_zero]
    omega
  · have hdegree:=congrArg Polynomial.natDegree hcancel
    rw [Polynomial.natDegree_mul (sourceL_ne_zero hdpos) hA,sourceL_natDegree hdpos] at hdegree
    omega

/-- Literal sharper submitted bound, before replacing tau by two. -/
theorem original_numerator_degree_sharp {r p d : ℕ} (hrp : r<p) (hd : d=p-r)
    (N A : Polynomial ℚ) (hcancel : N=sourceL d*A)
    (hN : N.natDegree≤3*d^2+3*d+6*p+r-2) :
    A.natDegree≤3*d^2-2*d+7*p+4*sourceTau d-2 := by
  have h:=original_numerator_degree_sharp_add hrp hd N A hcancel hN
  omega

/-- The sharper bound applies to the actual cancelled source numerator. -/
theorem correctedNumerator_natDegree_sharp {r d : ℕ} (hr : 0<r) (hd : 0<d) :
    (correctedNumerator r d hr hd).natDegree≤3*d^2-2*d+7*(r+d)+4*sourceTau d-2 :=
  original_numerator_degree_sharp (by omega) (by omega) _ _
    (correctedNumerator_spec hr hd) (originalInitialNumerator_natDegree (by omega))

end
end SubmittedGenus.FixedPivot
