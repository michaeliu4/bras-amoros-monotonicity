import Results.Genus.FixedPivot.ProgressionDegree
import Results.Genus.FixedPivot.RawDegree

/-! The original finite initial-data numerator and its source-derived z-degree bound. -/
namespace SubmittedGenus.FixedPivot
open RawGraph Polynomial
open scoped BigOperators
noncomputable section

def rawPolynomialQ (m r p : ℕ) : Polynomial ℚ :=
  (rawPolynomial m r p 4).map (Nat.castRingHom ℚ)

lemma rawPolynomialQ_natDegree (m r p : ℕ) :
    (rawPolynomialQ m r p).natDegree≤3*m+r-2 :=
  Polynomial.natDegree_map_le.trans (raw_cap_four_natDegree m r p)

/-- N_s(1,z), formed from precisely the paper's first d+1 source phases. -/
def phaseInitialNumerator (r p d s : ℕ) : Polynomial ℚ :=
  ∑ k∈Finset.range (d+1),∑ j∈Finset.range (k+1),
    (rationalSourceQ d).coeff j*rawPolynomialQ (2*p+s+(k-j)*d) r p

/-- The source finite prefix plus all original phase numerators. -/
def originalInitialNumerator (r p d : ℕ) : Polynomial ℚ :=
  (∑ m∈Finset.Icc (p+1) (2*p),rawPolynomialQ m r p)*Polynomial.eval 1 (rationalSourceQ d)+
    ∑ s∈Finset.Icc 1 d,phaseInitialNumerator r p d s

lemma phaseInitialNumerator_natDegree {r p d s : ℕ} (hrp : r<p) (hs : s≤d) :
    (phaseInitialNumerator r p d s).natDegree≤3*d^2+3*d+6*p+r-2 := by
  unfold phaseInitialNumerator
  apply natDegree_sum_le_of_forall_le
  intro k hk
  apply natDegree_sum_le_of_forall_le
  intro j hj
  have hk':=Finset.mem_range.mp hk
  have hj':=Finset.mem_range.mp hj
  apply natDegree_mul_le.trans
  have hq:=rationalSourceQ_coefficientDegree d j
  have hz:=rawPolynomialQ_natDegree (2*p+s+(k-j)*d) r p
  have hjk : j≤k := by omega
  have hsub : (k-j)*d+j*d=k*d := by rw [← Nat.add_mul,Nat.sub_add_cancel hjk]
  have hkd : k*d≤d*d := Nat.mul_le_mul_right d (by omega)
  have hm : 2≤3*(2*p+s+(k-j)*d)+r := by omega
  have hraw : (rawPolynomialQ (2*p+s+(k-j)*d) r p).natDegree+2≤
      3*(2*p+s+(k-j)*d)+r := by omega
  have hD : 2≤3*d^2+3*d+6*p+r := by omega
  have hDsub:=Nat.sub_add_cancel hD
  nlinarith

lemma prefix_natDegree {r p : ℕ} (hrp : r<p) :
    (∑ m∈Finset.Icc (p+1) (2*p),rawPolynomialQ m r p).natDegree≤6*p+r-2 := by
  apply natDegree_sum_le_of_forall_le
  intro m hm
  have hb:=Finset.mem_Icc.mp hm
  have hz:=rawPolynomialQ_natDegree m r p
  omega

/-- The precise original D0 bound is proved for the actual initial-data polynomial. -/
theorem originalInitialNumerator_natDegree {r p d : ℕ} (hrp : r<p) :
    (originalInitialNumerator r p d).natDegree≤3*d^2+3*d+6*p+r-2 := by
  unfold originalInitialNumerator
  apply (natDegree_add_le _ _).trans
  apply max_le
  · apply natDegree_mul_le.trans
    have hp:=prefix_natDegree hrp
    have hq:=rationalSourceQ_eval_one_natDegree d
    have hP : 2≤6*p+r := by omega
    have hPs:=Nat.sub_add_cancel hP
    have hD : 2≤3*d^2+3*d+6*p+r := by omega
    have hDs:=Nat.sub_add_cancel hD
    nlinarith
  · apply natDegree_sum_le_of_forall_le
    intro s hs
    exact phaseInitialNumerator_natDegree hrp (Finset.mem_Icc.mp hs).2

/-- Cancelling the actual initial-data polynomial gives the advertised degree,
without a separately supplied degree premise. -/
theorem source_initial_numerator_degree_descent {r p : ℕ} (hrp : r<p)
    (A : Polynomial ℚ) (hA : originalInitialNumerator r p (p-r)=sourceL (p-r)*A) :
    A.natDegree≤3*(p-r)^2+7*p+6 :=
  original_numerator_degree_descent hrp rfl _ A hA (originalInitialNumerator_natDegree hrp)

end
end SubmittedGenus.FixedPivot
