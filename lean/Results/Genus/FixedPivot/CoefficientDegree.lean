import Results.Genus.FixedPivot.ProgressionPolynomial
import Results.Genus.FixedPivot.SourceDegree
import Mathlib.Algebra.Polynomial.BigOperators

/-! Original weighted coefficient-degree bounds for the integral progression polynomial. -/
namespace SubmittedGenus.FixedPivot
open Polynomial
open scoped BigOperators
noncomputable section

/-- Coefficient j has z-degree at most L*j. -/
def CoefficientDegreeBound (L : ℕ) (q : Polynomial (Polynomial ℚ)) : Prop :=
  ∀ j,(q.coeff j).natDegree≤L*j

lemma coefficientDegreeBound_one (L : ℕ) : CoefficientDegreeBound L 1 := by
  intro j
  simp only [Polynomial.coeff_one]
  split_ifs <;> simp

lemma CoefficientDegreeBound.mul {L : ℕ} {p q : Polynomial (Polynomial ℚ)}
    (hp : CoefficientDegreeBound L p) (hq : CoefficientDegreeBound L q) :
    CoefficientDegreeBound L (p*q) := by
  intro n
  rw [Polynomial.coeff_mul]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro ij hij
  have he:=Finset.mem_antidiagonal.mp hij
  apply Polynomial.natDegree_mul_le.trans
  have hi:=hp ij.1
  have hj:=hq ij.2
  nlinarith

lemma coefficientDegreeBound_prod {I : Type*} {L : ℕ} (s : Finset I)
    (p : I→Polynomial (Polynomial ℚ)) (hp : ∀ i∈s,CoefficientDegreeBound L (p i)) :
    CoefficientDegreeBound L (∏ i∈s,p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using coefficientDegreeBound_one L
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact (hp i (Finset.mem_insert_self i s)).mul (ih (fun j hj => hp j (Finset.mem_insert_of_mem hj)))

lemma coefficientDegreeBound_quadratic {L : ℕ} (a b : Polynomial ℚ)
    (ha : a.natDegree≤L) (hb : b.natDegree≤2*L) :
    CoefficientDegreeBound L (1-C a*X+C b*X^2) := by
  intro j
  rw [show C a*X=(monomial 1 a : Polynomial (Polynomial ℚ)) by rw [← C_mul_X_pow_eq_monomial,pow_one],
    C_mul_X_pow_eq_monomial]
  simp only [coeff_add,coeff_sub,coeff_one,coeff_monomial]
  by_cases h0 : j=0
  · subst j; simp
  · by_cases h1 : j=1
    · subst j; simpa using ha
    · by_cases h2 : j=2
      · subst j; simpa [Nat.mul_comm] using hb
      · simp [h0,h1,h2,Ne.symm]

lemma coefficientDegreeBound_linear {L : ℕ} (a : Polynomial ℚ) (ha : a.natDegree≤L) :
    CoefficientDegreeBound L (1-C a*X) := by
  simpa using coefficientDegreeBound_quadratic a 0 ha (by simp)

lemma progressionPair_coefficientDegree {d j : ℕ} (hj : 2*j≤d) :
    CoefficientDegreeBound (3*d) (progressionPair (carryB (X : Polynomial ℚ)) (carryC X) d j) := by
  unfold progressionPair
  apply coefficientDegreeBound_quadratic
  · apply Polynomial.natDegree_mul_le.trans
    have hs:=traceSum_natDegree_le (d-2*j)
    have hc : ((carryC (X : Polynomial ℚ))^j).natDegree=4*j := by
      rw [Polynomial.natDegree_pow,carryC_natDegree]; omega
    rw [hc]
    omega
  · rw [Polynomial.natDegree_pow,carryC_natDegree]
    omega

def rationalSourceQ (d : ℕ) : Polynomial (Polynomial ℚ) :=
  progressionPolynomial (carryB X) (carryC X) d

/-- The manuscript's coefficient estimate deg q_j ≤3*d*j is derived from every
actual paired factor and the optional center, over rational polynomials. -/
theorem rationalSourceQ_coefficientDegree (d : ℕ) : CoefficientDegreeBound (3*d) (rationalSourceQ d) := by
  unfold rationalSourceQ progressionPolynomial
  apply CoefficientDegreeBound.mul
  · apply coefficientDegreeBound_prod
    intro j hj
    apply progressionPair_coefficientDegree
    have hh:=Finset.mem_range.mp hj
    omega
  · split_ifs
    · apply coefficientDegreeBound_linear
      rw [Polynomial.natDegree_pow,carryC_natDegree]
      omega
    · exact coefficientDegreeBound_one _

end
end SubmittedGenus.FixedPivot
