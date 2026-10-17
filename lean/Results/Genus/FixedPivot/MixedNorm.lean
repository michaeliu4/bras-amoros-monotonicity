import Results.Genus.FixedPivot.Denominator
import Results.Genus.FixedPivot.PolynomialNorm
import Results.Genus.InverseCertificates.MixedScalar

/-!
# Source-specific mixed-factor coefficient bounds

The actual integer-factor construction is interpreted as real polynomials and
bounded in the manuscript's absolute weighted norm. This supplies the missing
link from the carry eigenvalue factors to the scalar majorants a_j.
-/
noncomputable section
namespace SubmittedGenus.FixedPivot
open scoped BigOperators
open InverseCertificates WeightedSeries

local notation "Xr" => (Polynomial.X : Polynomial ℝ)

def carryTracePolynomial (n : ℕ) : Polynomial ℝ := traceSum (carryB Xr) (carryC Xr) n

lemma carryB_coeff_nonneg (n : ℕ) : 0 ≤ (carryB Xr).coeff n := by
  simp only [carryB,Polynomial.coeff_add,Polynomial.coeff_X_pow]
  positivity

lemma neg_carryC_coeff_nonneg (n : ℕ) : 0 ≤ (-carryC Xr).coeff n := by
  have he : -carryC Xr = Xr^3+Xr^4 := by unfold carryC; ring
  rw [he]
  simp only [Polynomial.coeff_add,Polynomial.coeff_X_pow]
  positivity

/-- The source S_n really has nonnegative coefficients. -/
theorem carryTrace_coeff_nonneg (k n : ℕ) : 0 ≤ (carryTracePolynomial k).coeff n := by
  induction k using Nat.twoStepInduction generalizing n with
  | zero =>
    simp only [carryTracePolynomial,traceSum_zero]
    rw [show (2 : Polynomial ℝ)=1+1 by ring,Polynomial.coeff_add]
    simp only [Polynomial.coeff_one]
    positivity
  | one => exact carryB_coeff_nonneg n
  | more k ih ih1 =>
    have he : carryTracePolynomial (k+2) =
        carryB Xr*carryTracePolynomial (k+1)+(-carryC Xr)*carryTracePolynomial k := by
      unfold carryTracePolynomial
      rw [traceSum_rec]
      ring
    rw [he,Polynomial.coeff_add]
    exact add_nonneg (polynomial_coeff_mul_nonneg carryB_coeff_nonneg ih1 n)
      (polynomial_coeff_mul_nonneg neg_carryC_coeff_nonneg ih n)

lemma carryB_at_q : carryB q = 1-u := by
  have h := q_relation
  have h' := congrArg (fun x : ℝ => q*x) h
  unfold carryB u
  nlinarith

lemma carryC_at_q : carryC q = -u := by
  have h := q_relation
  have h' := congrArg (fun x : ℝ => q^2*x) h
  unfold carryC u
  nlinarith

lemma carryTrace_eval (n : ℕ) : (carryTracePolynomial n).eval q = 1+(-u)^n := by
  have hm := map_traceSum (Polynomial.evalRingHom q) (carryB Xr) (carryC Xr) n
  have hb : (carryB Xr).eval q = carryB q := by simp [carryB]
  have hc : (carryC Xr).eval q = carryC q := by simp [carryC]
  change (carryTracePolynomial n).eval q =
    traceSum ((carryB Xr).eval q) ((carryC Xr).eval q) n at hm
  rw [hb,hc,carryB_at_q,carryC_at_q] at hm
  rw [hm]
  simpa only [one_mul,one_pow,sub_eq_add_neg] using traceSum_eq_powers (1 : ℝ) (-u) n

/-- Exact coefficient norm, justified by positivity rather than assumed evaluation. -/
theorem carryTrace_norm (n : ℕ) : polynomialNorm q (carryTracePolynomial n) = 1+(-u)^n := by
  rw [polynomialNorm_eq_eval _ (carryTrace_coeff_nonneg n),carryTrace_eval]

lemma carryTrace_norm_le (n : ℕ) : polynomialNorm q (carryTracePolynomial n) ≤ 1+u^n := by
  rw [carryTrace_norm]
  have h := le_abs_self ((-u)^n)
  rw [abs_pow,abs_neg,abs_of_nonneg u_nonneg] at h
  linarith

lemma carryC_norm : polynomialNorm q (carryC Xr) = u := by
  rw [← polynomialNorm_neg,polynomialNorm_eq_eval _ neg_carryC_coeff_nonneg]
  simp only [Polynomial.eval_neg]
  have he : (carryC Xr).eval q=carryC q := by simp [carryC]
  rw [he,carryC_at_q]
  ring

lemma carryC_pow_norm_le (n : ℕ) : polynomialNorm q ((carryC Xr)^n) ≤ u^n := by
  simpa only [carryC_norm] using polynomialNorm_pow_le q_nonneg (carryC Xr) n

/-- The complete nonconstant residual of each paired factor obeys its source bound. -/
theorem mixedPair_residual_norm (d j : ℕ) :
    polynomialNorm q (1-mixedPair Xr d j) ≤ u^j*(1+u^(d-2*j))+u^d := by
  have he : 1-mixedPair Xr d j =
      (carryC Xr)^j*carryTracePolynomial (d-2*j)-(carryC Xr)^d := by
    unfold mixedPair carryTracePolynomial
    ring
  rw [he]
  calc
    _ ≤ polynomialNorm q ((carryC Xr)^j*carryTracePolynomial (d-2*j))+
        polynomialNorm q ((carryC Xr)^d) := polynomialNorm_sub_le q_nonneg _ _
    _ ≤ polynomialNorm q ((carryC Xr)^j)*polynomialNorm q (carryTracePolynomial (d-2*j))+
        u^d := add_le_add (polynomialNorm_mul_le q_nonneg _ _) (carryC_pow_norm_le d)
    _ ≤ u^j*(1+u^(d-2*j))+u^d := add_le_add
      (mul_le_mul (carryC_pow_norm_le j) (carryTrace_norm_le (d-2*j))
        (polynomialNorm_nonneg q_nonneg _) (pow_nonneg u_nonneg j)) le_rfl

/-- This identifies the actual paired source factors with the original a_j majorant. -/
theorem mixedPair_residual_le_a (d j : ℕ) (hj : 2*j+1 ≤ d) :
    polynomialNorm q (1-mixedPair Xr d j) ≤ mixedA u j := by
  have he : u^j*u^(d-2*j)=u^(d-j) := by
    rw [← pow_add]
    congr 1
    omega
  have h1 : u^(d-j) ≤ u^(j+1) :=
    pow_le_pow_of_le_one u_nonneg u_lt_one.le (by omega)
  have h2 : u^d ≤ u^(2*j+1) :=
    pow_le_pow_of_le_one u_nonneg u_lt_one.le hj
  have hn := mixedPair_residual_norm d j
  rw [mul_add,mul_one,he] at hn
  unfold mixedA
  linarith

lemma mixedPair_norm_le (d j : ℕ) (hj : 2*j+1 ≤ d) :
    polynomialNorm q (mixedPair Xr d j) ≤ 1+mixedA u j := by
  have he : mixedPair Xr d j=1-(1-mixedPair Xr d j) := by ring
  calc
    polynomialNorm q (mixedPair Xr d j) ≤
      polynomialNorm q 1+polynomialNorm q (1-mixedPair Xr d j) := by
        conv_lhs => rw [he]
        exact polynomialNorm_sub_le q_nonneg _ _
    _ ≤ 1+mixedA u j := by
      rw [polynomialNorm_one]
      exact add_le_add le_rfl (mixedPair_residual_le_a d j hj)

end SubmittedGenus.FixedPivot
