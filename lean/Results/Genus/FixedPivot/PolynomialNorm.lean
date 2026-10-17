import Results.Genus.WeightedSeries
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic

/-! Finite polynomial absolute coefficient norms, connected to the full-series norm. -/
noncomputable section
namespace SubmittedGenus.FixedPivot
open scoped BigOperators
open WeightedSeries

/-- This is the manuscript's absolute coefficient norm on a genuine polynomial. -/
def polynomialNorm (q : ℝ) (p : Polynomial ℝ) : ℝ := weightedNorm q p.coeff

lemma polynomial_summable (q : ℝ) (p : Polynomial ℝ) : WeightedSummable q p.coeff := by
  apply (weightedSummable_and_norm_eq_prefix_of_support (N := p.natDegree+1) ?_).1
  intro n hn
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

lemma polynomialNorm_eq_sum (q : ℝ) (p : Polynomial ℝ) :
    polynomialNorm q p = ∑ n ∈ p.support, |p.coeff n| * q^n := by
  unfold polynomialNorm weightedNorm absWeightedTerm
  apply tsum_eq_sum
  intro n hn
  rw [Polynomial.notMem_support_iff.mp hn]
  simp

lemma polynomialNorm_nonneg {q : ℝ} (hq : 0 ≤ q) (p : Polynomial ℝ) :
    0 ≤ polynomialNorm q p := weightedNorm_nonneg hq _

/-- Nonnegative polynomial coefficients justify evaluation; no infinite raw F is evaluated. -/
lemma polynomialNorm_eq_eval {q : ℝ} (p : Polynomial ℝ)
    (hp : ∀ n, 0 ≤ p.coeff n) : polynomialNorm q p = p.eval q := by
  rw [polynomialNorm_eq_sum,Polynomial.eval_eq_sum,Polynomial.sum_def]
  apply Finset.sum_congr rfl
  intro n _
  rw [abs_of_nonneg (hp n)]

lemma polynomialNorm_neg (q : ℝ) (p : Polynomial ℝ) :
    polynomialNorm q (-p) = polynomialNorm q p := by
  unfold polynomialNorm weightedNorm absWeightedTerm
  simp only [Polynomial.coeff_neg,abs_neg]

lemma polynomialNorm_add_le {q : ℝ} (hq : 0 ≤ q) (p t : Polynomial ℝ) :
    polynomialNorm q (p+t) ≤ polynomialNorm q p+polynomialNorm q t := by
  let N := max (p+t).natDegree (max p.natDegree t.natDegree)+1
  have ha : ∀ n, N ≤ n → (p+t).coeff n=0 := by
    intro n hn
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    dsimp [N] at hn
    omega
  have he := (weightedSummable_and_norm_eq_prefix_of_support (q := q) ha).2
  unfold polynomialNorm
  rw [he]
  calc
    prefixNorm q (p+t).coeff N = prefixNorm q (fun n => p.coeff n+t.coeff n) N := by
      rfl
    _ ≤ prefixNorm q p.coeff N+prefixNorm q t.coeff N := prefixNorm_add_le hq _ _ _
    _ ≤ weightedNorm q p.coeff+weightedNorm q t.coeff :=
      add_le_add ((polynomial_summable q p).prefixNorm_le hq N)
        ((polynomial_summable q t).prefixNorm_le hq N)

lemma polynomialNorm_sub_le {q : ℝ} (hq : 0 ≤ q) (p t : Polynomial ℝ) :
    polynomialNorm q (p-t) ≤ polynomialNorm q p+polynomialNorm q t := by
  simpa only [sub_eq_add_neg,polynomialNorm_neg] using polynomialNorm_add_le hq p (-t)

lemma polynomialNorm_mul_le {q : ℝ} (hq : 0 ≤ q) (p t : Polynomial ℝ) :
    polynomialNorm q (p*t) ≤ polynomialNorm q p*polynomialNorm q t := by
  have he : (p*t).coeff = convolution p.coeff t.coeff := by
    funext n
    exact Polynomial.coeff_mul p t n
  unfold polynomialNorm
  rw [he]
  exact weightedNorm_convolution_le (polynomial_summable q p) (polynomial_summable q t) hq

@[simp] lemma polynomialNorm_one (q : ℝ) : polynomialNorm q 1=1 := by
  rw [polynomialNorm_eq_eval]
  · simp
  · intro n
    simp only [Polynomial.coeff_one]
    split_ifs <;> norm_num

@[simp] lemma polynomialNorm_zero (q : ℝ) : polynomialNorm q 0=0 := by
  simp [polynomialNorm,weightedNorm,absWeightedTerm]

lemma polynomialNorm_pow_le {q : ℝ} (hq : 0 ≤ q) (p : Polynomial ℝ) (n : ℕ) :
    polynomialNorm q (p^n) ≤ (polynomialNorm q p)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ,pow_succ]
    exact (polynomialNorm_mul_le hq _ _).trans
      (mul_le_mul_of_nonneg_right ih (polynomialNorm_nonneg hq p))

lemma polynomialNorm_prod_le {q : ℝ} (hq : 0 ≤ q) {ι : Type*}
    (s : Finset ι) (p : ι → Polynomial ℝ) :
    polynomialNorm q (∏ i ∈ s, p i) ≤ ∏ i ∈ s, polynomialNorm q (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi,Finset.prod_insert hi]
    exact (polynomialNorm_mul_le hq _ _).trans
      (mul_le_mul_of_nonneg_left ih (polynomialNorm_nonneg hq (p i)))

/-- Coefficientwise nonnegativity is closed under genuine polynomial multiplication. -/
lemma polynomial_coeff_mul_nonneg {p t : Polynomial ℝ}
    (hp : ∀ n, 0 ≤ p.coeff n) (ht : ∀ n, 0 ≤ t.coeff n) (n : ℕ) :
    0 ≤ (p*t).coeff n := by
  rw [Polynomial.coeff_mul]
  exact Finset.sum_nonneg (fun ij _ => mul_nonneg (hp _) (ht _))

lemma polynomial_coeff_pow_nonneg {p : Polynomial ℝ}
    (hp : ∀ n, 0 ≤ p.coeff n) (k n : ℕ) : 0 ≤ (p^k).coeff n := by
  induction k generalizing n with
  | zero => simp only [pow_zero,Polynomial.coeff_one]; split_ifs <;> norm_num
  | succ k ih =>
    rw [pow_succ]
    exact polynomial_coeff_mul_nonneg (fun n => by exact ih (n := n)) hp n

/-- Polynomial and full formal-series norms are the same, including the zero tail. -/
lemma polynomialNorm_eq_series (q : ℝ) (p : Polynomial ℝ) :
    polynomialNorm q p = weightedNorm q (fun n => PowerSeries.coeff n (p : PowerSeries ℝ)) := by
  simp only [Polynomial.coeff_coe,polynomialNorm]

end SubmittedGenus.FixedPivot
