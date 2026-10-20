import Results.Genus.FixedPivot.CorrectionNorm
import Mathlib.Data.Nat.Fib.Basic

/-! Original Binet-based signed conversion, including the eight-degree source support. -/
namespace SubmittedGenus.FixedPivot
open Polynomial WeightedSeries InverseCertificates
open scoped BigOperators
noncomputable section

lemma q_pos : 0<q := lt_trans (by norm_num) q_lower

/-- Binet's identity in a denominator-free weighted form at the original q. -/
lemma fibonacci_binet_weighted (n : ℕ) :
    (2*q+1)*(Nat.fib n : ℝ)*q^n=1-(-q^2)^n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp only [Nat.fib_one,Nat.cast_one,mul_one,pow_one]; nlinarith [q_relation]
  | more n ih ih1 =>
    calc
      _=q*((2*q+1)*(Nat.fib (n+1) : ℝ)*q^(n+1))+
          q^2*((2*q+1)*(Nat.fib n : ℝ)*q^n) := by
        rw [Nat.fib_add_two,Nat.cast_add]
        simp only [pow_add,pow_one]
        ring
      _=q*(1-(-q^2)^(n+1))+q^2*(1-(-q^2)^n) := by rw [ih,ih1]
      _=1-(-q^2)^(n+2) := by
        simp only [pow_succ]
        linear_combination (1+(-q^2)^n*q^2)*q_relation

lemma fibonacci_weighted_upper (n : ℕ) : (Nat.fib (n+1) : ℝ)*q^n≤1 := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simpa using q_lt_one.le
  | more n ih ih1 =>
    calc
      _=q*((Nat.fib (n+2) : ℝ)*q^(n+1))+q^2*((Nat.fib (n+1) : ℝ)*q^n) := by
        rw [show n+2+1=(n+1)+2 by omega,Nat.fib_add_two,Nat.cast_add]
        simp only [pow_add,pow_one]
        ring
      _≤q*1+q^2*1 := add_le_add (mul_le_mul_of_nonneg_left ih1 q_nonneg)
        (mul_le_mul_of_nonneg_left ih (sq_nonneg q))
      _=1 := by nlinarith [q_relation]

lemma original_binet_margin : 2*q+1<(9/4 : ℝ)*(1-q^16) := by
  have hp:=pow_le_pow_left₀ q_nonneg q_upper 16
  have hn : 2*((309017 : ℝ)/500000)+1<(9/4 : ℝ)*(1-((309017 : ℝ)/500000)^16) := by norm_num
  nlinarith [q_upper]

lemma fibonacci_weighted_lower {g : ℕ} (hg : 8≤g) :
    1≤(9/4 : ℝ)*(Nat.fib g : ℝ)*q^g := by
  have he:=fibonacci_binet_weighted g
  have ha : (-q^2)^g≤q^(2*g) := by
    calc
      _≤|(-q^2)^g| := le_abs_self _
      _=q^(2*g) := by rw [abs_pow,abs_neg,abs_of_nonneg (sq_nonneg q),pow_mul]
  have hp : q^(2*g)≤q^16 := pow_le_pow_of_le_one q_nonneg q_lt_one.le (by omega)
  have hlow : 1-q^16≤(2*q+1)*(Nat.fib g : ℝ)*q^g := by linarith
  have hs : 0<2*q+1 := by linarith [q_nonneg]
  have hmul:=mul_le_mul_of_nonneg_left hlow (show (0 : ℝ)≤9/4 by norm_num)
  nlinarith [original_binet_margin]

/-- Exactly the paper's 9/4 comparison, valid once the corrected support starts at8. -/
lemma fibonacci_kernel_bound {g j : ℕ} (hj : 8≤j) (hjg : j≤g) :
    (Nat.fib (g-j+1) : ℝ)≤(9/4 : ℝ)*q^j*(Nat.fib g : ℝ) := by
  apply (mul_le_mul_iff_left₀ (pow_pos q_pos (g-j))).mp
  calc
    _≤1 := by simpa [mul_comm] using fibonacci_weighted_upper (g-j)
    _≤(9/4 : ℝ)*(Nat.fib g : ℝ)*q^g := fibonacci_weighted_lower (by omega)
    _=_ := by
      have hp : q^g=q^j*q^(g-j) := by rw [← pow_add,Nat.add_sub_of_le hjg]
      rw [hp]
      ring

def fibonacciSeries : PowerSeries ℝ := PowerSeries.mk (fun n => (Nat.fib (n+1) : ℝ))

lemma correctionFactor_fibonacci : correctionFactor*fibonacciSeries=1 := by
  apply PowerSeries.ext
  intro n
  rcases n with _ | (_ | n)
  · simp [correctionFactor,fibonacciSeries]
  · norm_num [correctionFactor,fibonacciSeries,PowerSeries.coeff_mul,Finset.Nat.antidiagonal_succ,Finset.Nat.antidiagonal_zero,PowerSeries.coeff_X]
  · rw [correctionFactor,sub_mul,sub_mul,one_mul,pow_two,mul_assoc]
    simp only [map_sub,PowerSeries.coeff_succ_X_mul,fibonacciSeries,PowerSeries.coeff_mk,
      PowerSeries.coeff_one,show n+1+1≠0 by omega,if_false]
    rw [show n+1+1+1=(n+1)+2 by omega,Nat.fib_add_two,Nat.cast_add]
    ring

lemma fixedPivotSeriesReal_small {r p g : ℕ} (hr : 0<r) (hrp : r<p) (hg : g<8) :
    PowerSeries.coeff g (fixedPivotSeriesReal r p)=0 := by
  rw [fixedPivotSeriesReal_coeff]
  apply Finset.sum_eq_zero
  intro m _
  by_cases hm : p<m
  · exact rawPolynomialReal_coeff_zero (by omega)
  · rw [rawPolynomialReal_zero (by omega),Polynomial.coeff_zero]

lemma correctedSeries_small {r p j : ℕ} (hr : 0<r) (hrp : r<p) (hj : j<8) :
    PowerSeries.coeff j (correctedSeries r p)=0 := by
  unfold correctedSeries
  rw [PowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro ab hab
  have he:=Finset.mem_antidiagonal.mp hab
  rw [fixedPivotSeriesReal_small hr hrp (by omega),mul_zero]

/-- Signed reconstruction is an exact complete-series identity. -/
lemma fixedPivotSeriesReal_reconstruction (r p : ℕ) :
    fixedPivotSeriesReal r p=correctedSeries r p*fibonacciSeries := by
  unfold correctedSeries
  change _=(correctionFactor*fixedPivotSeriesReal r p)*fibonacciSeries
  rw [mul_right_comm,correctionFactor_fibonacci,one_mul]

/-- Original signed Fibonacci conversion; no positivity of corrected coefficients is used. -/
theorem fixedPivotSeriesReal_fibonacci_bound {r p : ℕ} (hr : 0<r) (hrp : r<p)
    (hs : WeightedSummable q (fun n => PowerSeries.coeff n (correctedSeries r p))) (g : ℕ) :
    PowerSeries.coeff g (fixedPivotSeriesReal r p)≤
      (9/4 : ℝ)*weightedNorm q (fun n => PowerSeries.coeff n (correctedSeries r p))*(Nat.fib g : ℝ) := by
  rw [fixedPivotSeriesReal_reconstruction,PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [fibonacciSeries,PowerSeries.coeff_mk]
  calc
    _≤∑ j∈Finset.range (g+1),
        |PowerSeries.coeff j (correctedSeries r p)| *((9/4 : ℝ)*q^j*(Nat.fib g : ℝ)) := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases hj8 : 8≤j
      · exact (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)).trans
          (mul_le_mul_of_nonneg_left (fibonacci_kernel_bound hj8 (by have:=Finset.mem_range.mp hj; omega)) (abs_nonneg _))
      · rw [correctedSeries_small hr hrp (by omega),abs_zero,zero_mul,zero_mul]
    _=(9/4 : ℝ)*prefixNorm q (fun n => PowerSeries.coeff n (correctedSeries r p)) (g+1)*(Nat.fib g : ℝ) := by
      unfold prefixNorm absWeightedTerm
      rw [Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _≤_ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hs.prefixNorm_le q_nonneg (g+1)) (by norm_num)) (by positivity)

end
end SubmittedGenus.FixedPivot
