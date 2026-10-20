import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Absolute weighted coefficient sums for the submitted genus proof

This file supplies the convergence and signed-coefficient foundations used by the
original fixed-pivot argument. In particular `weightedNorm` is a real-valued
`tsum`; it is used as a norm only with a `WeightedSummable` hypothesis. It is not
an extended-real norm on divergent series.

No concrete graph mass, denominator residual, or manuscript numerical bound is
assumed or certified here.
-/

noncomputable section

open scoped BigOperators
open Finset

namespace SubmittedGenus
namespace WeightedSeries

/-- Nonnegative bounded prefixes prove both convergence and the same bound. -/
theorem summable_and_tsum_le_of_prefix_bound {f : ℕ → ℝ} {C : ℝ}
    (hf : ∀ n, 0 ≤ f n) (hC : ∀ N, ∑ n ∈ range N, f n ≤ C) :
    Summable f ∧ (∑' n, f n) ≤ C :=
  ⟨summable_of_sum_range_le hf hC, Real.tsum_le_of_sum_range_le hf hC⟩

/-- Signed coefficients after evaluation at a nonnegative radius. -/
def weightedTerm (q : ℝ) (a : ℕ → ℝ) (n : ℕ) : ℝ := a n * q ^ n

/-- Absolute coefficient majorant at the radius `q`. -/
def absWeightedTerm (q : ℝ) (a : ℕ → ℝ) (n : ℕ) : ℝ := |a n| * q ^ n

/-- Absolute weighted summability; this is never inferred from a default `tsum`. -/
def WeightedSummable (q : ℝ) (a : ℕ → ℝ) : Prop := Summable (absWeightedTerm q a)

/-- The finite real absolute weighted norm on absolutely summable sequences. -/
def weightedNorm (q : ℝ) (a : ℕ → ℝ) : ℝ := ∑' n, absWeightedTerm q a n

/-- The finite prefix includes degrees strictly below `N`. -/
def prefixNorm (q : ℝ) (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ range N, absWeightedTerm q a n

lemma absWeightedTerm_nonneg {q : ℝ} (hq : 0 ≤ q) (a : ℕ → ℝ) (n : ℕ) :
    0 ≤ absWeightedTerm q a n := mul_nonneg (abs_nonneg _) (pow_nonneg hq _)

lemma norm_weightedTerm {q : ℝ} (hq : 0 ≤ q) (a : ℕ → ℝ) (n : ℕ) :
    ‖weightedTerm q a n‖ = absWeightedTerm q a n := by
  simp [weightedTerm, absWeightedTerm, Real.norm_eq_abs, abs_mul, abs_of_nonneg hq]

lemma weightedNorm_nonneg {q : ℝ} (hq : 0 ≤ q) (a : ℕ → ℝ) :
    0 ≤ weightedNorm q a := tsum_nonneg (absWeightedTerm_nonneg hq a)

lemma prefixNorm_nonneg {q : ℝ} (hq : 0 ≤ q) (a : ℕ → ℝ) (N : ℕ) :
    0 ≤ prefixNorm q a N := sum_nonneg fun n _ => absWeightedTerm_nonneg hq a n

lemma WeightedSummable.norm_summable {q : ℝ} {a : ℕ → ℝ}
    (ha : WeightedSummable q a) (hq : 0 ≤ q) :
    Summable (fun n => ‖weightedTerm q a n‖) := by
  simpa only [norm_weightedTerm hq] using (show Summable (absWeightedTerm q a) from ha)

lemma WeightedSummable.summable {q : ℝ} {a : ℕ → ℝ}
    (ha : WeightedSummable q a) (hq : 0 ≤ q) : Summable (weightedTerm q a) :=
  (ha.norm_summable hq).of_norm

lemma WeightedSummable.abs_tsum_le {q : ℝ} {a : ℕ → ℝ}
    (ha : WeightedSummable q a) (hq : 0 ≤ q) :
    |∑' n, weightedTerm q a n| ≤ weightedNorm q a := by
  simpa only [Real.norm_eq_abs, norm_weightedTerm hq, weightedNorm]
    using norm_tsum_le_tsum_norm (ha.norm_summable hq)

lemma WeightedSummable.prefixNorm_le {q : ℝ} {a : ℕ → ℝ}
    (ha : WeightedSummable q a) (hq : 0 ≤ q) (N : ℕ) :
    prefixNorm q a N ≤ weightedNorm q a :=
  ha.sum_le_tsum (range N) (fun n _ => absWeightedTerm_nonneg hq a n)

lemma WeightedSummable.term_le {q : ℝ} {a : ℕ → ℝ}
    (ha : WeightedSummable q a) (hq : 0 ≤ q) (n : ℕ) :
    absWeightedTerm q a n ≤ weightedNorm q a :=
  ha.le_tsum n (fun m _ => absWeightedTerm_nonneg hq a m)

/-- This is the convergence gate for a finite-prefix graph-mass estimate. -/
theorem weightedSummable_and_norm_le_of_prefix_bound {q C : ℝ} {a : ℕ → ℝ}
    (hq : 0 ≤ q) (hC : ∀ N, prefixNorm q a N ≤ C) :
    WeightedSummable q a ∧ weightedNorm q a ≤ C :=
  summable_and_tsum_le_of_prefix_bound (absWeightedTerm_nonneg hq a) hC

/-- For nonnegative counts the absolute weighted sum is the generating-function value. -/
theorem nonnegative_weighted_mass_of_prefix_bound {q C : ℝ} {a : ℕ → ℝ}
    (hq : 0 ≤ q) (ha : ∀ n, 0 ≤ a n)
    (hC : ∀ N, ∑ n ∈ range N, a n * q ^ n ≤ C) :
    Summable (fun n => a n * q ^ n) ∧ (∑' n, a n * q ^ n) ≤ C :=
  summable_and_tsum_le_of_prefix_bound (fun n => mul_nonneg (ha n) (pow_nonneg hq n)) hC

lemma WeightedSummable.mono_radius {q r : ℝ} {a : ℕ → ℝ}
    (ha : WeightedSummable r a) (hq : 0 ≤ q) (hqr : q ≤ r) : WeightedSummable q a :=
  ha.of_nonneg_of_le (absWeightedTerm_nonneg hq a) (fun n =>
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq hqr n) (abs_nonneg _))

lemma weightedNorm_mono_radius {q r : ℝ} {a : ℕ → ℝ}
    (ha : WeightedSummable r a) (hq : 0 ≤ q) (hqr : q ≤ r) :
    weightedNorm q a ≤ weightedNorm r a :=
  (ha.mono_radius hq hqr).tsum_le_tsum
    (fun n => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq hqr n) (abs_nonneg _)) ha

/-- A signed absolutely convergent family may be regrouped across two countable indices. -/
theorem signed_tsum_comm {f : ℕ → ℕ → ℝ}
    (hf : Summable (fun p : ℕ × ℕ => |f p.1 p.2|)) :
    (∑' i, ∑' j, f i j) = ∑' j, ∑' i, f i j := by
  have hs : Summable (Function.uncurry f) := by
    apply Summable.of_norm
    simpa only [Real.norm_eq_abs, Function.uncurry] using hf
  exact hs.tsum_comm.symm

/-- Regroup an absolutely convergent signed family by any fiber map. Finite
fibers may subsequently be evaluated by `tsum_fintype`. -/
theorem signed_tsum_fiberwise {ι κ : Type*} {f : ι → ℝ}
    (hf : Summable (fun i => |f i|)) (degree : ι → κ) :
    (∑' k, ∑' i : degree ⁻¹' {k}, f i) = ∑' i, f i := by
  have hs : Summable f := by
    apply Summable.of_norm
    simpa only [Real.norm_eq_abs] using hf
  exact (hs.hasSum.tsum_fiberwise degree).tsum_eq

/-- The Cauchy coefficient product, indexed by the natural-number antidiagonal. -/
def convolution (a b : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ ij ∈ antidiagonal n, a ij.1 * b ij.2

lemma convolution_eq_range (a b : ℕ → ℝ) (n : ℕ) :
    convolution a b n = ∑ i ∈ range (n + 1), a i * b (n - i) :=
  Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => a i * b j) n

lemma weightedTerm_convolution (q : ℝ) (a b : ℕ → ℝ) (n : ℕ) :
    weightedTerm q (convolution a b) n =
      convolution (weightedTerm q a) (weightedTerm q b) n := by
  unfold weightedTerm convolution
  rw [sum_mul]
  apply sum_congr rfl
  intro ij hij
  rw [← mem_antidiagonal.mp hij, pow_add]
  ring

lemma absWeightedTerm_convolution_le {q : ℝ} (hq : 0 ≤ q)
    (a b : ℕ → ℝ) (n : ℕ) :
    absWeightedTerm q (convolution a b) n ≤
      convolution (absWeightedTerm q a) (absWeightedTerm q b) n := by
  rw [← norm_weightedTerm hq, weightedTerm_convolution]
  unfold convolution
  calc
    ‖∑ ij ∈ antidiagonal n, weightedTerm q a ij.1 * weightedTerm q b ij.2‖
        ≤ ∑ ij ∈ antidiagonal n, ‖weightedTerm q a ij.1 * weightedTerm q b ij.2‖ :=
      norm_sum_le _ _
    _ ≤ ∑ ij ∈ antidiagonal n, ‖weightedTerm q a ij.1‖ * ‖weightedTerm q b ij.2‖ :=
      sum_le_sum (fun ij _ => norm_mul_le _ _)
    _ = ∑ ij ∈ antidiagonal n, absWeightedTerm q a ij.1 * absWeightedTerm q b ij.2 := by
      simp only [norm_weightedTerm hq]

lemma WeightedSummable.convolution {q : ℝ} {a b : ℕ → ℝ}
    (ha : WeightedSummable q a) (hb : WeightedSummable q b) (hq : 0 ≤ q) :
    WeightedSummable q (convolution a b) := by
  have h := summable_norm_sum_mul_antidiagonal_of_summable_norm
    (ha.norm_summable hq) (hb.norm_summable hq)
  change Summable (fun n =>
    ‖WeightedSeries.convolution (weightedTerm q a) (weightedTerm q b) n‖) at h
  change Summable (absWeightedTerm q (WeightedSeries.convolution a b))
  simpa only [← weightedTerm_convolution, norm_weightedTerm hq] using h

/-- Absolute-q submultiplicativity, with both convergence hypotheses explicit. -/
theorem weightedNorm_convolution_le {q : ℝ} {a b : ℕ → ℝ}
    (ha : WeightedSummable q a) (hb : WeightedSummable q b) (hq : 0 ≤ q) :
    weightedNorm q (convolution a b) ≤ weightedNorm q a * weightedNorm q b := by
  have hab := ha.convolution hb hq
  have hm := ha.mul_of_nonneg hb (absWeightedTerm_nonneg hq a)
    (absWeightedTerm_nonneg hq b)
  have hs := summable_sum_mul_antidiagonal_of_summable_mul hm
  have heq := ha.tsum_mul_tsum_eq_tsum_sum_antidiagonal hb hm
  exact (hab.tsum_le_tsum (absWeightedTerm_convolution_le hq a b) hs).trans_eq heq.symm

/-- Evaluation commutes with the product only after absolute convergence is proved. -/
theorem weighted_tsum_convolution {q : ℝ} {a b : ℕ → ℝ}
    (ha : WeightedSummable q a) (hb : WeightedSummable q b) (hq : 0 ≤ q) :
    (∑' n, weightedTerm q (convolution a b) n) =
      (∑' n, weightedTerm q a n) * (∑' n, weightedTerm q b n) := by
  simp only [weightedTerm_convolution, convolution]
  exact (tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
    (ha.norm_summable hq) (hb.norm_summable hq)).symm

/-- A prefix sequence is zero in degrees at least `N`. -/
def truncate (N : ℕ) (a : ℕ → ℝ) (n : ℕ) : ℝ := if n < N then a n else 0

lemma weightedSummable_truncate (q : ℝ) (a : ℕ → ℝ) (N : ℕ) :
    WeightedSummable q (truncate N a) := by
  apply summable_of_ne_finset_zero (s := range N)
  intro n hn
  simp only [mem_range, not_lt] at hn
  simp [absWeightedTerm, truncate, not_lt.mpr hn]

lemma weightedNorm_truncate (q : ℝ) (a : ℕ → ℝ) (N : ℕ) :
    weightedNorm q (truncate N a) = prefixNorm q a N := by
  unfold weightedNorm prefixNorm
  rw [tsum_eq_sum (s := range N)]
  · apply sum_congr rfl
    intro n hn
    simp [absWeightedTerm, truncate, mem_range.mp hn]
  · intro n hn
    simp only [mem_range] at hn
    simp [absWeightedTerm, truncate, hn]

lemma convolution_truncate_right_of_lt (a b : ℕ → ℝ) {n N : ℕ} (hn : n < N) :
    convolution a (truncate N b) n = convolution a b n := by
  apply sum_congr rfl
  intro ij hij
  have hij' := mem_antidiagonal.mp hij
  have hj : ij.2 < N := (hij' ▸ Nat.le_add_left ij.2 ij.1).trans_lt hn
  simp [truncate, hj]

lemma prefixNorm_convolution_truncate_right (q : ℝ) (a b : ℕ → ℝ) (N : ℕ) :
    prefixNorm q (convolution a (truncate N b)) N =
      prefixNorm q (convolution a b) N := by
  apply sum_congr rfl
  intro n hn
  simp only [absWeightedTerm, convolution_truncate_right_of_lt a b (mem_range.mp hn)]

/-- The second sequence need not converge: a product prefix only sees its prefix. -/
lemma prefixNorm_convolution_le {q : ℝ} {a : ℕ → ℝ}
    (ha : WeightedSummable q a) (hq : 0 ≤ q) (b : ℕ → ℝ) (N : ℕ) :
    prefixNorm q (convolution a b) N ≤ weightedNorm q a * prefixNorm q b N := by
  rw [← prefixNorm_convolution_truncate_right q a b N]
  calc
    prefixNorm q (convolution a (truncate N b)) N
        ≤ weightedNorm q (convolution a (truncate N b)) :=
      (ha.convolution (weightedSummable_truncate q b N) hq).prefixNorm_le hq N
    _ ≤ weightedNorm q a * weightedNorm q (truncate N b) :=
      weightedNorm_convolution_le ha (weightedSummable_truncate q b N) hq
    _ = weightedNorm q a * prefixNorm q b N := by rw [weightedNorm_truncate]

lemma prefixNorm_add_le {q : ℝ} (hq : 0 ≤ q) (a b : ℕ → ℝ) (N : ℕ) :
    prefixNorm q (fun n => a n + b n) N ≤ prefixNorm q a N + prefixNorm q b N := by
  unfold prefixNorm absWeightedTerm
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro n _
  simpa only [add_mul] using mul_le_mul_of_nonneg_right (abs_add_le (a n) (b n))
    (pow_nonneg hq n)

/-- Finite coefficient support is an explicit convergence witness. -/
theorem weightedSummable_and_norm_eq_prefix_of_support {q : ℝ} {a : ℕ → ℝ}
    {N : ℕ} (hN : ∀ n, N ≤ n → a n = 0) :
    WeightedSummable q a ∧ weightedNorm q a = prefixNorm q a N := by
  have ha : truncate N a = a := by
    funext n
    by_cases hn : n < N
    · simp [truncate, hn]
    · simp [truncate, hn, hN n (Nat.le_of_not_gt hn)]
  constructor
  · simpa only [ha] using weightedSummable_truncate q a N
  · simpa only [ha] using weightedNorm_truncate q a N

/-- Finite-numerator conversion does not substitute the potentially divergent
value of the source series. Only its finite prefix occurs on the right. -/
theorem finite_numerator_norm_le {q : ℝ} {a b : ℕ → ℝ} {N : ℕ}
    (hq : 0 ≤ q) (ha : WeightedSummable q a)
    (hN : ∀ n, N ≤ n → convolution a b n = 0) :
    WeightedSummable q (convolution a b) ∧
      weightedNorm q (convolution a b) ≤ weightedNorm q a * prefixNorm q b N := by
  obtain ⟨hs, heq⟩ := weightedSummable_and_norm_eq_prefix_of_support (q := q) hN
  exact ⟨hs, heq.trans_le (prefixNorm_convolution_le ha hq b N)⟩

/-- A residual equation proves convergence without presupposing convergence of
its solution. Finite prefixes are bounded first, then the nonnegative summation
criterion supplies the infinite tail. -/
theorem weightedSummable_and_norm_le_of_residual {q : ℝ} {v e x : ℕ → ℝ}
    (hq : 0 ≤ q) (hv : WeightedSummable q v) (he : WeightedSummable q e)
    (hsmall : weightedNorm q e < 1)
    (hres : ∀ n, x n = v n + convolution e x n) :
    WeightedSummable q x ∧
      weightedNorm q x ≤ weightedNorm q v / (1 - weightedNorm q e) := by
  have hden : 0 < 1 - weightedNorm q e := sub_pos.mpr hsmall
  apply weightedSummable_and_norm_le_of_prefix_bound hq
  intro N
  have hprefix : prefixNorm q x N ≤
      weightedNorm q v + weightedNorm q e * prefixNorm q x N := by
    calc
      prefixNorm q x N = prefixNorm q (fun n => v n + convolution e x n) N := by
        congr 1
        funext n
        exact hres n
      _ ≤ prefixNorm q v N + prefixNorm q (convolution e x) N :=
        prefixNorm_add_le hq v (convolution e x) N
      _ ≤ weightedNorm q v + weightedNorm q e * prefixNorm q x N :=
        add_le_add (hv.prefixNorm_le hq N) (prefixNorm_convolution_le he hq x N)
  apply (le_div_iff₀ hden).2
  nlinarith

/-- The finite Cauchy product agrees with the formal power-series product. -/
lemma coeff_mul_eq_convolution (a b : PowerSeries ℝ) (n : ℕ) :
    PowerSeries.coeff n (a * b) =
      convolution (fun i => PowerSeries.coeff i a) (fun j => PowerSeries.coeff j b) n :=
  PowerSeries.coeff_mul n a b

/-- Original fixed-factor reciprocal criterion. A finite polynomial `V` and
residual `1 - K*V` with absolute-q norm below one prove the full reciprocal norm,
including its infinite tail. The coefficient identity is proved in the actual
formal power-series ring, not postulated as a numerical certificate. -/
theorem powerSeries_inverse_of_residual {q : ℝ} (K V : PowerSeries ℝ)
    (hq : 0 ≤ q) (hK : PowerSeries.constantCoeff K ≠ 0)
    (hV : WeightedSummable q (fun n => PowerSeries.coeff n V))
    (hE : WeightedSummable q (fun n => PowerSeries.coeff n (1 - K * V)))
    (hsmall : weightedNorm q (fun n => PowerSeries.coeff n (1 - K * V)) < 1) :
    WeightedSummable q (fun n => PowerSeries.coeff n K⁻¹) ∧
      weightedNorm q (fun n => PowerSeries.coeff n K⁻¹) ≤
        weightedNorm q (fun n => PowerSeries.coeff n V) /
          (1 - weightedNorm q (fun n => PowerSeries.coeff n (1 - K * V))) := by
  apply weightedSummable_and_norm_le_of_residual hq hV hE hsmall
  intro n
  have hid : K⁻¹ = V + (1 - K * V) * K⁻¹ := by
    rw [sub_mul, one_mul, mul_comm K V, mul_assoc, PowerSeries.mul_inv_cancel K hK,
      mul_one]
    ring
  have hc := congrArg (PowerSeries.coeff n) hid
  simpa only [map_add, coeff_mul_eq_convolution] using hc

end WeightedSeries
end SubmittedGenus
