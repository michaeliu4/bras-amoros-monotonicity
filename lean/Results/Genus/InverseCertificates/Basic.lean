import Results.Genus.WeightedSeries
import Results.Genus.FiniteArithmetic

/-! Finite integer-coefficient certificates and their absolute-q interpretation. -/
noncomputable section
open scoped BigOperators
namespace SubmittedGenus.InverseCertificates
open WeightedSeries

def intSeries (a : List ℤ) : PowerSeries ℝ :=
  PowerSeries.mk (fun n => (a.getD n 0 : ℝ))

@[simp] lemma coeff_intSeries (a : List ℤ) (n : ℕ) :
    PowerSeries.coeff n (intSeries a) = (a.getD n 0 : ℝ) := PowerSeries.coeff_mk _ _

lemma getD_zero_of_length_le (a : List ℤ) {n : ℕ} (hn : a.length ≤ n) :
    a.getD n 0 = 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hn]

lemma intSeries_support (a : List ℤ) (n : ℕ) (hn : a.length ≤ n) :
    PowerSeries.coeff n (intSeries a) = 0 := by
  rw [coeff_intSeries, getD_zero_of_length_le a hn, Int.cast_zero]

lemma intSeries_summable (a : List ℤ) (q : ℝ) :
    WeightedSummable q (fun n => PowerSeries.coeff n (intSeries a)) :=
  (weightedSummable_and_norm_eq_prefix_of_support (intSeries_support a)).1

/-- Horner evaluation of the absolute coefficient polynomial. -/
def realHorner (q : ℝ) : List ℤ → ℝ
  | [] => 0
  | a :: as => |(a : ℝ)| + q * realHorner q as

lemma prefix_eq_realHorner (a : List ℤ) (q : ℝ) :
    (∑ n ∈ Finset.range a.length, |(a.getD n 0 : ℝ)| * q ^ n) = realHorner q a := by
  induction a with
  | nil => simp [realHorner]
  | cons a as ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one]
    rw [show (∑ k ∈ Finset.range as.length, |(as.getD k 0 : ℝ)| * q ^ (k + 1)) =
        q * ∑ k ∈ Finset.range as.length, |(as.getD k 0 : ℝ)| * q ^ k by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [pow_succ]
      ring]
    rw [ih]
    simp [realHorner, add_comm]

lemma intSeries_norm (a : List ℤ) (q : ℝ) :
    weightedNorm q (fun n => PowerSeries.coeff n (intSeries a)) = realHorner q a := by
  rw [(weightedSummable_and_norm_eq_prefix_of_support (q := q) (intSeries_support a)).2]
  simpa only [prefixNorm, absWeightedTerm, coeff_intSeries] using prefix_eq_realHorner a q

/-- The finite convolution beyond the sum of the input degrees vanishes. -/
lemma convolution_support (a b : List ℤ) (n : ℕ) (hn : a.length + b.length - 1 ≤ n) :
    FiniteArithmetic.convolution (fun i => a.getD i 0) (fun i => b.getD i 0) n = 0 := by
  unfold FiniteArithmetic.convolution
  apply Finset.sum_eq_zero
  intro i hi
  change a.getD i 0 * b.getD (n - i) 0 = 0
  by_cases ha : a.length ≤ i
  · rw [getD_zero_of_length_le a ha, zero_mul]
  · have hb : b.length ≤ n - i := by omega
    rw [getD_zero_of_length_le b hb, mul_zero]

/-- Check every possibly nonzero coefficient, rather than a truncated residual. -/
def ResidualCheck (a b e : List ℤ) : Prop :=
  ∀ n : Fin (a.length + b.length), e.getD n 0 =
    (if n.val = 0 then 1 else 0) -
      FiniteArithmetic.convolution (fun i => a.getD i 0) (fun i => b.getD i 0) n

instance (a b e : List ℤ) : Decidable (ResidualCheck a b e) :=
  inferInstanceAs (Decidable (∀ n : Fin (a.length + b.length), _))

lemma residualCheck_sound (a b e : List ℤ)
    (hlen : e.length ≤ a.length + b.length) (hpos : 0 < a.length + b.length)
    (h : ResidualCheck a b e) :
    1 - intSeries a * intSeries b = intSeries e := by
  apply PowerSeries.ext
  intro n
  rw [map_sub, FiniteArithmetic.coeff_mul_eq_convolution]
  simp only [PowerSeries.coeff_one, coeff_intSeries]
  have he : e.getD n 0 = (if n = 0 then 1 else 0) -
      FiniteArithmetic.convolution (fun i => a.getD i 0) (fun i => b.getD i 0) n := by
    by_cases hn : n < a.length + b.length
    · exact h ⟨n, hn⟩
    · rw [getD_zero_of_length_le e (by omega), convolution_support a b n (by omega)]
      simp [show n ≠ 0 by omega]
  have hr := congrArg (fun z : ℤ => (z : ℝ)) he
  push_cast at hr
  simpa [FiniteArithmetic.convolution] using hr.symm

/-- Exact rational absolute norm of a finite coefficient list. -/
def ratHorner (q : ℚ) : List ℤ → ℚ
  | [] => 0
  | a :: as => |(a : ℚ)| + q * ratHorner q as

lemma realHorner_ratCast (a : List ℤ) (q : ℚ) :
    realHorner (q : ℝ) a = (ratHorner q a : ℝ) := by
  induction a with
  | nil => simp [realHorner, ratHorner]
  | cons a as ih => simp [realHorner, ratHorner, ih, Rat.cast_abs]

lemma intSeries_norm_rat (a : List ℤ) (q : ℚ) :
    weightedNorm (q : ℝ) (fun n => PowerSeries.coeff n (intSeries a)) =
      (ratHorner q a : ℝ) := by
  rw [intSeries_norm, realHorner_ratCast]

end SubmittedGenus.InverseCertificates
