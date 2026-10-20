import Results.Genus.WeightedSeries
import Results.Genus.FiniteArithmetic.CapacityW

namespace SubmittedGenus.FiniteArithmetic.Analytic

open PowerSeries
open scoped BigOperators

noncomputable section

def realCoeff (f : PowerSeries ℤ) (n : ℕ) : ℝ := ((coeff n f : ℤ) : ℝ)

def SummableAt (r : ℝ) (f : PowerSeries ℤ) : Prop :=
  WeightedSeries.WeightedSummable r (realCoeff f)

def normAt (r : ℝ) (f : PowerSeries ℤ) : ℝ :=
  WeightedSeries.weightedNorm r (realCoeff f)

@[simp] theorem realCoeff_add (a b : PowerSeries ℤ) (n : ℕ) :
    realCoeff (a + b) n = realCoeff a n + realCoeff b n := by simp [realCoeff]

theorem realCoeff_mul (a b : PowerSeries ℤ) :
    realCoeff (a * b) = WeightedSeries.convolution (realCoeff a) (realCoeff b) := by
  funext n
  simp [realCoeff, coeff_mul, WeightedSeries.convolution]

theorem normAt_nonneg {r : ℝ} (hr : 0 ≤ r) (f : PowerSeries ℤ) : 0 ≤ normAt r f :=
  WeightedSeries.weightedNorm_nonneg hr _

theorem add_bound {r A B : ℝ} {a b : PowerSeries ℤ} (hr : 0 ≤ r)
    (ha : SummableAt r a ∧ normAt r a ≤ A) (hb : SummableAt r b ∧ normAt r b ≤ B) :
    SummableAt r (a + b) ∧ normAt r (a + b) ≤ A + B := by
  apply WeightedSeries.weightedSummable_and_norm_le_of_prefix_bound hr
  intro N
  have he : realCoeff (a + b) = fun n => realCoeff a n + realCoeff b n := by
    funext n
    exact realCoeff_add a b n
  rw [he]
  exact (WeightedSeries.prefixNorm_add_le hr _ _ N).trans
    (add_le_add ((ha.1.prefixNorm_le hr N).trans ha.2) ((hb.1.prefixNorm_le hr N).trans hb.2))

theorem mul_bound {r A B : ℝ} {a b : PowerSeries ℤ} (hr : 0 ≤ r)
    (ha : SummableAt r a ∧ normAt r a ≤ A) (hb : SummableAt r b ∧ normAt r b ≤ B) :
    SummableAt r (a * b) ∧ normAt r (a * b) ≤ A * B := by
  have hA : 0 ≤ A := (normAt_nonneg hr a).trans ha.2
  constructor
  · change WeightedSeries.WeightedSummable r (realCoeff (a * b))
    rw [realCoeff_mul]
    exact ha.1.convolution hb.1 hr
  · change WeightedSeries.weightedNorm r (realCoeff (a * b)) ≤ _
    rw [realCoeff_mul]
    exact (WeightedSeries.weightedNorm_convolution_le ha.1 hb.1 hr).trans
      (mul_le_mul ha.2 hb.2 (normAt_nonneg hr b) hA)

/-- A source equation with a small absolutely convergent denominator tail
proves convergence of the source itself, without assuming its evaluation. -/
theorem geometric_bound {r A B : ℝ} {a b f : PowerSeries ℤ} (hr : 0 ≤ r)
    (ha : SummableAt r a ∧ normAt r a ≤ A) (hb : SummableAt r b ∧ normAt r b ≤ B)
    (hB : B < 1) (hf : (1 - b) * f = a) :
    SummableAt r f ∧ normAt r f ≤ A / (1 - B) := by
  have he : f = a + b * f := by rw [← hf]; ring
  have hs := WeightedSeries.weightedSummable_and_norm_le_of_residual hr ha.1 hb.1
    (hb.2.trans_lt hB) (x := realCoeff f) (by
      intro n
      conv_lhs => rw [he]
      rw [realCoeff_add, realCoeff_mul])
  refine ⟨hs.1, hs.2.trans ?_⟩
  apply div_le_div₀
  · exact (normAt_nonneg hr a).trans ha.2
  · exact ha.2
  · exact sub_pos.mpr hB
  · exact sub_le_sub_left hb.2 1

#print axioms geometric_bound

end
end SubmittedGenus.FiniteArithmetic.Analytic
