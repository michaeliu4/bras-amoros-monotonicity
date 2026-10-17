import Results.Genus.CapFiveMass.General.Mass
import Results.Genus.CapFiveMass.General.FourthNorm

/-! Literal fourth-norm and k=sqrt(a/b) interfaces for mass:five. -/
noncomputable section
open scoped BigOperators
namespace SubmittedGenus.CapFiveMass.General

lemma fourthTrace_nonneg (t : ℕ) {z : ℝ} (hz : 0 ≤ z) : 0 ≤ fourthTrace t z := by
  unfold fourthTrace
  apply Finset.sum_nonneg; intro i _
  apply Finset.sum_nonneg; intro j _
  apply Finset.sum_nonneg; intro k _
  apply Finset.sum_nonneg; intro l _
  split_ifs
  · exact pow_nonneg hz _
  · rfl

lemma fourthNorm_pow_four (t : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    fourthNorm t z ^ 4 = fourthTrace t z := by
  exact Real.rpow_inv_natCast_pow (fourthTrace_nonneg t hz) (by decide : (4 : ℕ) ≠ 0)

lemma trace_bound_of_fourthNorm {t : ℕ} {z a : ℝ} (hz : 0 ≤ z)
    (h : fourthNorm t z ≤ a) : fourthTrace t z ≤ a ^ 4 := by
  rw [← fourthNorm_pow_four t hz]
  exact pow_le_pow_left₀ (Real.rpow_nonneg (fourthTrace_nonneg t hz) _) h 4

lemma rootMajorant_original (H : Control) :
    rootMajorant H =
      H.z ^ 10 * (alphabetMass 5 H.z / H.b) * (Real.sqrt (H.a / H.b))⁻¹ /
        ((1 - H.b) * (1 - H.b * Real.sqrt (H.a / H.b)) * (1 - H.a)) := by
  have hk : Real.sqrt (H.a / H.b) ^ 2 = H.a / H.b :=
    Real.sq_sqrt (div_nonneg H.a_pos.le H.b_pos.le)
  have he_sq : (H.b * Real.sqrt (H.a / H.b)) ^ 2 = mixedRoot H ^ 2 := by
    rw [mul_pow, hk, mixedRoot_sq]
    field_simp
  have he : H.b * Real.sqrt (H.a / H.b) = mixedRoot H :=
    (sq_eq_sq₀ (mul_nonneg H.b_pos.le (Real.sqrt_nonneg _)) (mixedRoot_pos H).le).mp he_sq
  unfold rootMajorant
  rw [← he]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Original display with independent real z,a5,b4 and exactly the stated
fourth-norm, alphabet and endpoint hypotheses, at a positive mass radius. -/
theorem mass_five_general (z a b : ℝ) (hz : 0 < z)
    (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hD5 : fourthNorm 5 z ≤ a) (hD4 : fourthNorm 4 z ≤ b)
    (hs : b ≤ alphabetMass 5 z) (hh5 : strongEndpoint z ≤ a) (hh4 : carryEndpoint z ≤ b) :
    Summable (fun g => (count g : ℝ) * z ^ g) ∧
      mass z ≤ z ^ 10 * (alphabetMass 5 z / b) * (Real.sqrt (a / b))⁻¹ /
        ((1 - b) * (1 - b * Real.sqrt (a / b)) * (1 - a)) := by
  let H : Control := ⟨z, a, b, hz, ha, hab, hb, hs,
    trace_bound_of_fourthNorm hz.le hD5, trace_bound_of_fourthNorm hz.le hD4, hh5, hh4⟩
  have h := genuine_mass_bound H
  rw [rootMajorant_original H] at h
  exact h

end SubmittedGenus.CapFiveMass.General
