import Results.Genus.CapFourMass.Normalization
import Results.Genus.CapFourMass.ProgressionSums

/-! Exact source normalization used by the finite pure and mixed bases. -/
noncomputable section
namespace SubmittedGenus.CapFourMass

/-- Original integer count of ordinary self-pair centers. -/
def feedbackCount (m p : ℕ) : ℕ := (m-1)/2-p
def feedbackExponent (r p : ℕ) : ℕ := 1+(p-r)/3

def normalizationK (m r p : ℕ) : ℝ :=
  feedbackT^(feedbackExponent r p)/normalizer^(2*p+(m-1)%2)
def normalizedMass (m : ℕ) (X : ℝ) : ℝ := normalizer^(m-1)*X

lemma normalization_exponents {m p : ℕ} (hm : 2*p < m) :
    m-1=2*feedbackCount m p+(2*p+(m-1)%2) := by
  unfold feedbackCount
  omega

lemma normalizationK_times (m r p : ℕ) (hm : 2*p < m) (X : ℝ) :
    normalizationK m r p*normalizedMass m X =
      feedbackT^(feedbackExponent r p)*normalizer^(2*feedbackCount m p)*X := by
  unfold normalizationK normalizedMass
  have hpow : normalizer^(m-1) =
      normalizer^(2*feedbackCount m p)*normalizer^(2*p+(m-1)%2) :=
    (congrArg (fun n : ℕ => normalizer^n) (normalization_exponents hm)).trans (pow_add _ _ _)
  rw [hpow]
  have hw : normalizer^(2*p+(m-1)%2) ≠ 0 := pow_ne_zero _ (ne_of_gt normalizer_bounds.1)
  field_simp

/-- Source-independent scalar part of (mass:normalized-majorization).
The original β^N is preserved until this proved enlargement is applied. -/
theorem normalized_majorization (m r p : ℕ) (hm : 2*p < m) (X : ℝ) (hX : 0 ≤ X) :
    feedbackT^(feedbackExponent r p)*feedbackBeta^(feedbackCount m p)*X ≤
      normalizationK m r p*normalizedMass m X := by
  rw [normalizationK_times m r p hm X]
  have hT : 0 ≤ feedbackT := div_nonneg feedbackGamma_bounds.1.le feedbackBeta_bounds.1.le
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (feedback_power_le_normalized _) (pow_nonneg hT _)) hX

lemma normalizationK_period_two (m r p : ℕ) (hm : 1 ≤ m) :
    normalizationK (m+2) r p=normalizationK m r p := by
  unfold normalizationK
  congr 2
  omega
lemma normalizationK_period_even (m r p d : ℕ) (hm : 1 ≤ m) :
    normalizationK (m+2*d) r p=normalizationK m r p := by
  unfold normalizationK
  congr 2
  omega

lemma normalized_pure_step (P : ℕ → ℝ) (m : ℕ) (hm : 1 ≤ m)
    (hP : P (m+2)=lam^2*P m) :
    normalizedMass (m+2) (P (m+2)) = (normalizer*lam)^2*normalizedMass m (P m) := by
  unfold normalizedMass
  rw [hP,show m+2-1=(m-1)+2 by omega,pow_add,mul_pow]
  ring

lemma normalized_mixed_step (M : ℕ → ℝ) (m d : ℕ) (hm : 1 ≤ m)
    (hM : M (m+2*d) ≤ lam^(2*d)*rho^2*M m) :
    normalizedMass (m+2*d) (M (m+2*d)) ≤
      (normalizer*lam)^(2*d)*rho^2*normalizedMass m (M m) := by
  unfold normalizedMass
  have h := mul_le_mul_of_nonneg_left hM (pow_nonneg normalizer_bounds.1.le (m+2*d-1))
  rw [show m+2*d-1=(m-1)+2*d by omega,pow_add] at h ⊢
  simpa only [mul_pow,mul_assoc,mul_left_comm,mul_comm] using h

lemma pure_progression_ratio_bounds :
    0 ≤ (normalizer*lam)^2 ∧ (normalizer*lam)^2 < 1 := by
  constructor
  · exact sq_nonneg _
  · have hp : 0 ≤ normalizer*lam := mul_nonneg normalizer_bounds.1.le lam_pos.le
    have hlt := normalizer_lam_lt_one
    nlinarith

lemma mixed_progression_ratio_bounds (d : ℕ) :
    0 ≤ (normalizer*lam)^(2*d)*rho^2 ∧ (normalizer*lam)^(2*d)*rho^2 < 1 := by
  have hp : 0 ≤ normalizer*lam := mul_nonneg normalizer_bounds.1.le lam_pos.le
  have hpow : (normalizer*lam)^(2*d) ≤ 1 := pow_le_one₀ hp normalizer_lam_lt_one.le
  have hρ := rho_bounds
  have hρsq : rho^2 < 1 := by nlinarith
  exact ⟨mul_nonneg (pow_nonneg hp _) (sq_nonneg _),
    (mul_le_of_le_one_left (sq_nonneg rho) hpow).trans_lt hρsq⟩

end SubmittedGenus.CapFourMass
