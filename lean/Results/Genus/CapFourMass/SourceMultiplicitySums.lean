import Results.Genus.CapFourMass.SourceMixed

/-! Actual source pure/mixed sums over every long multiplicity, from precisely the original finite bases. -/
noncomputable section
open scoped BigOperators
namespace SubmittedGenus.CapFourMass

/-- N=m-r with the first long multiplicity m=2p+1, p=r+d. -/
def longTailN (r d n : ℕ) : ℕ := r+2*d+1+n
def longMultiplicity (r d n : ℕ) : ℕ := r+longTailN r d n

lemma longTailN_large (r d n : ℕ) : r+2*d<longTailN r d n := by
  unfold longTailN
  omega
lemma longMultiplicity_eq (r d n : ℕ) : longMultiplicity r d n=2*(r+d)+1+n := by
  unfold longMultiplicity longTailN
  ring
lemma longTailN_add (r d n k : ℕ) : longTailN r d (n+k)=longTailN r d n+k := by
  unfold longTailN
  omega
lemma longMultiplicity_add (r d n k : ℕ) : longMultiplicity r d (n+k)=longMultiplicity r d n+k := by
  unfold longMultiplicity longTailN
  omega

/-- Exactly K_m times the normalized actual pure source. -/
def sourcePureSeries (r d n : ℕ) : ℝ :=
  normalizationK (longMultiplicity r d n) r (r+d)*
    normalizedMass (longMultiplicity r d n)
      (sourcePure r (longTailN r d n) d (by have:=longTailN_large r d n; omega))

/-- Exactly K_m times the normalized actual mixed source. -/
def sourceMixedSeries (r d n : ℕ) : ℝ :=
  normalizationK (longMultiplicity r d n) r (r+d)*
    normalizedMass (longMultiplicity r d n)
      (sourceMixed r (longTailN r d n) d (by have:=longTailN_large r d n; omega))

lemma normalizationK_nonneg (m r p : ℕ) : 0 ≤ normalizationK m r p := by
  unfold normalizationK
  have hT : 0 ≤ feedbackT := div_nonneg feedbackGamma_bounds.1.le feedbackBeta_bounds.1.le
  exact div_nonneg (pow_nonneg hT _) (pow_nonneg normalizer_bounds.1.le _)

lemma sourcePureSeries_nonneg (r d n : ℕ) : 0 ≤ sourcePureSeries r d n := by
  unfold sourcePureSeries normalizedMass
  exact mul_nonneg (normalizationK_nonneg _ _ _)
    (mul_nonneg (pow_nonneg normalizer_bounds.1.le _) (sourcePure_nonneg _ _ _ _))
lemma sourceMixedSeries_nonneg (r d n : ℕ) : 0 ≤ sourceMixedSeries r d n := by
  unfold sourceMixedSeries normalizedMass
  exact mul_nonneg (normalizationK_nonneg _ _ _)
    (mul_nonneg (pow_nonneg normalizer_bounds.1.le _) (sourceMixed_nonneg _ _ _ _))

lemma sourcePureSeries_step (r d : ℕ) (hd : 0<d) (n : ℕ) :
    sourcePureSeries r d (n+2)=(normalizer*lam)^2*sourcePureSeries r d n := by
  unfold sourcePureSeries
  simp only [longMultiplicity_add,longTailN_add]
  rw [normalizationK_period_two _ r (r+d) (by rw [longMultiplicity_eq]; omega)]
  have he:=normalized_sourcePure_two_step r (longTailN r d n) d hd
    (by have:=longTailN_large r d n; omega) (by have:=longTailN_large r d n; omega)
  simp only [longMultiplicity,Nat.add_assoc] at he ⊢
  rw [he]
  ring

lemma sourceMixedSeries_step (r d : ℕ) (n : ℕ) :
    sourceMixedSeries r d (n+2*d) ≤
      (normalizer*lam)^(2*d)*rho^2*sourceMixedSeries r d n := by
  unfold sourceMixedSeries
  simp only [longMultiplicity_add,longTailN_add]
  rw [normalizationK_period_even _ r (r+d) d (by rw [longMultiplicity_eq]; omega)]
  have he:=normalized_sourceMixed_two_gap r (longTailN r d n) d
    (by have:=longTailN_large r d n; omega) (by have:=longTailN_large r d n; omega)
  simp only [longMultiplicity,Nat.add_assoc] at he ⊢
  exact (mul_le_mul_of_nonneg_left he (normalizationK_nonneg _ _ _)).trans_eq (by ring)

/-- The two original pure bases give the complete infinite source sum. -/
theorem sourcePureSeries_hasSum (r d : ℕ) (hd : 0<d) :
    HasSum (sourcePureSeries r d)
      ((∑ s : Fin 2,sourcePureSeries r d s.val)/(1-(normalizer*lam)^2)) :=
  complete_progression_hasSum 2 pure_progression_ratio_bounds.1 pure_progression_ratio_bounds.2
    (sourcePureSeries r d) (sourcePureSeries_nonneg r d) (sourcePureSeries_step r d hd)

/-- Precisely 2d original mixed bases bound every remaining multiplicity. -/
theorem sourceMixedSeries_complete (r d : ℕ) (hd : 0<d) :
    Summable (sourceMixedSeries r d) ∧
      (∑' n,sourceMixedSeries r d n) ≤
      (∑ s : Fin (2*d),sourceMixedSeries r d s.val)/(1-(normalizer*lam)^(2*d)*rho^2) := by
  letI : NeZero (2*d) := ⟨by omega⟩
  exact complete_progression_le (2*d) (mixed_progression_ratio_bounds d).1
    (mixed_progression_ratio_bounds d).2 (sourceMixedSeries r d) (sourceMixedSeries_nonneg r d)
    (sourceMixedSeries_step r d)

end SubmittedGenus.CapFourMass
