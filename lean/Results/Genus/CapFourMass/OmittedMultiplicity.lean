import Results.Genus.CapFourMass.PureTailSeries

/-! The original full-feedback omitted tail as a convergent double series over
all omitted pivots and every enlarged multiplicity m≥p+1. -/
noncomputable section
open scoped BigOperators
namespace SubmittedGenus.CapFourMass

def pureOmittedScale (i : TailIndex) : ℝ :=
  radius^8*alphabetMass*feedbackT/eta*eta^(i.pivot.a+i.pivot.b)*
    sigma^(i.pivot.b-i.pivot.r)*tBound^i.gap

lemma pureOmittedScale_nonneg (i : TailIndex) : 0≤pureOmittedScale i := by
  have hT : 0≤feedbackT := div_nonneg feedbackGamma_bounds.1.le feedbackBeta_bounds.1.le
  unfold pureOmittedScale
  exact mul_nonneg (mul_nonneg (mul_nonneg
    (div_nonneg (mul_nonneg (mul_nonneg (pow_nonneg radius_pos.le _)
      (le_of_lt (lt_trans zero_lt_one alphabetMass_gt_one))) hT) eta_bounds.1.le)
    (pow_nonneg eta_bounds.1.le _)) (pow_nonneg sigma_bounds.1.le _))
    (pow_nonneg (lt_trans zero_lt_one tBound_gt_one).le _)

def pureOmittedFamily (P : ℕ) (ij : TailIndex×ℕ) : ℝ :=
  if P < ij.1.pivot.p then pureOmittedScale ij.1*pureMultiplicityTerm ij.1.pivot.p ij.2 else 0

lemma pureOmittedFamily_nonneg (P : ℕ) (ij : TailIndex×ℕ) : 0≤pureOmittedFamily P ij := by
  unfold pureOmittedFamily
  split_ifs
  · exact mul_nonneg (pureOmittedScale_nonneg _) (pureMultiplicity_nonneg _ _)
  · rfl

lemma pureOmitted_row_hasSum (P : ℕ) (i : TailIndex) :
    HasSum (fun j : ℕ => pureOmittedFamily P (i,j)) (pureOmittedTerm P i) := by
  by_cases hp : P < i.pivot.p
  · simpa only [pureOmittedFamily,pureOmittedTerm,hp,if_true,pureOmittedScale]
      using (purePivotMultiplicity_hasSum i.pivot).mul_left (pureOmittedScale i)
  · simp only [pureOmittedFamily,pureOmittedTerm,hp,if_false]
    exact hasSum_zero

/-- Every term is nonnegative, and summation over all added short and original
long multiplicities equals the submitted full-feedback rational expression. -/
theorem pureOmittedFamily_hasSum (P : ℕ) :
    HasSum (pureOmittedFamily P) (pureTailExpression P) := by
  have hrow : (fun i : TailIndex => ∑' j : ℕ,pureOmittedFamily P (i,j))=pureOmittedTerm P :=
    funext (fun i => (pureOmitted_row_hasSum P i).tsum_eq)
  have hs : Summable (pureOmittedFamily P) :=
    (summable_prod_of_nonneg (pureOmittedFamily_nonneg P)).mpr
      ⟨fun i => (pureOmitted_row_hasSum P i).summable, by
        rw [hrow]
        exact (pureOmitted_hasSum P).summable⟩
  have he : (∑' ij,pureOmittedFamily P ij)=pureTailExpression P := by
    rw [hs.tsum_prod,hrow]
    exact (pureOmitted_hasSum P).tsum_eq
  exact he ▸ hs.hasSum

/-- Literal original signed feedback exponent at multiplicity m=p+1+j. -/
lemma pureOmittedFamily_source (P : ℕ) (i : TailIndex) (j : ℕ) :
    pureOmittedFamily P (i,j)=
      if P < i.pivot.p then
        pureOmittedScale i*lambdaBound^(i.pivot.p+j-2)*
          feedbackBeta^((((i.pivot.p+j)/2:ℕ):ℤ)-(i.pivot.p:ℤ))
      else 0 := by
  unfold pureOmittedFamily pureMultiplicityTerm
  split_ifs <;> first | ring | rfl

end SubmittedGenus.CapFourMass
