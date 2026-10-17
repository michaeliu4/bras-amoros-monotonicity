import Results.Genus.CapFourMass.NormalizedFeedback

/-! Exact complete multiplicity sum used in the original pure omitted sector. -/
noncomputable section
open scoped BigOperators
namespace SubmittedGenus.CapFourMass

/-- m=p+1+j. The feedback exponent is genuinely signed on the added short
range; replacing it by truncated natural subtraction would be incorrect. -/
def pureMultiplicityTerm (p j : ℕ) : ℝ :=
  lambdaBound^(p+j-2)*feedbackBeta^((((p+j)/2 : ℕ) : ℤ)-(p:ℤ))

def pureParityOne : ℝ := lambdaBound^(-2:ℤ)*pureJ+lambdaBound^(-1:ℤ)
def pureParityTwo : ℝ := (lambdaBound^(-2:ℤ)+lambdaBound^(-1:ℤ))*pureJ

lemma pureMultiplicity_nonneg (p j : ℕ) : 0 ≤ pureMultiplicityTerm p j := by
  unfold pureMultiplicityTerm
  exact mul_nonneg (pow_nonneg lambdaBound_pos.le _) (zpow_pos feedbackBeta_bounds.1 _).le

lemma pureMultiplicity_step (p : ℕ) (hp : 2 ≤ p) (j : ℕ) :
    pureMultiplicityTerm p (j+2) = pureJ*pureMultiplicityTerm p j := by
  have he : (((p+(j+2))/2 : ℕ) : ℤ)-(p:ℤ) = (((p+j)/2 : ℕ) : ℤ)-(p:ℤ)+1 := by omega
  have hL : p+(j+2)-2=(p+j-2)+2 := by omega
  unfold pureMultiplicityTerm
  rw [he,hL,pow_add,zpow_add₀ (ne_of_gt feedbackBeta_bounds.1),zpow_one,pureJ]
  ring

lemma pureMultiplicity_hasSum_bases (p : ℕ) (hp : 2 ≤ p) :
    HasSum (pureMultiplicityTerm p)
      ((pureMultiplicityTerm p 0+pureMultiplicityTerm p 1)/(1-pureJ)) := by
  have h := complete_progression_hasSum 2 pureJ_bounds.1.le pureJ_bounds.2
    (pureMultiplicityTerm p) (pureMultiplicity_nonneg p) (pureMultiplicity_step p hp)
  simpa only [Fin.sum_univ_succ,Fin.val_zero,Fin.val_succ,Finset.univ_eq_empty,
    Finset.sum_empty,add_zero] using h

lemma pureMultiplicity_odd_bases (b : ℕ) (hb : 1 ≤ b) :
    pureMultiplicityTerm (2*b+1) 0+pureMultiplicityTerm (2*b+1) 1 =
      feedbackBeta^(-1:ℤ)*(pureJ*feedbackBeta^(-2:ℤ))^b*pureParityOne := by
  have hL : lambdaBound ≠ 0 := ne_of_gt lambdaBound_pos
  have hβ : feedbackBeta ≠ 0 := ne_of_gt feedbackBeta_bounds.1
  have he0 : (2*b+1+0)/2=b := by omega
  have he1 : (2*b+1+1)/2=b+1 := by omega
  have hLe0 : 2*b+1+0-2=(2*b-1) := by omega
  have hLe1 : 2*b+1+1-2=2*b := by omega
  have hLp : lambdaBound^(2*b-1)*lambdaBound=lambdaBound^(2*b) := by
    rw [← pow_succ,show 2*b-1+1=2*b by omega]
  unfold pureMultiplicityTerm
  rw [zpow_natCast_sub_natCast₀ hβ,zpow_natCast_sub_natCast₀ hβ,he0,he1,hLe0,hLe1]
  simp only [pureParityOne,pureJ,zpow_neg,zpow_ofNat,mul_pow,pow_add,pow_one,
    pow_mul,pow_succ]
  simp only [div_pow,inv_pow,one_pow,← pow_mul,Nat.mul_comm b 2]
  field_simp
  simp only [Nat.zero_mul,pow_zero,one_mul,mul_one,← pow_mul,Nat.mul_comm b 2]
  linear_combination feedbackBeta^(2*b)*hLp

lemma pureMultiplicity_even_bases (b : ℕ) :
    pureMultiplicityTerm (2*b+2) 0+pureMultiplicityTerm (2*b+2) 1 =
      feedbackBeta^(-2:ℤ)*(pureJ*feedbackBeta^(-2:ℤ))^b*pureParityTwo := by
  have hL : lambdaBound ≠ 0 := ne_of_gt lambdaBound_pos
  have hβ : feedbackBeta ≠ 0 := ne_of_gt feedbackBeta_bounds.1
  have he0 : (2*b+2+0)/2=b+1 := by omega
  have he1 : (2*b+2+1)/2=b+1 := by omega
  have hLe0 : 2*b+2+0-2=2*b := by omega
  have hLe1 : 2*b+2+1-2=2*b+1 := by omega
  unfold pureMultiplicityTerm
  rw [zpow_natCast_sub_natCast₀ hβ,zpow_natCast_sub_natCast₀ hβ,he0,he1,hLe0,hLe1]
  simp only [pureParityTwo,pureJ,zpow_neg,zpow_ofNat,mul_pow,pow_add,pow_one,
    pow_mul,pow_succ]
  simp only [div_pow,inv_pow,one_pow,← pow_mul,Nat.mul_comm b 2]
  field_simp
  <;> ring

/-- Original exact multiplicity formula for odd p=2b+1. -/
theorem pureMultiplicity_odd_hasSum (b : ℕ) (hb : 1 ≤ b) :
    HasSum (pureMultiplicityTerm (2*b+1))
      (feedbackBeta^(-1:ℤ)*(pureJ*feedbackBeta^(-2:ℤ))^b*pureParityOne/(1-pureJ)) := by
  have h := pureMultiplicity_hasSum_bases (2*b+1) (by omega)
  rwa [pureMultiplicity_odd_bases b hb] at h

/-- Original exact multiplicity formula for even p=2b+2. -/
theorem pureMultiplicity_even_hasSum (b : ℕ) :
    HasSum (pureMultiplicityTerm (2*b+2))
      (feedbackBeta^(-2:ℤ)*(pureJ*feedbackBeta^(-2:ℤ))^b*pureParityTwo/(1-pureJ)) := by
  have h := pureMultiplicity_hasSum_bases (2*b+2) (by omega)
  rwa [pureMultiplicity_even_bases b] at h

end SubmittedGenus.CapFourMass
