import Results.Genus.CapFourMass.TailSource
import Results.Genus.CapFourMass.MultiplicityFactors

/-! Convergent original short and full-feedback omitted-pivot envelope series. -/
noncomputable section
open scoped BigOperators
namespace SubmittedGenus.CapFourMass

def parityFamilyTerm (P : ℕ) (A B : ℝ) (c : ParityPair → ℝ) (i : TailIndex) : ℝ :=
  c i.1*omittedParityTerm A B sigma P (i.1.1.val+1) (i.1.2.val+1)
    (parityOffset i.1.1 i.1.2) i.2

lemma parityFamilyTerm_nonneg (P : ℕ) {A B : ℝ} (hA : 0≤A) (hB : 0≤B)
    (c : ParityPair → ℝ) (hc : ∀ uv,0≤c uv) (i : TailIndex) :
    0≤parityFamilyTerm P A B c i :=
  mul_nonneg (hc _) (omittedParity_nonneg hA hB sigma_bounds.1.le _ _ _ _ _)

lemma parityFamily_hasSum (P : ℕ) {A B : ℝ} (hconv : convergenceDomain A B)
    (c : ParityPair → ℝ) (hc : ∀ uv,0≤c uv) :
    HasSum (parityFamilyTerm P A B c) (∑ uv : ParityPair,c uv*Htail P uv.1 uv.2 A B) := by
  have hrow (uv : ParityPair) : HasSum (fun q : ℕ×ℕ => parityFamilyTerm P A B c (uv,q))
      (c uv*Htail P uv.1 uv.2 A B) :=
    (omittedParity_hasSum hconv.1 hconv.2.1 sigma_bounds.1.le hconv.2.2.1
      hconv.2.2.2.1 hconv.2.2.2.2.1 hconv.2.2.2.2.2 P (uv.1.val+1) (uv.2.val+1)
      (parityOffset uv.1 uv.2) (parityOffset_le _ _)).mul_left _
  have hs : Summable (parityFamilyTerm P A B c) :=
    (summable_prod_of_nonneg (parityFamilyTerm_nonneg P hconv.1 hconv.2.1 c hc)).mpr
      ⟨fun uv => (hrow uv).summable,(hasSum_fintype _).summable⟩
  have he : (∑' i,parityFamilyTerm P A B c i)=∑ uv : ParityPair,c uv*Htail P uv.1 uv.2 A B := by
    rw [hs.tsum_prod,tsum_fintype]
    exact Finset.sum_congr rfl (fun uv _ => (hrow uv).tsum_eq)
  exact he ▸ hs.hasSum

def shortOmittedTerm (P : ℕ) (i : TailIndex) : ℝ :=
  if P < i.pivot.p then
    radius^8*alphabetMass/(lambdaBound^2*eta*(lambdaBound-1))*
      eta^(i.pivot.a+i.pivot.b)*sigma^(i.pivot.b-i.pivot.r)*
        (lambdaBound^(2*i.pivot.p)-lambdaBound^i.pivot.p)
  else 0

lemma shortOmittedTerm_nonneg (P : ℕ) (i : TailIndex) : 0≤shortOmittedTerm P i := by
  unfold shortOmittedTerm
  split_ifs
  · have hL : lambdaBound^i.pivot.p ≤ lambdaBound^(2*i.pivot.p) :=
      pow_le_pow_right₀ lambdaBound_gt_one.le (by omega)
    have hc : 0≤radius^8*alphabetMass/(lambdaBound^2*eta*(lambdaBound-1)) := by
      exact div_nonneg (mul_nonneg (pow_nonneg radius_pos.le _)
        (le_of_lt (lt_trans zero_lt_one alphabetMass_gt_one)))
        (mul_nonneg (mul_nonneg (sq_nonneg _) eta_bounds.1.le) (sub_pos.mpr lambdaBound_gt_one).le)
    exact mul_nonneg (mul_nonneg (mul_nonneg hc (pow_nonneg eta_bounds.1.le _))
      (pow_nonneg sigma_bounds.1.le _)) (sub_nonneg.mpr hL)
  · rfl

lemma shortOmittedTerm_eq_parity (P : ℕ) (i : TailIndex) :
    shortOmittedTerm P i=radius^8*alphabetMass/(lambdaBound^2*eta*(lambdaBound-1))*
      (parityFamilyTerm P eta (eta*lambdaBound^4) (fun uv => lambdaBound^(2*(uv.2.val+1))) i-
       parityFamilyTerm P eta (eta*lambdaBound^2) (fun uv => lambdaBound^(uv.2.val+1)) i) := by
  unfold shortOmittedTerm parityFamilyTerm omittedParityTerm
  change (if P < i.pivot.p then _ else 0)=_*(
    lambdaBound^(2*(i.pivot.v.val+1))*(if P < i.pivot.p then _ else 0)-
    lambdaBound^(i.pivot.v.val+1)*(if P < i.pivot.p then _ else 0))
  by_cases hp : P < i.pivot.p
  · simp only [if_pos hp]
    change _ = _*(lambdaBound^(2*(i.pivot.v.val+1))*
      (eta^i.pivot.a*(eta*lambdaBound^4)^i.pivot.b*sigma^(i.pivot.b-i.pivot.r))-
      lambdaBound^(i.pivot.v.val+1)*
      (eta^i.pivot.a*(eta*lambdaBound^2)^i.pivot.b*sigma^(i.pivot.b-i.pivot.r)))
    have hp2 : 2*i.pivot.p=2*(i.pivot.v.val+1)+4*i.pivot.b := by
      dsimp [ParityPivot.p]; ring
    have hp1 : i.pivot.p=(i.pivot.v.val+1)+2*i.pivot.b := by
      dsimp [ParityPivot.p]; ring
    rw [hp2,hp1]
    simp only [pow_add,mul_pow,← pow_mul]
    ring
  · simp only [if_neg hp,mul_zero,sub_zero]

/-- Original short omitted-tail expression is exactly a convergent sum of
nonnegative pivot-envelope contributions. -/
theorem shortOmitted_hasSum (P : ℕ) : HasSum (shortOmittedTerm P) (shortTailExpression P) := by
  have h4:=parityFamily_hasSum P short_convergence_four
    (fun uv => lambdaBound^(2*(uv.2.val+1))) (fun _ => pow_nonneg lambdaBound_pos.le _)
  have h2:=parityFamily_hasSum P short_convergence_two
    (fun uv => lambdaBound^(uv.2.val+1)) (fun _ => pow_nonneg lambdaBound_pos.le _)
  have hs:=((h4.sub h2).mul_left (radius^8*alphabetMass/(lambdaBound^2*eta*(lambdaBound-1))))
  have he : (fun i => radius^8*alphabetMass/(lambdaBound^2*eta*(lambdaBound-1))*
      (parityFamilyTerm P eta (eta*lambdaBound^4) (fun uv => lambdaBound^(2*(uv.2.val+1))) i-
       parityFamilyTerm P eta (eta*lambdaBound^2) (fun uv => lambdaBound^(uv.2.val+1)) i))=
      shortOmittedTerm P := funext (fun i => (shortOmittedTerm_eq_parity P i).symm)
  rw [he] at hs
  simpa only [shortTailExpression,← Finset.sum_sub_distrib] using hs

lemma shortOmittedTerm_eq_multiplicity (P : ℕ) (i : TailIndex) :
    shortOmittedTerm P i=
      if P < i.pivot.p then
        radius^8*alphabetMass/eta*eta^(i.pivot.a+i.pivot.b)*sigma^(i.pivot.b-i.pivot.r)*
          ∑ j : Fin i.pivot.p,lambdaBound^(i.pivot.p+1+j.val-3)
      else 0 := by
  unfold shortOmittedTerm
  split_ifs
  · have hp : 2 ≤ i.pivot.p := by
      have hr:=i.pivot.toPivot.property.1
      have hrp:=i.pivot.toPivot.property.2
      change 1 ≤ i.pivot.r at hr
      change i.pivot.r < i.pivot.p at hrp
      omega
    rw [short_multiplicity_sum _ hp]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  · rfl

end SubmittedGenus.CapFourMass
