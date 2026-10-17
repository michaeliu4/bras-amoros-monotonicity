import Results.Genus.CapFourMass.TailSeries

/-! Exact nonnegative full-feedback omitted-pivot series with signed added-range exponents. -/
noncomputable section
open scoped BigOperators
namespace SubmittedGenus.CapFourMass

lemma parityMultiplicity_nonneg (v : Fin 2) : 0≤parityMultiplicity v := by
  have hL:=lambdaBound_pos
  have hJ:=pureJ_bounds.1
  unfold parityMultiplicity pureParityOne pureParityTwo
  split_ifs <;> positivity

def pureTailCoefficient (uv : ParityPair) : ℝ :=
  feedbackBeta^(-((uv.2.val+1:ℕ):ℤ))*tBound^((uv.2.val:ℤ)-(uv.1.val:ℤ))*
    parityMultiplicity uv.2/(eta*(1-pureJ))

lemma pureTailCoefficient_nonneg (uv : ParityPair) : 0≤pureTailCoefficient uv := by
  unfold pureTailCoefficient
  exact div_nonneg (mul_nonneg (mul_nonneg (zpow_pos feedbackBeta_bounds.1 _).le
    (zpow_pos (lt_trans zero_lt_one tBound_gt_one) _).le) (parityMultiplicity_nonneg _))
    (mul_nonneg eta_bounds.1.le (sub_pos.mpr pureJ_bounds.2).le)

def purePivotMultiplicity (q : ParityPivot) : ℝ :=
  feedbackBeta^(-((q.v.val+1:ℕ):ℤ))*(pureJ*feedbackBeta^(-2:ℤ))^q.b*
    parityMultiplicity q.v/(1-pureJ)

lemma purePivotMultiplicity_hasSum (q : ParityPivot) :
    HasSum (pureMultiplicityTerm q.p) (purePivotMultiplicity q) := by
  have hp : 2≤q.p := by
    have hr:=q.toPivot.property.1
    have hrp:=q.toPivot.property.2
    change 1≤q.r at hr
    change q.r<q.p at hrp
    omega
  have hv : q.v=0 ∨ q.v=1 := by
    have h:=q.v.isLt
    rcases (show q.v.val=0 ∨ q.v.val=1 by omega) with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  rcases hv with hv | hv
  · have hqp : q.p=2*q.b+1 := by simp [ParityPivot.p,hv]
    have hb : 1≤q.b := by omega
    rw [hqp]
    simpa [purePivotMultiplicity,parityMultiplicity,hv] using pureMultiplicity_odd_hasSum q.b hb
  · have hqp : q.p=2*q.b+2 := by simp [ParityPivot.p,hv]
    rw [hqp]
    simpa [purePivotMultiplicity,parityMultiplicity,hv] using pureMultiplicity_even_hasSum q.b

lemma purePivotMultiplicity_nonneg (q : ParityPivot) : 0≤purePivotMultiplicity q := by
  unfold purePivotMultiplicity
  exact div_nonneg (mul_nonneg (mul_nonneg (zpow_pos feedbackBeta_bounds.1 _).le
    (pow_nonneg (mul_nonneg pureJ_bounds.1.le (zpow_pos feedbackBeta_bounds.1 _).le) _))
    (parityMultiplicity_nonneg _)) (sub_pos.mpr pureJ_bounds.2).le

lemma parity_reweight_power (q : ParityPivot) {x : ℝ} (hx : 0<x) (Q : ℝ) :
    x^((q.v.val:ℤ)-(q.u.val:ℤ))*(eta/x^2)^q.a*(eta*Q*x^2)^q.b=
      eta^(q.a+q.b)*Q^q.b*x^(q.p-q.r) := by
  rw [parity_gap_power q hx]
  simp only [pow_add,div_pow,mul_pow,← pow_mul]
  ring

def pureOmittedTerm (P : ℕ) (i : TailIndex) : ℝ :=
  if P < i.pivot.p then
    radius^8*alphabetMass*feedbackT/eta*eta^(i.pivot.a+i.pivot.b)*
      sigma^(i.pivot.b-i.pivot.r)*tBound^i.gap*purePivotMultiplicity i.pivot
  else 0

lemma pureOmittedTerm_eq_parity (P : ℕ) (i : TailIndex) :
    pureOmittedTerm P i=radius^8*alphabetMass*feedbackT*
      parityFamilyTerm P pureA pureB pureTailCoefficient i := by
  have hp:=parity_reweight_power i.pivot (lt_trans zero_lt_one tBound_gt_one)
    (pureJ*feedbackBeta^(-2:ℤ))
  have hB : pureB=eta*(pureJ*feedbackBeta^(-2:ℤ))*tBound^2 := by unfold pureB; ring
  change tBound^((i.pivot.v.val:ℤ)-(i.pivot.u.val:ℤ))*pureA^i.pivot.a*
    (eta*(pureJ*feedbackBeta^(-2:ℤ))*tBound^2)^i.pivot.b=_ at hp
  rw [← hB] at hp
  unfold pureOmittedTerm parityFamilyTerm omittedParityTerm
  change (if P < i.pivot.p then _ else 0)=_*(pureTailCoefficient i.1*
    if P < i.pivot.p then _ else 0)
  by_cases hi : P < i.pivot.p
  · simp only [if_pos hi]
    change _=radius^8*alphabetMass*feedbackT*(
      (feedbackBeta^(-((i.pivot.v.val+1:ℕ):ℤ))*tBound^((i.pivot.v.val:ℤ)-(i.pivot.u.val:ℤ))*
        parityMultiplicity i.pivot.v/(eta*(1-pureJ)))*
      (pureA^i.pivot.a*pureB^i.pivot.b*sigma^(i.pivot.b-i.pivot.r)))
    calc
      _ = radius^8*alphabetMass*feedbackT*(feedbackBeta^(-((i.pivot.v.val+1:ℕ):ℤ))*
        parityMultiplicity i.pivot.v/(eta*(1-pureJ))*sigma^(i.pivot.b-i.pivot.r)*
        (eta^(i.pivot.a+i.pivot.b)*(pureJ*feedbackBeta^(-2:ℤ))^i.pivot.b*tBound^(i.pivot.p-i.pivot.r))) := by
          unfold purePivotMultiplicity TailIndex.gap
          simp only [div_eq_mul_inv,mul_inv_rev]
          ring
      _ = _ := by rw [← hp]; simp only [div_eq_mul_inv,mul_inv_rev]; ring
  · simp only [if_neg hi,mul_zero]

lemma pureOmittedTerm_nonneg (P : ℕ) (i : TailIndex) : 0≤pureOmittedTerm P i := by
  rw [pureOmittedTerm_eq_parity]
  have hT : 0≤feedbackT := div_nonneg feedbackGamma_bounds.1.le feedbackBeta_bounds.1.le
  exact mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg radius_pos.le _)
    (le_of_lt (lt_trans zero_lt_one alphabetMass_gt_one))) hT)
    (parityFamilyTerm_nonneg P pure_convergence.1 pure_convergence.2.1
      pureTailCoefficient pureTailCoefficient_nonneg i)

/-- The original full-feedback omitted tail is the sum of its actual positive
pivot coefficients, after the exact signed multiplicity sum is performed. -/
theorem pureOmitted_hasSum (P : ℕ) : HasSum (pureOmittedTerm P) (pureTailExpression P) := by
  have hs:=(parityFamily_hasSum P pure_convergence pureTailCoefficient pureTailCoefficient_nonneg).mul_left
    (radius^8*alphabetMass*feedbackT)
  have he : (fun i => radius^8*alphabetMass*feedbackT*
      parityFamilyTerm P pureA pureB pureTailCoefficient i)=pureOmittedTerm P :=
    funext (fun i => (pureOmittedTerm_eq_parity P i).symm)
  rw [he] at hs
  exact hs

end SubmittedGenus.CapFourMass
