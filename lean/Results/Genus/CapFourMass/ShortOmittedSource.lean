import Results.Genus.CapFourMass.ActualEnvelope
import Results.Genus.CapFourMass.TailSeries

/-! Actual short-multiplicity raw source over every omitted pivot, bounded by
the original convergent rational short-tail expression. -/
noncomputable section
open scoped BigOperators
namespace SubmittedGenus.CapFourMass

lemma parity_floor_r (q : ParityPivot) : (q.r-1)/2=q.a := by
  have hu:=q.u.isLt
  dsimp [ParityPivot.r]
  omega
lemma parity_floor_p (q : ParityPivot) : (q.p-1)/2=q.b := by
  have hv:=q.v.isLt
  dsimp [ParityPivot.p]
  omega

lemma parity_eta_bound (q : ParityPivot) :
    eta^((q.r-1)/2+(q.p-1)/2-(if q.p=2*q.r then 0 else 1)) ≤ eta^(q.a+q.b)/eta := by
  rw [parity_floor_r,parity_floor_p]
  apply (le_div_iff₀ eta_bounds.1).mpr
  rw [← pow_succ]
  apply pow_le_pow_of_le_one eta_bounds.1.le eta_bounds.2.le
  split_ifs <;> omega

def pivotEnvelope (q : ParityPivot) (m : ℕ) : ℝ :=
  radius^8*alphabetMass/eta*eta^(q.a+q.b)*sigma^(q.b-q.r)*lambdaBound^(m-3)

lemma sourceEnvelope_le_pivotEnvelope (q : ParityPivot) (m : ℕ) :
    ActualComponent.sourceEnvelope m q.r q.p ≤ pivotEnvelope q m := by
  have hp : 0≤radius^8*alphabetMass*lambdaBound^(m-3) :=
    mul_nonneg (mul_nonneg (pow_nonneg radius_pos.le _)
      (le_of_lt (lt_trans zero_lt_one alphabetMass_gt_one))) (pow_nonneg lambdaBound_pos.le _)
  have hh:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (parity_eta_bound q) hp)
    (pow_nonneg sigma_bounds.1.le (q.b-q.r))
  calc
    _ ≤ radius^8*alphabetMass*lambdaBound^(m-3)*(eta^(q.a+q.b)/eta)*sigma^(q.b-q.r) := by
      simpa only [ActualComponent.sourceEnvelope,parity_floor_p] using hh
    _ = _ := by unfold pivotEnvelope; ring

lemma parity_parameters (q : ParityPivot) (m : ℕ) (hm : q.p<m) :
    RawGraph.Parameters m q.r q.p 4 :=
  ⟨q.toPivot.property.1,q.toPivot.property.2,hm,by decide⟩

lemma raw_eval_nonneg {m r p : ℕ} (hp : RawGraph.Parameters m r p 4) :
    0≤Polynomial.eval₂ (Nat.castRingHom ℝ) radius (RawGraph.rawPolynomial m r p 4) := by
  rw [ActualComponent.raw_eval_eq_component_product hp]
  exact mul_nonneg (pow_nonneg radius_pos.le _) (Finset.prod_nonneg
    (fun c _ => ActualComponent.componentMass_nonneg c))

def shortOmittedSource (P : ℕ) (i : TailIndex) : ℝ :=
  if P < i.pivot.p then
    ∑ j : Fin i.pivot.p,Polynomial.eval₂ (Nat.castRingHom ℝ) radius
      (RawGraph.rawPolynomial (i.pivot.p+1+j.val) i.pivot.r i.pivot.p 4)
  else 0

lemma shortOmittedSource_nonneg (P : ℕ) (i : TailIndex) : 0≤shortOmittedSource P i := by
  unfold shortOmittedSource
  split_ifs
  · exact Finset.sum_nonneg (fun j _ => raw_eval_nonneg (parity_parameters i.pivot _ (by omega)))
  · rfl

/-- The original graph source, not an assumed pointwise numerical majorant. -/
theorem shortOmittedSource_le (P : ℕ) (i : TailIndex) :
    shortOmittedSource P i ≤ shortOmittedTerm P i := by
  rw [shortOmittedTerm_eq_multiplicity]
  unfold shortOmittedSource
  by_cases hp : P < i.pivot.p
  · simp only [if_pos hp,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    exact (ActualComponent.raw_eval_le_sourceEnvelope (parity_parameters i.pivot _ (by omega))).trans
      (sourceEnvelope_le_pivotEnvelope i.pivot (i.pivot.p+1+j.val))
  · simp only [if_neg hp,le_refl]

/-- All omitted short multiplicities converge and obey the submitted rational
short-tail bound. Only its final scalar ceiling comparison is separate. -/
theorem actual_short_omitted_sum (P : ℕ) :
    Summable (shortOmittedSource P) ∧ (∑' i,shortOmittedSource P i) ≤ shortTailExpression P := by
  have hb:=shortOmitted_hasSum P
  have hs:=hb.summable.of_nonneg_of_le (shortOmittedSource_nonneg P) (shortOmittedSource_le P)
  exact ⟨hs,(hs.tsum_le_tsum (shortOmittedSource_le P) hb.summable).trans_eq hb.tsum_eq⟩

end SubmittedGenus.CapFourMass
