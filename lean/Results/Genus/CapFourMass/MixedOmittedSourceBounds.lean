import Results.Genus.CapFourMass.PureOmittedSourceBounds

/-! Actual mixed-source omitted multiplicities, retaining the original paired
base numerator and using only the explicit complete-source envelope premise. -/
noncomputable section
open scoped BigOperators
namespace SubmittedGenus.CapFourMass

lemma sourceMixed_le_absolute (r N d : ℕ) (hN : d < N) :
    sourceMixed r N d hN ≤ sourceAbsolute r N d hN := by
  rw [sourceAbsolute_eq_pure_add_mixed]
  exact le_add_of_nonneg_left (sourcePure_nonneg _ _ _ _)

lemma sourceMixedSeries_pivot_le (henv : CompleteSourceEnvelope) (i : TailIndex) (n : ℕ) :
    sourceMixedSeries i.pivot.r i.gap n ≤ pureOmittedScale i*
      normalizer^(2*(n/2))*lambdaBound^(2*i.pivot.p+n-2) := by
  have hq:=i.pivot.toPivot.property
  change 1 ≤ i.pivot.r ∧ i.pivot.r < i.pivot.p at hq
  have hg : i.pivot.r+i.gap=i.pivot.p := by unfold TailIndex.gap; omega
  have hd : 0 < i.gap := by unfold TailIndex.gap; omega
  have hN : i.gap < longTailN i.pivot.r i.gap n := by have:=longTailN_large i.pivot.r i.gap n; omega
  have he:=henv i.pivot.r (longTailN i.pivot.r i.gap n) i.gap hq.1 hd hN
    (longTailN_large i.pivot.r i.gap n)
  change sourceAbsolute _ _ _ _ ≤ ActualComponent.sourceEnvelope (longMultiplicity i.pivot.r i.gap n) _ _ at he
  rw [hg] at he
  have hp:=(sourceMixed_le_absolute _ _ _ hN).trans
    (he.trans (sourceEnvelope_le_pivotEnvelope i.pivot _))
  have hm : 2*i.pivot.p < longMultiplicity i.pivot.r i.gap n := by rw [longMultiplicity_eq,hg]; omega
  unfold sourceMixedSeries
  rw [hg,normalizationK_times _ _ _ hm]
  have hc : feedbackCount (longMultiplicity i.pivot.r i.gap n) i.pivot.p=n/2 := by
    rw [longMultiplicity_eq,hg]
    unfold feedbackCount
    omega
  rw [hc]
  have ht : 0 ≤ feedbackT := div_nonneg feedbackGamma_bounds.1.le feedbackBeta_bounds.1.le
  have hw : 0 ≤ normalizer^(2*(n/2)) := pow_nonneg normalizer_bounds.1.le _
  have hb:=mul_le_mul_of_nonneg_left hp
    (mul_nonneg (pow_nonneg ht (feedbackExponent i.pivot.r i.pivot.p)) hw)
  have ht' : feedbackT^(feedbackExponent i.pivot.r i.pivot.p) ≤ feedbackT*tBound^i.gap :=
    feedback_gap_bound _
  have hs:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ht' hw)
    (pivotEnvelope_nonneg i.pivot (longMultiplicity i.pivot.r i.gap n))
  apply (hb.trans hs).trans_eq
  unfold pivotEnvelope pureOmittedScale
  rw [longMultiplicity_eq,hg,show 2*i.pivot.p+1+n-3=2*i.pivot.p+n-2 by omega]
  ring

lemma sum_range_pairs (f : ℕ→ℝ) (d : ℕ) :
    (∑ n ∈ Finset.range (2*d),f n)=∑ j ∈ Finset.range d,(f (2*j)+f (2*j+1)) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [show 2*(d+1)=2*d+1+1 by omega,Finset.sum_range_succ,Finset.sum_range_succ,
      Finset.sum_range_succ,ih]
    ring

def mixedBaseEnvelope (i : TailIndex) : ℝ :=
  pureOmittedScale i*(1+lambdaBound)*lambdaBound^(2*i.pivot.p-2)*
    ∑ j ∈ Finset.range i.gap,mixedJ^j

lemma mixedBaseEnvelope_nonneg (i : TailIndex) : 0 ≤ mixedBaseEnvelope i := by
  unfold mixedBaseEnvelope
  exact mul_nonneg (mul_nonneg (mul_nonneg (pureOmittedScale_nonneg i) (by linarith [lambdaBound_pos]))
    (pow_nonneg lambdaBound_pos.le _)) (Finset.sum_nonneg (fun j _ => pow_nonneg mixedJ_bounds.1.le j))

lemma sourceMixedSeries_bases_le (henv : CompleteSourceEnvelope) (i : TailIndex) :
    (∑ s : Fin (2*i.gap),sourceMixedSeries i.pivot.r i.gap s.val) ≤ mixedBaseEnvelope i := by
  have hh:=Finset.sum_le_sum (fun s (_ : s ∈ (Finset.univ : Finset (Fin (2*i.gap)))) =>
    sourceMixedSeries_pivot_le henv i s.val)
  apply hh.trans_eq
  change (∑ s : Fin (2*i.gap),
    (fun n : ℕ => pureOmittedScale i*normalizer^(2*(n/2))*lambdaBound^(2*i.pivot.p+n-2)) s.val)=_
  rw [Fin.sum_univ_eq_sum_range
    (fun n : ℕ => pureOmittedScale i*normalizer^(2*(n/2))*lambdaBound^(2*i.pivot.p+n-2))
    (2*i.gap),sum_range_pairs]
  have hp : 2 ≤ i.pivot.p := by have:=i.pivot.toPivot.property; change 1 ≤ i.pivot.r ∧ i.pivot.r < i.pivot.p at this; omega
  have he (j : ℕ) :
      pureOmittedScale i*normalizer^(2*(2*j/2))*lambdaBound^(2*i.pivot.p+2*j-2)+
      pureOmittedScale i*normalizer^(2*((2*j+1)/2))*lambdaBound^(2*i.pivot.p+(2*j+1)-2)=
      pureOmittedScale i*(1+lambdaBound)*lambdaBound^(2*i.pivot.p-2)*mixedJ^j := by
    have h1 : 2*j/2=j := by omega
    have h2 : (2*j+1)/2=j := by omega
    rw [h1,h2]
    have hb:=congrArg (fun x : ℝ => pureOmittedScale i*x) (mixed_base_pair i.pivot.p j hp)
    have e1 : 2*i.pivot.p+(2*j+1)-3=2*i.pivot.p+2*j-2 := by omega
    have e2 : 2*i.pivot.p+(2*j+2)-3=2*i.pivot.p+(2*j+1)-2 := by omega
    rw [e1,e2] at hb
    nlinarith [hb]
  simp_rw [he]
  rw [← Finset.mul_sum]
  rfl

/-- Every original mixed multiplicity for one pivot is bounded with the
retained geometric numerator, not the weaker factor d. -/
theorem sourceMixedSeries_pivot_sum (henv : CompleteSourceEnvelope) (i : TailIndex) :
    Summable (sourceMixedSeries i.pivot.r i.gap) ∧
      (∑' n,sourceMixedSeries i.pivot.r i.gap n) ≤ 
        mixedTailConstant*(lambdaBound^(2*i.pivot.p)*eta^(i.pivot.a+i.pivot.b)*
          sigma^(i.pivot.b-i.pivot.r)*tBound^i.gap*mixedFactor mixedJ negativeSquare i.gap) := by
  have hd : 0 < i.gap := by have:=i.pivot.toPivot.property.2; change i.pivot.r < i.pivot.p at this; unfold TailIndex.gap; omega
  obtain ⟨hs,hbound⟩:=sourceMixedSeries_complete i.pivot.r i.gap hd
  refine ⟨hs,?_⟩
  have hbase:=sourceMixedSeries_bases_le henv i
  have hden : 0 < 1-(normalizer*lam)^(2*i.gap)*rho^2 :=
    sub_pos.mpr (mixed_progression_ratio_bounds i.gap).2
  have h1:=div_le_div_of_nonneg_right hbase hden.le
  have h2:=mul_le_mul_of_nonneg_left (actual_mixed_denominator_reciprocal i.gap)
    (mixedBaseEnvelope_nonneg i)
  simp only [← div_eq_mul_one_div] at h2
  apply (hbound.trans (h1.trans h2)).trans_eq
  unfold mixedBaseEnvelope
  rw [mul_div_assoc,mixed_geometric_factor]
  unfold pureOmittedScale mixedTailConstant
  have hp : 2 ≤ i.pivot.p := by have:=i.pivot.toPivot.property; change 1 ≤ i.pivot.r ∧ i.pivot.r < i.pivot.p at this; omega
  have hpow : lambdaBound^(2*i.pivot.p-2)=lambdaBound^(2*i.pivot.p)/lambdaBound^2 := by
    apply (eq_div_iff (pow_ne_zero _ (ne_of_gt lambdaBound_pos))).mpr
    rw [← pow_add,show 2*i.pivot.p-2+2=2*i.pivot.p by omega]
  rw [hpow]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

lemma mixedTailConstant_nonneg : 0 ≤ mixedTailConstant := by
  unfold mixedTailConstant
  have ht : 0 ≤ feedbackT := div_nonneg feedbackGamma_bounds.1.le feedbackBeta_bounds.1.le
  exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg radius_pos.le _)
    (le_of_lt (lt_trans zero_lt_one alphabetMass_gt_one))) (by linarith [lambdaBound_pos])) ht)
    (mul_nonneg (sq_nonneg _) eta_bounds.1.le)

def mixedOmittedNormalized (P : ℕ) (ij : TailIndex×ℕ) : ℝ :=
  if P  <  ij.1.pivot.p then sourceMixedSeries ij.1.pivot.r ij.1.gap ij.2 else 0

lemma mixedOmittedNormalized_nonneg (P : ℕ) (ij : TailIndex×ℕ) :
    0 ≤ mixedOmittedNormalized P ij := by
  unfold mixedOmittedNormalized
  split_ifs
  · exact sourceMixedSeries_nonneg _ _ _
  · rfl

lemma mixedOmittedNormalized_row (henv : CompleteSourceEnvelope) (P : ℕ) (i : TailIndex) :
    Summable (fun n => mixedOmittedNormalized P (i,n)) ∧
      (∑' n,mixedOmittedNormalized P (i,n)) ≤ 
        mixedTailConstant*(omittedPivotCoefficient P i*tBound^i.gap*
          mixedFactor mixedJ negativeSquare i.gap) := by
  by_cases hp : P  <  i.pivot.p
  · simpa only [mixedOmittedNormalized,omittedPivotCoefficient,hp,if_true] using
      sourceMixedSeries_pivot_sum henv i
  · simp only [mixedOmittedNormalized,omittedPivotCoefficient,hp,if_false,zero_mul,mul_zero]
    exact ⟨summable_zero,by simp⟩

/-- The whole normalized mixed omitted source, with precisely the 2d base
progressions, is convergent and bounded by the original three-evaluation expression. -/
theorem mixed_omitted_normalized_sum (henv : CompleteSourceEnvelope) (P : ℕ) :
    Summable (mixedOmittedNormalized P) ∧
      (∑' ij,mixedOmittedNormalized P ij) ≤ mixedTailExpression P := by
  have hb:=mixed_omitted_pivot_sum P
  have hmajor:=(hb.1.mul_left mixedTailConstant)
  have hrow : Summable (fun i : TailIndex => ∑' n,mixedOmittedNormalized P (i,n)) :=
    hmajor.of_nonneg_of_le (fun i => tsum_nonneg (fun n => mixedOmittedNormalized_nonneg P (i,n)))
      (fun i => (mixedOmittedNormalized_row henv P i).2)
  have hs : Summable (mixedOmittedNormalized P) :=
    (summable_prod_of_nonneg (mixedOmittedNormalized_nonneg P)).mpr
      ⟨fun i => (mixedOmittedNormalized_row henv P i).1,hrow⟩
  refine ⟨hs,?_⟩
  rw [hs.tsum_prod]
  have hh:=hrow.tsum_le_tsum (fun i => (mixedOmittedNormalized_row henv P i).2) hmajor
  rw [tsum_mul_left] at hh
  exact hh.trans hb.2

/-- Exact unnormalized feedback term at m=2p+1+n. -/
def mixedContractedAt (q : ParityPivot) (n : ℕ) : ℝ :=
  feedbackT^(feedbackExponent q.r q.p)*
    feedbackBeta^(feedbackCount (longMultiplicity q.r (q.p-q.r) n) q.p)*
      sourceMixed q.r (longTailN q.r (q.p-q.r) n) (q.p-q.r)
        (by have:=longTailN_large q.r (q.p-q.r) n; omega)

lemma mixedContractedAt_nonneg (q : ParityPivot) (n : ℕ) : 0 ≤ mixedContractedAt q n := by
  unfold mixedContractedAt
  exact mul_nonneg (mul_nonneg
    (pow_nonneg (div_nonneg feedbackGamma_bounds.1.le feedbackBeta_bounds.1.le) _)
    (pow_nonneg feedbackBeta_bounds.1.le _)) (sourceMixed_nonneg _ _ _ _)

lemma mixedContractedAt_le (q : ParityPivot) (n : ℕ) :
    mixedContractedAt q n ≤ sourceMixedSeries q.r (q.p-q.r) n := by
  have hq:=q.toPivot.property
  change 1 ≤ q.r ∧ q.r < q.p at hq
  have hg : q.r+(q.p-q.r)=q.p := by omega
  have hm : 2*q.p < longMultiplicity q.r (q.p-q.r) n := by rw [longMultiplicity_eq,hg]; omega
  unfold mixedContractedAt sourceMixedSeries
  rw [hg]
  exact normalized_majorization _ _ _ hm _ (sourceMixed_nonneg _ _ _ _)

def mixedOmittedSource (P : ℕ) (ij : TailIndex×ℕ) : ℝ :=
  if P  <  ij.1.pivot.p then mixedContractedAt ij.1.pivot ij.2 else 0

lemma mixedOmittedSource_nonneg (P : ℕ) (ij : TailIndex×ℕ) : 0 ≤ mixedOmittedSource P ij := by
  unfold mixedOmittedSource
  split_ifs
  · exact mixedContractedAt_nonneg _ _
  · rfl

lemma mixedOmittedSource_le (P : ℕ) (ij : TailIndex×ℕ) :
    mixedOmittedSource P ij ≤ mixedOmittedNormalized P ij := by
  unfold mixedOmittedSource mixedOmittedNormalized
  split_ifs
  · exact mixedContractedAt_le _ _
  · rfl

/-- The actual original beta-weighted mixed source has the submitted omitted
bound; the complete-source envelope is the only remaining geometric premise. -/
theorem mixed_omitted_source_sum (henv : CompleteSourceEnvelope) (P : ℕ) :
    Summable (mixedOmittedSource P) ∧
      (∑' ij,mixedOmittedSource P ij) ≤ mixedTailExpression P := by
  have hb:=mixed_omitted_normalized_sum henv P
  have hs:=hb.1.of_nonneg_of_le (mixedOmittedSource_nonneg P) (mixedOmittedSource_le P)
  exact ⟨hs,(hs.tsum_le_tsum (mixedOmittedSource_le P) hb.1).trans hb.2⟩

end SubmittedGenus.CapFourMass
