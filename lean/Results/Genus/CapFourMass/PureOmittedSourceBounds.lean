import Results.Genus.CapFourMass.ShortOmittedSource
import Results.Genus.CapFourMass.OmittedMultiplicity
import Results.Genus.CapFourMass.SourceMultiplicitySums

/-! Exact pure omitted-source domination. The only remaining hypothesis is
explicitly the complete core-first absolute spectral source envelope. -/
noncomputable section
open scoped BigOperators
namespace SubmittedGenus.CapFourMass

/-- The geometric source obligation, kept separate from all scalar tail sums. -/
def CompleteSourceEnvelope : Prop :=
  ∀ (r N d : ℕ) (hr : 1≤r) (hd : 0<d) (hN : d<N), r+2*d<N →
    sourceAbsolute r N d hN ≤ ActualComponent.sourceEnvelope (r+N) r (r+d)

lemma pivotEnvelope_nonneg (q : ParityPivot) (m : ℕ) : 0≤pivotEnvelope q m := by
  unfold pivotEnvelope
  exact mul_nonneg (mul_nonneg (mul_nonneg
    (div_nonneg (mul_nonneg (pow_nonneg radius_pos.le _)
      (le_of_lt (lt_trans zero_lt_one alphabetMass_gt_one))) eta_bounds.1.le)
    (pow_nonneg eta_bounds.1.le _)) (pow_nonneg sigma_bounds.1.le _))
    (pow_nonneg lambdaBound_pos.le _)

def pureContractedAt (q : ParityPivot) (m : ℕ) (hm : q.p<m) : ℝ :=
  feedbackT^(feedbackExponent q.r q.p)*feedbackBeta^(feedbackCount m q.p)*
    sourcePure q.r (m-q.r) (q.p-q.r) (by have:=q.toPivot.property; change 1≤q.r ∧ q.r<q.p at this; omega)

lemma pureContractedAt_nonneg (q : ParityPivot) (m : ℕ) (hm : q.p<m) :
    0≤pureContractedAt q m hm := by
  unfold pureContractedAt
  exact mul_nonneg (mul_nonneg
    (pow_nonneg (div_nonneg feedbackGamma_bounds.1.le feedbackBeta_bounds.1.le) _)
    (pow_nonneg feedbackBeta_bounds.1.le _)) (sourcePure_nonneg _ _ _ _)

lemma pureContractedAt_le (henv : CompleteSourceEnvelope) (q : ParityPivot)
    (m : ℕ) (hm : q.p<m) (hlong : 2*q.p<m) :
    pureContractedAt q m hm ≤
      feedbackT*tBound^(q.p-q.r)*feedbackBeta^(feedbackCount m q.p)*pivotEnvelope q m := by
  have hq:=q.toPivot.property
  change 1≤q.r ∧ q.r<q.p at hq
  have hn : q.p-q.r<m-q.r := by omega
  have he:=henv q.r (m-q.r) (q.p-q.r) hq.1 (by omega) hn (by omega)
  rw [show q.r+(m-q.r)=m by omega,show q.r+(q.p-q.r)=q.p by omega] at he
  have hp:=(sourcePure_le_absolute q.r (m-q.r) (q.p-q.r) hn).trans
    (he.trans (sourceEnvelope_le_pivotEnvelope q m))
  have ht : 0≤feedbackT := div_nonneg feedbackGamma_bounds.1.le feedbackBeta_bounds.1.le
  have hb : 0≤feedbackBeta^(feedbackCount m q.p) := pow_nonneg feedbackBeta_bounds.1.le _
  have h1:=mul_le_mul_of_nonneg_left hp (mul_nonneg (pow_nonneg ht (feedbackExponent q.r q.p)) hb)
  have h2:=mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (feedback_gap_bound (q.p-q.r)) hb) (pivotEnvelope_nonneg q m)
  exact h1.trans h2

def pureOmittedSource (P : ℕ) (ij : TailIndex×ℕ) : ℝ :=
  if h : P < ij.1.pivot.p ∧ ij.1.pivot.p ≤ ij.2 then
    pureContractedAt ij.1.pivot (ij.1.pivot.p+1+ij.2) (by omega)
  else 0

lemma pureOmittedSource_nonneg (P : ℕ) (ij : TailIndex×ℕ) : 0≤pureOmittedSource P ij := by
  unfold pureOmittedSource
  split_ifs
  · exact pureContractedAt_nonneg _ _ _
  · rfl

lemma pureOmittedSource_le (henv : CompleteSourceEnvelope) (P : ℕ) (ij : TailIndex×ℕ) :
    pureOmittedSource P ij ≤ pureOmittedFamily P ij := by
  rcases ij with ⟨i,j⟩
  unfold pureOmittedSource
  split_ifs with h
  · change P < i.pivot.p ∧ i.pivot.p ≤ j at h
    unfold pureOmittedFamily
    rw [if_pos h.1]
    have hb:=pureContractedAt_le henv i.pivot (i.pivot.p+1+j) (by omega) (by omega)
    apply hb.trans_eq
    have he : (((i.pivot.p+j)/2-i.pivot.p:ℕ):ℤ)=
        (((i.pivot.p+j)/2:ℕ):ℤ)-(i.pivot.p:ℤ) := by omega
    have hp : feedbackBeta^(feedbackCount (i.pivot.p+1+j) i.pivot.p)=
        feedbackBeta^((((i.pivot.p+j)/2:ℕ):ℤ)-(i.pivot.p:ℤ)) := by
      rw [feedbackCount,show i.pivot.p+1+j-1=i.pivot.p+j by omega,← he,zpow_natCast]
    rw [hp]
    unfold pureOmittedScale pureMultiplicityTerm pivotEnvelope TailIndex.gap
    rw [show i.pivot.p+1+j-3=i.pivot.p+j-2 by omega]
    ring
  · exact pureOmittedFamily_nonneg P (i,j)

/-- The actual contracted pure source at every omitted long multiplicity is
summable and obeys the original full-feedback tail once the source envelope is supplied. -/
theorem pure_omitted_source_sum (henv : CompleteSourceEnvelope) (P : ℕ) :
    Summable (pureOmittedSource P) ∧
      (∑' ij,pureOmittedSource P ij) ≤ pureTailExpression P := by
  have hb:=pureOmittedFamily_hasSum P
  have hs:=hb.summable.of_nonneg_of_le (pureOmittedSource_nonneg P) (pureOmittedSource_le henv P)
  exact ⟨hs,(hs.tsum_le_tsum (pureOmittedSource_le henv P) hb.summable).trans_eq hb.tsum_eq⟩

end SubmittedGenus.CapFourMass
