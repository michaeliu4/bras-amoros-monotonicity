import Results.Genus.CapFourMass.GenuineMass
import Results.Genus.CapFourMass.ShortSourceFamilies
import Results.Genus.CapFourMass.DependentShift
import Results.Genus.CapFourMass.MixedOmittedSourceBounds

/-! Pointwise partition of the exact master source into the original six sectors. -/
noncomputable section
open scoped BigOperators
namespace SubmittedGenus.CapFourMass
attribute [local instance] Classical.propDecidable

def pureLongContracted (q : ParityPivot) (n : ℕ) : ℝ :=
  feedbackT^(feedbackExponent q.r q.p)*
    feedbackBeta^(feedbackCount (longMultiplicity q.r (q.p-q.r) n) q.p)*
      sourcePure q.r (longTailN q.r (q.p-q.r) n) (q.p-q.r)
        (by have:=longTailN_large q.r (q.p-q.r) n; omega)

lemma pureLongContracted_le (q : ParityPivot) (n : ℕ) :
    pureLongContracted q n  ≤  sourcePureSeries q.r (q.p-q.r) n := by
  have hq:=q.toPivot.property
  change 1  ≤  q.r ∧ q.r < q.p at hq
  have hg : q.r+(q.p-q.r)=q.p := by omega
  have hm : 2*q.p < longMultiplicity q.r (q.p-q.r) n := by rw [longMultiplicity_eq,hg]; omega
  unfold pureLongContracted sourcePureSeries
  rw [hg]
  exact normalized_majorization _ _ _ hm _ (sourcePure_nonneg _ _ _ _)

lemma long_master_coordinates (q : ParityPivot) (j : ℕ) (hj : q.p  ≤  j) :
    longMultiplicity q.r (q.p-q.r) (j-q.p)=q.p+1+j ∧
    longTailN q.r (q.p-q.r) (j-q.p)=q.p+1+j-q.r := by
  have hq:=q.toPivot.property
  change 1  ≤  q.r ∧ q.r < q.p at hq
  unfold longMultiplicity longTailN
  omega

lemma pureLongContracted_eq (q : ParityPivot) (j : ℕ) (hj : q.p  ≤  j) :
    pureLongContracted q (j-q.p)=pureContractedAt q (q.p+1+j) (by omega) := by
  unfold pureLongContracted pureContractedAt
  simp only [(long_master_coordinates q j hj).1,(long_master_coordinates q j hj).2]

lemma master_long_eq (i : TailIndex) (j : ℕ) (hj : i.pivot.p  ≤  j) :
    GenuineSource.masterTerm (masterEquiv (i,j))=
      pureLongContracted i.pivot (j-i.pivot.p)+mixedContractedAt i.pivot (j-i.pivot.p) := by
  unfold GenuineSource.masterTerm
  rw [dif_neg (by rw [masterEquiv_short_iff]; omega)]
  simp only [masterEquiv_m,masterEquiv_r,masterEquiv_p]
  unfold pureLongContracted mixedContractedAt
  simp only [(long_master_coordinates i.pivot j hj).1,(long_master_coordinates i.pivot j hj).2]
  ring

def shortSector (P : ℕ) (ij : TailIndex×ℕ) : ℝ :=
  prefixSeries P shortSeries ij+shortOmittedFamily P ij

def pureSector (P : ℕ) (ij : TailIndex×ℕ) : ℝ :=
  extendPast (fun i : TailIndex => i.pivot.p)
    (prefixSeries P (fun r p => sourcePureSeries r (p-r))) ij+pureOmittedSource P ij

def mixedSector (P : ℕ) (ij : TailIndex×ℕ) : ℝ :=
  extendPast (fun i : TailIndex => i.pivot.p)
    (prefixSeries P (fun r p => sourceMixedSeries r (p-r))) ij+
  extendPast (fun i : TailIndex => i.pivot.p) (mixedOmittedSource P) ij

lemma shortSector_eq (P : ℕ) (ij : TailIndex×ℕ) :
    shortSector P ij=shortSeries ij.1.pivot.r ij.1.pivot.p ij.2 := by
  unfold shortSector prefixSeries shortOmittedFamily
  by_cases hp : ij.1.pivot.p  ≤  P
  · simp [hp,show ¬P < ij.1.pivot.p by omega]
  · simp [hp,show P < ij.1.pivot.p by omega]

lemma pureSector_long (P : ℕ) (i : TailIndex) (j : ℕ) (hj : i.pivot.p  ≤  j) :
    pureLongContracted i.pivot (j-i.pivot.p)  ≤  pureSector P (i,j) := by
  unfold pureSector extendPast prefixSeries pureOmittedSource
  simp only [hj,if_true]
  by_cases hp : i.pivot.p ≤ P
  · simpa [hp,show ¬P < i.pivot.p by omega,hj] using
      pureLongContracted_le i.pivot (j-i.pivot.p)
  · simpa [hp,show P < i.pivot.p by omega,hj] using
      (pureLongContracted_eq i.pivot j hj).le

lemma mixedSector_long (P : ℕ) (i : TailIndex) (j : ℕ) (hj : i.pivot.p  ≤  j) :
    mixedContractedAt i.pivot (j-i.pivot.p)  ≤  mixedSector P (i,j) := by
  unfold mixedSector extendPast prefixSeries mixedOmittedSource
  simp only [hj,if_true]
  by_cases hp : i.pivot.p  ≤  P
  · simp only [hp,if_true,show ¬P < i.pivot.p by omega,if_false,add_zero]
    exact mixedContractedAt_le _ _
  · simp only [hp,if_false,show P < i.pivot.p by omega,if_true,zero_add,le_refl]

lemma master_le_sectors (Ps Pp Pm : ℕ) (ij : TailIndex×ℕ) :
    GenuineSource.masterTerm (masterEquiv ij)  ≤ 
      shortSector Ps ij+pureSector Pp ij+mixedSector Pm ij := by
  rcases ij with ⟨i,j⟩
  by_cases hj : j < i.pivot.p
  · rw [shortSector_eq]
    have hp : ¬i.pivot.p  ≤  j := by omega
    unfold GenuineSource.masterTerm
    rw [dif_pos ((masterEquiv_short_iff i j).mpr hj)]
    simp only [masterEquiv_m,masterEquiv_r,masterEquiv_p]
    simp [shortSeries,hj,pureSector,mixedSector,extendPast,pureOmittedSource,hp]
  · have hl : i.pivot.p  ≤  j := by omega
    rw [master_long_eq i j hl,shortSector_eq]
    simp only [shortSeries,if_neg hj,zero_add]
    exact add_le_add (pureSector_long Pp i j hl) (mixedSector_long Pm i j hl)

#print axioms master_le_sectors
end SubmittedGenus.CapFourMass
