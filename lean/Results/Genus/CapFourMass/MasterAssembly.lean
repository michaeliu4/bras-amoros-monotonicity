import Results.Genus.CapFourMass.MasterPointwise
import Results.Genus.CapFourMass.IntervalShortAcceptance
import Results.Genus.CapFourMass.IntervalMixedAcceptance
import Results.Genus.CapFourMass.IntervalPureAcceptance

/-! Exact six-sector assembly for the original cap-four mass. The finite
prefix certificates and complete source envelope remain explicit obligations. -/
noncomputable section
open scoped BigOperators
namespace SubmittedGenus.CapFourMass
open OriginalPopulations

lemma shortSector_bound (P : ℕ) : Summable (shortSector P) ∧
    (∑' ij,shortSector P ij)  ≤  originalShortPrefix P+shortTailExpression P := by
  have hp:=shortPrefix_summable P
  have ht:=shortOmittedFamily_bound P
  refine ⟨hp.add ht.1,?_⟩
  change (∑' ij,(prefixSeries P shortSeries ij+shortOmittedFamily P ij)) ≤ _
  rw [hp.tsum_add ht.1,shortPrefix_tsum]
  linarith [ht.2]

lemma pureSector_bound (henv : CompleteSourceEnvelope) (P : ℕ) : Summable (pureSector P) ∧
    (∑' ij,pureSector P ij)  ≤  originalPurePrefix P+pureTailExpression P := by
  have hp:=purePrefix_summable P
  have he:=extendPast_summable (fun i : TailIndex => i.pivot.p) _ hp
  have ht:=pure_omitted_source_sum henv P
  refine ⟨he.add ht.1,?_⟩
  change (∑' ij,(extendPast (fun i : TailIndex => i.pivot.p)
    (prefixSeries P (fun r p => sourcePureSeries r (p-r))) ij+pureOmittedSource P ij)) ≤ _
  rw [he.tsum_add ht.1,extendPast_tsum _ _ hp,purePrefix_tsum]
  linarith [ht.2]

lemma mixedSector_bound (henv : CompleteSourceEnvelope) (P : ℕ) : Summable (mixedSector P) ∧
    (∑' ij,mixedSector P ij)  ≤  originalMixedPrefix P+mixedTailExpression P := by
  have hp:=mixedPrefix_summable P
  have he:=extendPast_summable (fun i : TailIndex => i.pivot.p) _ hp
  have ht:=mixed_omitted_source_sum henv P
  have het:=extendPast_summable (fun i : TailIndex => i.pivot.p) _ ht.1
  refine ⟨he.add het,?_⟩
  change (∑' ij,(extendPast (fun i : TailIndex => i.pivot.p)
    (prefixSeries P (fun r p => sourceMixedSeries r (p-r))) ij+
    extendPast (fun i : TailIndex => i.pivot.p) (mixedOmittedSource P) ij)) ≤ _
  rw [he.tsum_add het,extendPast_tsum _ _ hp,extendPast_tsum _ _ ht.1]
  linarith [mixedPrefix_tsum_le P,ht.2]

/-- Convergence and genuine source mass follow from all six original sectors.
This theorem does not substitute a numeric majorant for an unproved source bridge. -/
theorem genuine_mass_six_sectors (henv : CompleteSourceEnvelope) (Ps Pp Pm : ℕ) :
    Summable (fun g => (countFour g:ℝ)*radius^g) ∧
    massFour radius  ≤  originalShortPrefix Ps+shortTailExpression Ps+
      (originalPurePrefix Pp+pureTailExpression Pp)+
      (originalMixedPrefix Pm+mixedTailExpression Pm) := by
  have hs:=shortSector_bound Ps
  have hp:=pureSector_bound henv Pp
  have hm:=mixedSector_bound henv Pm
  have hsum:=(hs.1.add hp.1).add hm.1
  have hmaster : Summable (fun ij => GenuineSource.masterTerm (masterEquiv ij)) :=
    hsum.of_nonneg_of_le (fun ij =>
      (GenuineSource.rawPartition_nonneg radius_pos.le _).trans
        (GenuineSource.validPartition_le_master _)) (master_le_sectors Ps Pp Pm)
  have hg:=GenuineSource.genuine_mass_le_master (master_summable_iff _ |>.mp hmaster)
  refine ⟨hg.1,?_⟩
  have he:=hmaster.tsum_le_tsum (master_le_sectors Ps Pp Pm) hsum
  rw [master_tsum_eq] at he
  rw [(hs.1.add hp.1).tsum_add hm.1,hs.1.tsum_add hp.1] at he
  linarith [hg.2,hs.2,hp.2,hm.2]

/-- The original A(1247/2000) < 2024, conditional only on the remaining actual
source envelope and three original finite-prefix acceptance statements.
All three infinite-tail numerical acceptance statements are discharged. -/
theorem mass_four_of_original_prefix_certificates (henv : CompleteSourceEnvelope)
    (hshort : originalShortPrefix 100  ≤  shortPrefixCeiling)
    (hpure : originalPurePrefix 400  ≤  purePrefixCeiling)
    (hmixed : originalMixedPrefix 100  ≤  mixedPrefixCeiling) :
    Summable (fun g => (countFour g:ℝ)*((1247:ℝ)/2000)^g) ∧
      massFour ((1247:ℝ)/2000) < 2024 := by
  have h:=genuine_mass_six_sectors henv 100 400 100
  have hs:=Interval.original_short_tail_le
  have hp:=Interval.original_pure_tail_le
  have hm:=Interval.original_mixed_tail_le
  refine ⟨h.1,?_⟩
  change massFour radius < 2024
  linarith [h.2,six_ceilings_lt_2024]

#print axioms genuine_mass_six_sectors
#print axioms mass_four_of_original_prefix_certificates
end SubmittedGenus.CapFourMass
