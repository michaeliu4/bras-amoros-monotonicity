import Results.Genus.CapFourMass.SignedPhysicalSource
import Results.Genus.CapFourMass.TaggedActualCompiler
import Results.Genus.CapFourMass.TaggedModeSums
import Results.Genus.CapFourMass.ModeRunEnvelope

/-! The actual positive-edge signed physical source, summed over its canonical
complete-mode assignments, obeys the typed absolute-run envelope. Canonical
labels are only injected into independent run slots after the complete scalar
contraction. The isolated zero-edge carry loop is handled separately. -/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFourMass.ActualComponent
open RawGraph RawGraph.Topology FixedPivot CarryLocalization
attribute [local instance] Classical.propDecidable Classical.decEq

variable {r N d : ℕ} (hr : 0 < r) (hd : 0 < d) (hN : d < N) (hbig : 2*d < N)

lemma pure_path_modeFiber_empty (c : Component (r+N) r (r+d))
    (hc : (freeComponentOrder (r+N) r (r+d) c).cycle=false) (hn : edgeCount c≠0)
    (s : Option StrongRun)
    (he : taggedAtoms (taggedPathWord hd hN c)=(TaggedPathCode.pure s).atoms) :
    IsEmpty (ModeFiber hr hN hbig c) := by
  refine ⟨fun a => ?_⟩
  have hm:=component_mode_label_coverage hr hd hN hbig c hn a
  simp only [taggedSourceWord,hc,Bool.false_eq_true,if_false] at hm
  obtain ⟨n,hn',hmem⟩:=carry_mem_taggedAtoms _ (taggedPathWord_compatible hr hd hN c) _ hm
  rw [he] at hmem
  cases s <;> simp [TaggedPathCode.atoms] at hmem

/-- The actual path contraction is completed before taking its absolute value. -/
theorem physical_path_absolute_le (c : Component (r+N) r (r+d))
    (hc : (freeComponentOrder (r+N) r (r+d) c).cycle=false) (hn : edgeCount c≠0) :
    (∑ b : ModeFiber hr hN hbig c→Bool,
      |physicalSignedMass (sourceSignedKernel hd hN (componentChoice hr hN hbig c b)) c|) ≤
      modeEndpointBudget c*edgeCost c := by
  obtain ⟨q,he,hm,hS,hC,hE⟩:=actual_tagged_path hr hd hN c
  have hbound:=path_absolute_le_edgeCost c hc q.erase
    (by simpa only [sourceWord,hc,Bool.false_eq_true,if_false] using hS)
    (by simpa only [sourceWord,hc,Bool.false_eq_true,if_false] using hC)
    (by simpa only [sourceWord,hc,Bool.false_eq_true,if_false] using hE)
    (domainHalf c 0) (domainHalf c (Fin.last _)) (left_energy_kind c) (right_energy_kind c)
  simp_rw [physicalSignedMass_path_eq_tagged hr hd hN _ c hc,hm] 
  cases q with
  | pure s =>
    letI := pure_path_modeFiber_empty hr hd hN hbig c hc hn s he
    simpa [TaggedPathCode.matrixWith,TaggedPathCode.erase,PathCode.absolute] using hbound
  | carried pre tag n hn' bs post =>
    have hinj:=component_slot_injective hr hN hbig c bs tag
      (actual_path_slot_coverage hr hd hN hbig c hc hn pre post tag n hn' bs he)
    exact (tagged_path_absolute_sum_le (componentChoice hr hN hbig c)
      pre post tag n hn' bs (domainHalf c 0) (domainHalf c (Fin.last _)) hinj).trans hbound

/-- Cyclic rotation preserves the complete signed trace before the shared-label
assignment is injected into the independent carry slots. -/
theorem physical_cycle_absolute_le (c : Component (r+N) r (r+d))
    (hc : (freeComponentOrder (r+N) r (r+d) c).cycle=true) :
    (∑ b : ModeFiber hr hN hbig c→Bool,
      |physicalSignedMass (sourceSignedKernel hd hN (componentChoice hr hN hbig c b)) c|) ≤
      modeEndpointBudget c*edgeCost c := by
  obtain ⟨n,bs,hne,he,hm,hS,hC,hE⟩:=actual_tagged_cycle hr hd hN c hc
  have hbound:=cycle_absolute_le_edgeCost c hc (bs.map TaggedBlock.run)
    (by intro hempty; cases bs with
      | nil => exact hne rfl
      | cons b bs => simp at hempty)
    (by simpa only [sourceWord,hc,if_true] using hS)
    (by simpa only [sourceWord,hc,if_true] using hC)
    (by simpa only [sourceWord,hc,if_true] using hE)
  have hword (choice : Option (CarryRepresentative N d hN)→Mode) :
      physicalSignedMass (sourceSignedKernel hd hN choice) c=
        ((bs.map (TaggedBlock.matrixWith (labelledModeMatrix choice))).prod).trace := by
    rw [physicalSignedMass_cycle_eq_tagged hr hd hN choice c hc,
      ←matrix_word_trace_rotate (TaggedEdge.matrixWith (labelledModeMatrix choice))
        (taggedClosedWord hd hN c) n,hm]
  simp_rw [hword]
  cases bs with
  | nil => contradiction
  | cons b bs =>
    have hinj:=component_slot_injective hr hN hbig c bs b.label
      (actual_cycle_slot_coverage hr hd hN hbig c hc n b bs he)
    simpa only [List.map_cons,List.prod_cons] using
      (tagged_cycle_absolute_sum_le (componentChoice hr hN hbig c) b bs hinj).trans hbound

/-- All non-isolated actual components satisfy the original local absolute-mode
budget, with exact source edge counts and actual endpoint masks. -/
theorem physical_positive_absolute_le (c : Component (r+N) r (r+d)) (hn : edgeCount c≠0) :
    (∑ b : ModeFiber hr hN hbig c→Bool,
      |physicalSignedMass (sourceSignedKernel hd hN (componentChoice hr hN hbig c b)) c|) ≤
      modeEndpointBudget c*edgeCost c := by
  cases hc : (freeComponentOrder (r+N) r (r+d) c).cycle with
  | false => exact physical_path_absolute_le hr hd hN hbig c hc hn
  | true => exact physical_cycle_absolute_le hr hd hN hbig c hc

end SubmittedGenus.CapFourMass.ActualComponent
