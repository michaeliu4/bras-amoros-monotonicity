import Results.Genus.CapFourMass.PhysicalAbsoluteBound

/-! Empty canonical mode fibers contribute one complete physical contraction.
This includes isolated core and strong-loop vertices, without an edge-count
hypothesis or an artificial carry mode. -/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFourMass.ActualComponent
open RawGraph RawGraph.Topology FixedPivot CarryLocalization
attribute [local instance] Classical.propDecidable Classical.decEq

variable {r N d : ℕ} (hr : 0 < r) (hd : 0 < d) (hN : d < N) (hbig : 2*d < N)

/-- Empty source mode fibers require no positive-edge premise. In particular,
an isolated core/strong-loop path has its actual complete scalar only once. -/
theorem physical_empty_mode_absolute_le (c : Component (r+N) r (r+d))
    (hempty : IsEmpty (ModeFiber hr hN hbig c)) :
    (∑ b : ModeFiber hr hN hbig c→Bool,
      |physicalSignedMass (sourceSignedKernel hd hN (componentChoice hr hN hbig c b)) c|) ≤
      modeEndpointBudget c*edgeCost c := by
  letI := hempty
  cases hc : (freeComponentOrder (r+N) r (r+d) c).cycle with
  | true => exact physical_cycle_absolute_le hr hd hN hbig c hc
  | false =>
    obtain ⟨q,_,hm,hS,hC,hE⟩:=actual_tagged_path hr hd hN c
    have hbound:=path_absolute_le_edgeCost c hc q.erase
      (by simpa only [sourceWord,hc,Bool.false_eq_true,if_false] using hS)
      (by simpa only [sourceWord,hc,Bool.false_eq_true,if_false] using hC)
      (by simpa only [sourceWord,hc,Bool.false_eq_true,if_false] using hE)
      (domainHalf c 0) (domainHalf c (Fin.last _)) (left_energy_kind c) (right_energy_kind c)
    simp_rw [physicalSignedMass_path_eq_tagged hr hd hN _ c hc,hm]
    cases q with
    | pure s =>
      simpa [TaggedPathCode.matrixWith,TaggedPathCode.erase,PathCode.absolute] using hbound
    | carried pre tag n hn bs post =>
      exact (tagged_path_absolute_sum_le (componentChoice hr hN hbig c)
        pre post tag n hn bs (domainHalf c 0) (domainHalf c (Fin.last _))
        (fun _ _ _ => Subsingleton.elim _ _)).trans hbound

end SubmittedGenus.CapFourMass.ActualComponent
