import Results.Genus.CapFourMass.PhysicalModeFubini
import Results.Genus.CapFourMass.PhysicalAbsoluteBound
import Results.Genus.CapFourMass.PhysicalEmptyModeBound
import Results.Genus.CapFourMass.ZeroEdgeModeSource
import Results.Genus.CapFourMass.SourceModeFactorization
import Results.Genus.CapFourMass.PureOmittedSourceBounds

/-! The original complete core-first absolute spectral source envelope.
Every source coordinate, carry-mode variable, loop and zero-edge corner is
covered by the actual physical component decomposition. -/
noncomputable section
open scoped BigOperators
namespace SubmittedGenus.CapFourMass
open RawGraph RawGraph.Topology FixedPivot SourceCoreFactorization CarryLocalization ActualComponent
attribute [local instance] Classical.propDecidable Classical.decEq
section Source
variable {r N d : ℕ} (hr : 0<r) (hd : 0<d) (hN : d<N) (hbig : 2*d<N) (hfar : r+2*d<N)

include hd in
lemma component_positive_mode_edges (c : SourceComponent r N d) (hn : edgeCount c≠0)
    (a : ModeFiber hr hN hbig c) : 1≤freeCarrySize N d hN a.val-1 := by
  have hp:=freeCarrySize_positive N d hN hbig a.val
  by_contra hh
  have he : freeCarrySize N d hN a.val=1 := by omega
  have hz:=singleton_owner_edgeCount hr hd hN hbig a.val he
  rw [a.property] at hz
  exact hn hz

include hfar in
/-- The local complete-mode sum keeps the entire core contraction inside abs. -/
theorem complete_component_absolute_le (c : SourceComponent r N d) :
    (∑b : ModeFiber hr hN hbig c→Bool,
      |∑core : CoreAt hN c→State,componentModeTerm hr hd hN hbig c core b|)≤
      modeEndpointBudget c*edgeCost c := by
  by_cases hz : edgeCount c=0
  · by_cases ha : Nonempty (ModeFiber hr hN hbig c)
    · exact zero_edge_component_absolute_le hr hd hN hbig c hz ha
    · letI : IsEmpty (ModeFiber hr hN hbig c):=⟨fun a => ha ⟨a⟩⟩
      have hpos : ∀a : ModeFiber hr hN hbig c,1≤freeCarrySize N d hN a.val-1:=fun a => isEmptyElim a
      simpa only [component_coefficient_eq_physical hr hd hN hbig hfar c hpos] using
        physical_empty_mode_absolute_le hr hd hN hbig c inferInstance
  · have hpos:=component_positive_mode_edges hr hd hN hbig c hz
    simpa only [component_coefficient_eq_physical hr hd hN hbig hfar c hpos] using
      physical_positive_absolute_le hr hd hN hbig c hz

include hr hd hbig hfar in
/-- The source-exact cap-four envelope for the complete absolute mode partition,
including all-negative modes, repeated run labels and the isolated loop corner. -/
theorem sourceAbsolute_le_sourceEnvelope :
    sourceAbsolute r N d hN≤sourceEnvelope (r+N) r (r+d) := by
  rw [sourceAbsolute_components hr hd hN hbig]
  apply absolute_product_le_sourceEnvelope (canonicalParameters hr hd hN)
  · intro c
    exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  · intro c
    exact complete_component_absolute_le hr hd hN hbig hfar c

end Source

/-- Discharges the geometric premise used by the original omitted-tail and
six-sector mass assembly. No supplied component layout or mode factorization
is an assumption. -/
theorem completeSourceEnvelope : CompleteSourceEnvelope := by
  intro r N d hr hd hN hfar
  exact sourceAbsolute_le_sourceEnvelope (by omega) hd hN (by omega) hfar

end SubmittedGenus.CapFourMass
