import Results.Genus.CapFourMass.OrderedModeCoverage
import Results.Genus.CapFourMass.PhysicalModeFubini
import Results.Genus.CapFourMass.ZeroEdgeModeSource
import Results.Genus.CapFourMass.IsolatedAllPlus

/-! Checked supplied orders evaluate complete core-first source coefficients.
The isolated zero-edge carry mode is a separate exact branch. -/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFourMass.ExecutableModes
open RawGraph RawGraph.Topology FixedPivot SourceCoreFactorization CarryLocalization ActualComponent
attribute [local instance] Classical.propDecidable Classical.decEq

section Source
variable {r N d : ℕ} (hr : 0<r) (hd : 0<d) (hN : d<N) (hbig : 2*d<N) (hfar : r+2*d<N)
variable (c : SourceComponent r N d) (O : OrderedComponent c.toSimpleGraph)

include hr hd hbig in
lemma ordered_positive_modes (hn : O.edges≠0) :
    ∀a : ModeFiber hr hN hbig c,1≤freeCarrySize N d hN a.val-1 := by
  intro a
  have hp:=freeCarrySize_positive N d hN hbig a.val
  by_contra hh
  have he : freeCarrySize N d hN a.val=1:=by omega
  have hz:=singleton_owner_edgeCount hr hd hN hbig a.val he
  rw [a.property] at hz
  exact hn ((ordered_edgeCount c O).trans hz)

include hr hd hbig in
lemma ordered_path_modes (hallowed : O.edges≠0 ∨ physical (orderedVertex c O 0)≤r) :
    ∀a : ModeFiber hr hN hbig c,1≤freeCarrySize N d hN a.val-1 := by
  by_cases hn : O.edges=0
  · have hl:=hallowed.resolve_left (not_ne_iff.mpr hn)
    letI := ordered_zero_low_fiber_empty hr hd hN hbig c O hn hl
    exact fun a => isEmptyElim a
  · exact ordered_positive_modes hr hd hN hbig c O hn

lemma componentChoice_allPlus : componentChoice hr hN hbig c (fun _ => false)=(fun _ => 0) := by
  funext tag
  cases tag with
  | none => rfl
  | some a => simp only [componentChoice,choiceMode,Bool.false_eq_true,if_false]; split_ifs <;> rfl

include hfar in
/-- The exact complete source coefficient in an arbitrary supplied strict order. -/
theorem ordered_coefficient_eq_mass
    (hpos : ∀a : ModeFiber hr hN hbig c,1≤freeCarrySize N d hN a.val-1)
    (b : ModeFiber hr hN hbig c→Bool) :
    (∑x : CoreAt hN c→State,componentModeTerm hr hd hN hbig c x b)=
      orderedMass c O (sourceSignedKernel hd hN (componentChoice hr hN hbig c b)) := by
  rw [component_coefficient_eq_physical hr hd hN hbig hfar c hpos b,
    orderedMass_eq_physical c O _ (sourceSignedKernel_symmetric hr hd hN _)]

include hfar in
/-- The accepted path code preserves every complete shared-label coefficient. -/
theorem ordered_path_coefficient (hc : O.cycle=false)
    (hallowed : O.edges≠0 ∨ physical (orderedVertex c O 0)≤r)
    (code : TaggedPathCode (Option (CarryRepresentative N d hN)))
    (hcheck : pathCodeCheck (pathTags hd hN (orderedVertex c O)) code=true)
    (b : ModeFiber hr hN hbig c→Bool) :
    (∑x : CoreAt hN c→State,componentModeTerm hr hd hN hbig c x b)=
      orderedHalf c O 0 ⬝ᵥ (code.matrixWith
        (labelledModeMatrix (componentChoice hr hN hbig c b))*ᵥ orderedHalf c O (Fin.last _)) := by
  rw [ordered_coefficient_eq_mass hr hd hN hbig hfar c O
      (ordered_path_modes hr hd hN hbig c O hallowed),
    orderedMass_path_eq_tags hr hd hN _ c O hc,
    pathCodeCheck_sound _ _ _ hcheck]

include hfar in
/-- Accepted cyclic rotation preserves the completed signed trace. -/
theorem ordered_cycle_coefficient (hc : O.cycle=true) (rotation : ℕ)
    (first : TaggedBlock (Option (CarryRepresentative N d hN)))
    (rest : List (TaggedBlock (Option (CarryRepresentative N d hN))))
    (hcheck : cycleCodeCheck (cycleTags hd hN (orderedVertex c O)) rotation (first::rest)=true)
    (b : ModeFiber hr hN hbig c→Bool) :
    (∑x : CoreAt hN c→State,componentModeTerm hr hd hN hbig c x b)=
      (((first::rest).map (TaggedBlock.matrixWith
        (labelledModeMatrix (componentChoice hr hN hbig c b)))).prod).trace := by
  have hn : O.edges≠0:=by have := O.cycle_min hc; omega
  rw [ordered_coefficient_eq_mass hr hd hN hbig hfar c O
      (ordered_positive_modes hr hd hN hbig c O hn),
    orderedMass_cycle_eq_tags hr hd hN _ c O hc,
    ←matrix_word_trace_rotate (TaggedEdge.matrixWith
      (labelledModeMatrix (componentChoice hr hN hbig c b)))
      (cycleTags hd hN (orderedVertex c O)) rotation,
    cycleCodeCheck_sound_rotated _ _ _ _ hcheck]

include hr hd hbig in
lemma ordered_isolated_size (hz : O.edges=0) (hh : r<physical (orderedVertex c O 0)) :
    freeCarrySize N d hN (carryLabel hd hN (orderedVertex c O 0))=1 := by
  exact mode_singleton_of_zero_edge hr hd hN hbig c ((ordered_edgeCount c O).symm.trans hz)
    ⟨_,ordered_high_mode_owner hr hd hN hbig c O hh⟩

include hr hd hbig in
/-- The isolated high vertex has one complete two-mode variable. -/
theorem ordered_isolated_absolute (hz : O.edges=0) (hh : r<physical (orderedVertex c O 0)) :
    (∑b : ModeFiber hr hN hbig c→Bool,
      |∑x : CoreAt hN c→State,componentModeTerm hr hd hN hbig c x b|)=
      carryAbsolute 0 freeBoundary loopBoundary := by
  have ho:=ordered_high_mode_owner hr hd hN hbig c O hh
  have hs:=ordered_isolated_size hr hd hN hbig c O hz hh
  generalize ha : carryLabel hd hN (orderedVertex c O 0)=a at ho hs
  cases ho
  exact singleton_component_absolute hr hd hN hbig a hs

include hr hd hbig in
/-- Its distinguished positive coefficient is retained exactly. -/
theorem ordered_isolated_allPlus (hz : O.edges=0) (hh : r<physical (orderedVertex c O 0)) :
    (∑x : CoreAt hN c→State,componentModeTerm hr hd hN hbig c x (fun _ => false))=
      (freeBoundary ⬝ᵥ modeVector 0)*(loopBoundary ⬝ᵥ modeVector 0) := by
  have ho:=ordered_high_mode_owner hr hd hN hbig c O hh
  have hs:=ordered_isolated_size hr hd hN hbig c O hz hh
  generalize ha : carryLabel hd hN (orderedVertex c O 0)=a at ho hs
  cases ho
  exact singleton_component_allPlus hr hd hN hbig a hs

end Source
end SubmittedGenus.CapFourMass.ExecutableModes
