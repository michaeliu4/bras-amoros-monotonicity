import Results.Genus.CapFourMass.ExecutableModeComponents
import Results.Genus.CapFourMass.ExecutableModeProgram
import Results.Genus.CapFourMass.OrderedModeCoefficients
import Results.Genus.CapFourMass.OrderedModeBounds

/-! Acceptance of one supplied natural-component program discharges the exact
original local core/mode source join. The finite interval evaluator consumes
only the literal layout, endpoint masks and typed program. -/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFourMass.ExecutableModes
open RawGraph RawGraph.Topology FixedPivot SourceCoreFactorization CarryLocalization ActualComponent
attribute [local instance] Classical.propDecidable Classical.decEq

section Source
variable {r N d : ℕ} (hr : 0<r) (hd : 0<d) (hN : d<N) (hbig : 2*d<N) (hfar : r+2*d<N)
variable (L : FreeLayout (r+N) r (r+d)) (hL : L.Valid) (c : Fin L.count)
variable (program : ModeProgram (Option (CarryRepresentative N d hN)))

/-- Literal supplied endpoints coincide with the proof-only actual order. -/
lemma ordered_half_eq_supplied (i : Fin (L.edges c+1)) :
    orderedHalf (componentKey L c) (orderedComponent L hL c) i=L.half c i := rfl

include hr hd hbig hfar hL in
/-- The all-plus contribution is preserved exactly, before any majorization. -/
theorem accepted_component_pure (hcheck : program.check hd hN L c=true) :
    (∑x : CoreAt hN (componentKey L c)→State,
      componentModeTerm hr hd hN hbig (componentKey L c) x (fun _ => false))=
      program.pureValue (L.half c 0) (L.half c (Fin.last _)) := by
  let O:=orderedComponent L hL c
  cases program with
  | path code =>
    obtain ⟨hc,hallowed,hcode⟩:= (ModeProgram.check_path hd hN L c code).mp hcheck
    have he:=ordered_path_coefficient hr hd hN hbig hfar (componentKey L c) O
      hc hallowed code hcode (fun _ => false)
    rw [componentChoice_allPlus] at he
    exact he
  | cycle rotation first rest =>
    obtain ⟨hc,hcode⟩:= (ModeProgram.check_cycle hd hN L c rotation first rest).mp hcheck
    have he:=ordered_cycle_coefficient hr hd hN hbig hfar (componentKey L c) O
      hc rotation first rest hcode (fun _ => false)
    rw [componentChoice_allPlus] at he
    exact he
  | isolated =>
    obtain ⟨_,hz,hh⟩:= (ModeProgram.check_isolated hd hN L c).mp hcheck
    exact ordered_isolated_allPlus hr hd hN hbig (componentKey L c) O hz hh

include hr hd hbig hfar hL in
/-- The canonical choices remain correlated until the injective finite-slot
bound. Absolute values surround each complete core contraction. -/
theorem accepted_component_absolute (hcheck : program.check hd hN L c=true) :
    (∑b : ModeFiber hr hN hbig (componentKey L c)→Bool,
      |∑x : CoreAt hN (componentKey L c)→State,
        componentModeTerm hr hd hN hbig (componentKey L c) x b|)≤
      program.absoluteValue (L.half c 0) (L.half c (Fin.last _)) := by
  let O:=orderedComponent L hL c
  cases program with
  | path code =>
    obtain ⟨hc,hallowed,hcode⟩:= (ModeProgram.check_path hd hN L c code).mp hcheck
    simp_rw [ordered_coefficient_eq_mass hr hd hN hbig hfar (componentKey L c) O
      (ordered_path_modes hr hd hN hbig (componentKey L c) O hallowed)]
    exact ordered_path_absolute_le hr hd hN hbig (componentKey L c) O hc hallowed code hcode
  | cycle rotation first rest =>
    obtain ⟨hc,hcode⟩:= (ModeProgram.check_cycle hd hN L c rotation first rest).mp hcheck
    have hn : O.edges≠0:=by have := O.cycle_min hc; omega
    simp_rw [ordered_coefficient_eq_mass hr hd hN hbig hfar (componentKey L c) O
      (ordered_positive_modes hr hd hN hbig (componentKey L c) O hn)]
    exact ordered_cycle_absolute_le hr hd hN hbig (componentKey L c) O hc rotation (first::rest) hcode
  | isolated =>
    obtain ⟨_,hz,hh⟩:= (ModeProgram.check_isolated hd hN L c).mp hcheck
    exact le_of_eq (ordered_isolated_absolute hr hd hN hbig (componentKey L c) O hz hh)

include hr hd hbig hfar hL in
lemma accepted_component_absolute_nonneg (hcheck : program.check hd hN L c=true) :
    0≤program.absoluteValue (L.half c 0) (L.half c (Fin.last _)) :=
  (Finset.sum_nonneg (fun _ _ => abs_nonneg _)).trans
    (accepted_component_absolute hr hd hN hbig hfar L hL c program hcheck)

end Source
end SubmittedGenus.CapFourMass.ExecutableModes
