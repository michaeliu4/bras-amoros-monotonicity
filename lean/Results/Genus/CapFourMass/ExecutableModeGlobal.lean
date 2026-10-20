import Results.Genus.CapFourMass.ExecutableModeLocal

/-! Source-correct executable whole-core mode evaluation. Finite natural-layout
and typed-program acceptance imply exact original pure values and an upper
bound for the complete original mixed partition, with the all-plus term
subtracted only after the absolute partition. -/
noncomputable section
open scoped BigOperators
namespace SubmittedGenus.CapFourMass.ExecutableModes
open RawGraph RawGraph.Topology FixedPivot SourceCoreFactorization CarryLocalization ActualComponent
attribute [local instance] Classical.propDecidable Classical.decEq

section Source
variable {r N d : ℕ} (hr : 0<r) (hd : 0<d) (hN : d<N) (hfar : r+2*d<N)
variable (L : FreeLayout (r+N) r (r+d)) (hL : L.Valid)
variable (program : Fin L.count→ModeProgram (Option (CarryRepresentative N d hN)))
variable (hcheck : ∀c,(program c).check hd hN L c=true)
include hr hd hfar hL hcheck

/-- The supplied finite component indices are a proved bijective reindexing of
all actual source components. The original two pivot weights occur once. -/
theorem sourcePure_eq_program : sourcePure r N d hN=programPure L program := by
  have hbig : 2*d<N:=by omega
  rw [sourcePure_eq_coefficient,sourceCoefficient_components hr hd hN hbig]
  have hm (c : SourceComponent r N d) :
      modeAssignmentEquiv hr hN hbig (fun _ => false) c=(fun _ => false) := rfl
  simp_rw [hm]
  unfold programPure
  congr 1
  rw [←(componentEquiv L hL).prod_comp (fun c : SourceComponent r N d =>
    ∑x : CoreAt hN c→State,componentModeTerm hr hd hN hbig c x (fun _ => false))]
  apply Finset.prod_congr rfl
  intro c _
  exact accepted_component_pure hr hd hN hbig hfar L hL c (program c) (hcheck c)

/-- Complete canonical signed assignments are bounded after their whole core
contractions. No scalar Covers-only layout or independent-label assumption is
used in this finite executable majorant. -/
theorem sourceAbsolute_le_program : sourceAbsolute r N d hN≤programAbsolute L program := by
  have hbig : 2*d<N:=by omega
  rw [sourceAbsolute_components hr hd hN hbig]
  unfold programAbsolute
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [←(componentEquiv L hL).prod_comp (fun c : SourceComponent r N d =>
    ∑b : ModeFiber hr hN hbig c→Bool,
      |∑x : CoreAt hN c→State,componentModeTerm hr hd hN hbig c x b|)]
  apply Finset.prod_le_prod
  · intro c _
    exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  · intro c _
    exact accepted_component_absolute hr hd hN hbig hfar L hL c (program c) (hcheck c)

/-- This is the original absolute-minus-exact-pure mixed evaluation convention,
including all-negative choices and the isolated zero-edge carry loop. -/
theorem sourceMixed_le_program : sourceMixed r N d hN≤programMixed L program := by
  have ha:=sourceAbsolute_le_program hr hd hN hfar L hL program hcheck
  have hp:=sourcePure_eq_program hr hd hN hfar L hL program hcheck
  rw [sourceAbsolute_eq_pure_add_mixed,hp] at ha
  unfold programMixed
  linarith

lemma programMixed_nonneg : 0≤programMixed L program :=
  (sourceMixed_nonneg r N d hN).trans (sourceMixed_le_program hr hd hN hfar L hL program hcheck)

end Source

/-- Fully explicit certificate-facing source theorem: the finite validator
acceptance discharges the topology premise rather than hiding it in a producer
contract. Every per-component signed program is likewise checked. -/
theorem accepted_source_values {r N d : ℕ} (hr : 0<r) (hd : 0<d) (hN : d<N)
    (hfar : r+2*d<N) (D : FreeLayoutData (r+N) r (r+d)) (hD : D.check=true)
    (program : Fin D.count→ModeProgram (Option (CarryRepresentative N d hN)))
    (hprogram : ∀c,(program c).check hd hN (D.acceptedLayout hD) c=true) :
    sourcePure r N d hN=programPure (D.acceptedLayout hD) program ∧
      sourceAbsolute r N d hN≤programAbsolute (D.acceptedLayout hD) program ∧
      sourceMixed r N d hN≤programMixed (D.acceptedLayout hD) program := by
  have hL:=D.acceptedLayout_valid hD
  exact ⟨sourcePure_eq_program hr hd hN hfar _ hL program hprogram,
    sourceAbsolute_le_program hr hd hN hfar _ hL program hprogram,
    sourceMixed_le_program hr hd hN hfar _ hL program hprogram⟩

end SubmittedGenus.CapFourMass.ExecutableModes
