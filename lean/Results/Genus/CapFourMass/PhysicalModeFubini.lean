import Results.Genus.CapFourMass.RetainedEdgeValues
import Results.Genus.CapFourMass.SignedCoreFactorization
import Results.Genus.CapFourMass.SourceModeSlots

/-! The complete core-first coefficient equals its actual signed physical
source, via exact vertex/edge coverage and finite tail contraction. -/
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators
namespace SubmittedGenus.CapFourMass.CarryLocalization
open RawGraph RawGraph.Topology FixedPivot SourceCoreFactorization ActualComponent
attribute [local instance] Classical.propDecidable Classical.decEq
section Fubini
variable {r N d : ℕ} (hr : 0<r) (hd : 0<d) (hN : d<N) (hbig : 2*d<N) (hfar : r+2*d<N)
variable (c : SourceComponent r N d)
variable (choice : Option (CarryRepresentative N d hN)→Mode)

include hfar in
lemma physicalTerm_eq_retained_terms (core : CoreAt hN c→State)
    (tail : (a : ModeFiber hr hN hbig c)→Fin (carryTailSize N d hN a.val)→State) :
    physicalTerm c (sourceSignedKernel hd hN choice) (sourceSignedKernel_symmetric hr hd hN choice)
      ((physicalAssignmentEquiv hr hd hN hbig c).symm (core,tail))=
      componentCoreTerm hN radius c core*
        ∏a : ModeFiber hr hN hbig c,retainedTailTerm N d hN hbig a.val (choice (some a.val))
          (localPortState hr hd hN hbig c core (firstModePort hr hN hbig c a))
          (localPortState hr hd hN hbig c core (lastModePort hr hN hbig c a)) (tail a) := by
  rw [physicalTerm_factor hr hd hN hbig c,signed_core_product hd hN hfar]
  simp only [physicalAssignment_core]
  congr 1
  apply Finset.prod_congr rfl
  intro a _
  exact physical_tail_factor hr hd hN hbig c a choice core tail

include hfar in
/-- All core states are summed jointly, while disjoint tails factor exactly. -/
theorem physicalSignedMass_eq_retained_sums :
    physicalSignedMass (sourceSignedKernel hd hN choice) c=
      ∑core : CoreAt hN c→State,componentCoreTerm hN radius c core*
        ∏a : ModeFiber hr hN hbig c,retainedTailSum N d hN hbig a.val (choice (some a.val))
          (localPortState hr hd hN hbig c core (firstModePort hr hN hbig c a))
          (localPortState hr hd hN hbig c core (lastModePort hr hN hbig c a)) := by
  rw [physicalSignedMass_eq_core_tail hr hd hN hbig c _ (sourceSignedKernel_symmetric hr hd hN choice)]
  simp_rw [physicalTerm_eq_retained_terms hr hd hN hbig hfar c choice]
  apply Finset.sum_congr rfl
  intro core _
  rw [←Finset.mul_sum]
  congr 1
  unfold retainedTailSum
  exact (Fintype.prod_sum (ι:=ModeFiber hr hN hbig c)
    (κ:=fun a => Fin (carryTailSize N d hN a.val)→State)
    (fun (a : ModeFiber hr hN hbig c) (y : Fin (carryTailSize N d hN a.val)→State) => retainedTailTerm N d hN hbig a.val (choice (some a.val))
    (localPortState hr hd hN hbig c core (firstModePort hr hN hbig c a))
    (localPortState hr hd hN hbig c core (lastModePort hr hN hbig c a)) y)).symm

include hfar in
/-- Every complete signed mode coefficient is represented by the actual
physical source. The sole excluded case is an isolated free/loop mode, handled
by its separate exact two-mode identity. Empty mode fibers are included. -/
theorem component_coefficient_eq_physical
    (hpos : ∀a : ModeFiber hr hN hbig c,1≤freeCarrySize N d hN a.val-1)
    (b : ModeFiber hr hN hbig c→Bool) :
    (∑core : CoreAt hN c→State,componentModeTerm hr hd hN hbig c core b)=
      physicalSignedMass (sourceSignedKernel hd hN (componentChoice hr hN hbig c b)) c := by
  rw [physicalSignedMass_eq_retained_sums hr hd hN hbig hfar]
  apply Finset.sum_congr rfl
  intro core _
  rw [componentModeTerm_retained_all]
  congr 1
  apply Finset.prod_congr rfl
  intro a _
  rw [componentChoice_owned,retainedTailSum_eq_source N d hN hbig a.val _ _ _ (hpos a)]

end Fubini
end SubmittedGenus.CapFourMass.CarryLocalization
