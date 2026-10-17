import Results.Genus.CapFourMass.PhysicalEdgeFactorization
import Results.Genus.CapFourMass.SignedPhysicalSource

/-! Complete signed physical source sums and exact core/run factorization. -/
noncomputable section
open scoped BigOperators
namespace SubmittedGenus.CapFourMass.CarryLocalization
open RawGraph RawGraph.SourceModel RawGraph.Topology FixedPivot SourceCoreFactorization
attribute [local instance] Classical.propDecidable Classical.decEq

section Source
variable {r N d : ℕ} (hr : 0<r) (hd : 0<d) (hN : d<N) (hbig : 2*d<N)
variable (c : SourceComponent r N d)
variable (K : Fin (r+N-1)→Fin (r+N-1)→State→State→ℝ)
variable (hsym : ∀i j v w,K i j v w=K j i w v)

def physicalTerm (x : c→State) : ℝ :=
  (∏v : c,if Domain r (r+d) 4 v.val.val ((x v).val+1) then radius^((x v).val+1) else 0)*
    ∏e : c.toSimpleGraph.edgeSet,physicalEdgeWeight c K hsym x e.val

lemma physicalTerm_ordered (x : c→State) :
    physicalTerm c K hsym x=
      (∏i : Fin (ActualComponent.edgeCount c+1),
        if Domain r (r+d) 4 (ActualComponent.vertex c i)
          ((x ((freeComponentOrder (r+N) r (r+d) c).label i)).val+1)
        then radius^((x ((freeComponentOrder (r+N) r (r+d) c).label i)).val+1) else 0)*
      ActualComponent.signedKernelProduct K c (fun i => x ((freeComponentOrder (r+N) r (r+d) c).label i)) := by
  unfold physicalTerm
  rw [←(freeComponentOrder (r+N) r (r+d) c).label.prod_comp
    (fun v : c => if Domain r (r+d) 4 v.val.val ((x v).val+1) then radius^((x v).val+1) else 0),
    ←signedKernelProduct_eq_physical c K hsym x]
  rfl

/-- The ordered signed source enumerates each genuine physical assignment once. -/
theorem physicalSignedMass_eq_physical :
    ActualComponent.physicalSignedMass K c=∑x : c→State,physicalTerm c K hsym x := by
  unfold ActualComponent.physicalSignedMass
  apply Fintype.sum_equiv (Equiv.arrowCongr (freeComponentOrder (r+N) r (r+d) c).label (Equiv.refl State))
  intro x
  rw [physicalTerm_ordered]
  simp only [Equiv.arrowCongr,Equiv.coe_fn_mk,Function.comp_def,Equiv.symm_apply_apply,Equiv.refl_apply]

def coreUnaryProduct (x : c→State) : ℝ :=
  ∏k : CoreAt hN c,
    if Domain r (r+d) 4 (coreVertex hN k.val).val ((x (ownedCoreVertex hN c k)).val+1)
    then radius^((x (ownedCoreVertex hN c k)).val+1) else 0

def tailUnaryProduct (x : c→State) (a : ModeFiber hr hN hbig c) : ℝ :=
  ∏t : Fin (carryTailSize N d hN a.val),
    if Domain r (r+d) 4 (tailVertex hr hN a.val t).val
      ((x (componentVertexEquiv hr hd hN hbig c (.inr ⟨a,t⟩))).val+1)
    then radius^((x (componentVertexEquiv hr hd hN hbig c (.inr ⟨a,t⟩))).val+1) else 0

def coreEdgeProduct (x : c→State) : ℝ :=
  ∏ij : {ij // ij∈coreEdgeSet hN c},
    K (coreVertex hN ij.val.1.val).val (coreVertex hN ij.val.2.val).val
      (x (ownedCoreVertex hN c ij.val.1)) (x (ownedCoreVertex hN c ij.val.2))

def runEdgeProduct (x : c→State) (a : ModeFiber hr hN hbig c) : ℝ :=
  ∏k : Fin (freeCarrySize N d hN a.val-1),
    K (runVertex hr hN a.val (carryEdgeLeft hr hN hbig c a k)).val
      (runVertex hr hN a.val (carryEdgeRight hr hN hbig c a k)).val
      (x (ownedRunVertex hr hd hN hbig c a (carryEdgeLeft hr hN hbig c a k)))
      (x (ownedRunVertex hr hd hN hbig c a (carryEdgeRight hr hN hbig c a k)))

/-- Pointwise canonical factorization of the full signed source. Each core
vertex, tail vertex and ordinary/carry edge appears exactly once. -/
theorem physicalTerm_factor (x : c→State) :
    physicalTerm c K hsym x=
      (coreUnaryProduct hN c x*coreEdgeProduct hN c K x)*
        ∏a : ModeFiber hr hN hbig c,
          tailUnaryProduct hr hd hN hbig c x a*runEdgeProduct hr hd hN hbig c K x a := by
  unfold physicalTerm
  have hv:=physical_product_split hr hd hN hbig c
    (fun v : c => if Domain r (r+d) 4 v.val.val ((x v).val+1) then radius^((x v).val+1) else 0)
  have hv' : (∏v : c,if Domain r (r+d) 4 v.val.val ((x v).val+1) then radius^((x v).val+1) else 0)=
      coreUnaryProduct hN c x*(∏a : ModeFiber hr hN hbig c,tailUnaryProduct hr hd hN hbig c x a) := by
    convert hv using 1
    · exact Fintype.prod_equiv (Equiv.refl _) _ _ (fun _ => rfl)
    · unfold coreUnaryProduct tailUnaryProduct
      congr 1
  rw [hv',physical_edge_product_split hr hd hN hbig c K hsym x]
  change (coreUnaryProduct hN c x*(∏a : ModeFiber hr hN hbig c,tailUnaryProduct hr hd hN hbig c x a))*
    (coreEdgeProduct hN c K x*(∏a : ModeFiber hr hN hbig c,runEdgeProduct hr hd hN hbig c K x a))=_
  rw [Finset.prod_mul_distrib]
  ring

/-- Entire core and tail assignments remain inside the same exact finite sum. -/
theorem physicalSignedMass_eq_core_tail :
    ActualComponent.physicalSignedMass K c=
      ∑core : CoreAt hN c→State,
        ∑tail : (a : ModeFiber hr hN hbig c)→Fin (carryTailSize N d hN a.val)→State,
          physicalTerm c K hsym ((physicalAssignmentEquiv hr hd hN hbig c).symm (core,tail)) := by
  rw [physicalSignedMass_eq_physical c K hsym]
  exact physical_sum_split hr hd hN hbig c _

end Source
end SubmittedGenus.CapFourMass.CarryLocalization
