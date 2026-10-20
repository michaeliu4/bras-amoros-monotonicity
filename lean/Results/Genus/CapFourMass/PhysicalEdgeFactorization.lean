import Results.Genus.CapFourMass.SourceEdgePartition
import Results.Genus.RawGraph.ComponentEdgeEvaluation
import Results.Genus.CapFourMass.ModeAssignmentPartition
import Results.Genus.CapFourMass.SignedUnaryMasks

/-! Exact signed physical edge and vertex products in canonical core/run
coordinates. These are algebraic identities before any finite sum or absolute value. -/
noncomputable section
open scoped BigOperators
namespace SubmittedGenus.CapFourMass.CarryLocalization
open RawGraph RawGraph.SourceModel RawGraph.Topology FixedPivot SourceCoreFactorization
attribute [local instance] Classical.propDecidable Classical.decEq

section Products
variable {r N d : ℕ} (hr : 0<r) (hd : 0<d) (hN : d<N) (hbig : 2*d<N)
variable (c : SourceComponent r N d)
variable {R : Type*} [CommMonoid R]
variable (K : Fin (r+N-1)→Fin (r+N-1)→State→State→R)
variable (hsym : ∀i j v w,K i j v w=K j i w v)

def physicalEdgeWeight (x : c→State) : Sym2 c→R :=
  Sym2.lift ⟨fun u v => K u.val.val v.val.val (x u) (x v),fun _ _ => hsym _ _ _ _⟩

omit [CommMonoid R] in
@[simp] lemma physicalEdgeWeight_pair (x : c→State) (u v : c) :
    physicalEdgeWeight c K hsym x s(u,v)=K u.val.val v.val.val (x u) (x v) := rfl

/-- Canonical graph products and actual ordered source products are equal. -/
lemma physical_edge_product_ordered (x : c→State) :
    (∏e : c.toSimpleGraph.edgeSet,physicalEdgeWeight c K hsym x e.val)=
      (∏j : Fin (ActualComponent.edgeCount c),
        K (ActualComponent.vertex c j.castSucc) (ActualComponent.vertex c j.succ)
          (x ((freeComponentOrder (r+N) r (r+d) c).label j.castSucc))
          (x ((freeComponentOrder (r+N) r (r+d) c).label j.succ)))*
        (if (freeComponentOrder (r+N) r (r+d) c).cycle=true then
          K (ActualComponent.vertex c (Fin.last _)) (ActualComponent.vertex c 0)
            (x ((freeComponentOrder (r+N) r (r+d) c).label (Fin.last _)))
            (x ((freeComponentOrder (r+N) r (r+d) c).label 0)) else 1) := by
  exact (freeComponentOrder (r+N) r (r+d) c).edge_product_eq_ordered (physicalEdgeWeight c K hsym x)

/-- One factor per upper ordinary core edge and per canonical consecutive
carry edge; signed factors are neither squared nor replaced by indicators. -/
lemma physical_edge_product_split (x : c→State) :
    (∏e : c.toSimpleGraph.edgeSet,physicalEdgeWeight c K hsym x e.val)=
      (∏ij : {ij // ij∈coreEdgeSet hN c},
        K (coreVertex hN ij.val.1.val).val (coreVertex hN ij.val.2.val).val
          (x (ownedCoreVertex hN c ij.val.1)) (x (ownedCoreVertex hN c ij.val.2)))*
      ∏a : ModeFiber hr hN hbig c,∏k : Fin (freeCarrySize N d hN a.val-1),
        K (runVertex hr hN a.val (carryEdgeLeft hr hN hbig c a k)).val
          (runVertex hr hN a.val (carryEdgeRight hr hN hbig c a k)).val
          (x (ownedRunVertex hr hd hN hbig c a (carryEdgeLeft hr hN hbig c a k)))
          (x (ownedRunVertex hr hd hN hbig c a (carryEdgeRight hr hN hbig c a k))) := by
  exact source_edge_product hr hd hN hbig c (physicalEdgeWeight c K hsym x)

end Products

lemma signedKernelProduct_eq_physical {r N d : ℕ} (c : SourceComponent r N d)
    (K : Fin (r+N-1)→Fin (r+N-1)→State→State→ℝ)
    (hsym : ∀i j v w,K i j v w=K j i w v) (x : c→State) :
    ActualComponent.signedKernelProduct K c (fun i => x ((freeComponentOrder (r+N) r (r+d) c).label i))=
      ∏e : c.toSimpleGraph.edgeSet,physicalEdgeWeight c K hsym x e.val :=
  (physical_edge_product_ordered c K hsym x).symm

end SubmittedGenus.CapFourMass.CarryLocalization
