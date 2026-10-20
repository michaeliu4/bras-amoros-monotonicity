import Results.Genus.CapFourMass.PhysicalSourceFactorization

/-! Signed physical source evaluation in any supplied strict ordering of the
actual component, independent of the choice-based existence ordering. -/
noncomputable section
open scoped BigOperators
namespace SubmittedGenus.CapFourMass.ExecutableModes
open RawGraph RawGraph.SourceModel RawGraph.Topology FixedPivot SourceCoreFactorization CarryLocalization ActualComponent
attribute [local instance] Classical.propDecidable Classical.decEq

section Ordered
variable {r N d : ℕ} (c : SourceComponent r N d)
variable (O : OrderedComponent c.toSimpleGraph)

def orderedVertex (j : Fin (O.edges+1)) : Fin (r+N-1) := (O.label j).val.val

def orderedKernelProduct (K : Fin (r+N-1)→Fin (r+N-1)→State→State→ℝ)
    (x : Fin (O.edges+1)→State) : ℝ :=
  (∏j : Fin O.edges,K (orderedVertex c O j.castSucc) (orderedVertex c O j.succ)
    (x j.castSucc) (x j.succ))*
    (if O.cycle=true then K (orderedVertex c O (Fin.last _)) (orderedVertex c O 0)
      (x (Fin.last _)) (x 0) else 1)

def orderedFullTerm (K : Fin (r+N-1)→Fin (r+N-1)→State→State→ℝ)
    (x : Fin (O.edges+1)→State) : ℝ :=
  (∏j : Fin (O.edges+1),if Domain r (r+d) 4 (orderedVertex c O j) ((x j).val+1)
    then radius^((x j).val+1) else 0)*orderedKernelProduct c O K x

def orderedMass (K : Fin (r+N-1)→Fin (r+N-1)→State→State→ℝ) : ℝ :=
  ∑x : Fin (O.edges+1)→State,orderedFullTerm c O K x

def orderedBoundaryAllowed (x : Fin (O.edges+1)→State) : Prop :=
  O.cycle=false → Domain r (r+d) 4 (orderedVertex c O 0) ((x 0).val+1) ∧
    Domain r (r+d) 4 (orderedVertex c O (Fin.last _)) ((x (Fin.last _)).val+1)

lemma physicalTerm_ordered_with (K : Fin (r+N-1)→Fin (r+N-1)→State→State→ℝ)
    (hsym : ∀i j v w,K i j v w=K j i w v) (x : c→State) :
    physicalTerm c K hsym x=orderedFullTerm c O K (fun j => x (O.label j)) := by
  unfold physicalTerm orderedFullTerm orderedKernelProduct
  rw [←O.label.prod_comp (fun v : c =>
    if Domain r (r+d) 4 v.val.val ((x v).val+1) then radius^((x v).val+1) else 0)]
  rw [O.edge_product_eq_ordered (physicalEdgeWeight c K hsym x)]
  rfl

/-- Reordering is a bijective physical spin reindexing, not an equality assumed
from matching scalar signatures or a cancellation estimate. -/
theorem orderedMass_eq_physical (K : Fin (r+N-1)→Fin (r+N-1)→State→State→ℝ)
    (hsym : ∀i j v w,K i j v w=K j i w v) :
    orderedMass c O K=physicalSignedMass K c := by
  rw [physicalSignedMass_eq_physical c K hsym]
  unfold orderedMass
  apply Fintype.sum_equiv (Equiv.arrowCongr O.label (Equiv.refl State))
  intro x
  rw [physicalTerm_ordered_with c O]
  simp only [Equiv.arrowCongr,Equiv.coe_fn_mk,Function.comp_def,Equiv.symm_apply_apply,Equiv.refl_apply]

end Ordered
end SubmittedGenus.CapFourMass.ExecutableModes
