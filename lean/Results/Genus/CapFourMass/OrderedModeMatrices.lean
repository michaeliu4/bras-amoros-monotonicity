import Results.Genus.CapFourMass.OrderedModeSource
import Results.Genus.CapFourMass.ExecutableModeMasks
import Results.Genus.CapFourMass.ExecutableModeTags

/-! The full physical signed source in a supplied ordering is exactly its
literal computable tagged matrix word. All unary masks and the closing edge
are retained until the exact signed normalization theorem discharges them. -/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFourMass.ExecutableModes
open RawGraph RawGraph.SourceModel RawGraph.Topology RawGraph.Transfer CapFiveMass.MatrixSource
open FixedPivot SourceCoreFactorization CarryLocalization ActualComponent
attribute [local instance] Classical.propDecidable Classical.decEq

section General
variable {r N d : ℕ} (c : SourceComponent r N d) (O : OrderedComponent c.toSimpleGraph)
variable (K : Fin (r+N-1)→Fin (r+N-1)→State→State→ℝ)

def orderedPathEdges (j : ℕ) : State→State→ℝ :=
  if hj : j<O.edges then K (orderedVertex c O (Fin.castSucc ⟨j,hj⟩))
    (orderedVertex c O (Fin.succ ⟨j,hj⟩)) else fun _ _ => 0

@[simp] lemma orderedPathEdges_fin (j : Fin O.edges) :
    orderedPathEdges c O K j.val=K (orderedVertex c O j.castSucc) (orderedVertex c O j.succ) := by
  simp only [orderedPathEdges,dif_pos j.isLt]

lemma orderedMass_boundary
    (hsym : ∀i j v w,K i j v w=K j i w v)
    (hsupport : ∀i j,StrongRuns.CarryStep r (r+d) i j→∀v w,K i j v w≠0→v.val+1≤3) :
    orderedMass c O K=∑x : Fin (O.edges+1)→State,
      radius^(∑i,((x i).val+1))*
        ((if orderedBoundaryAllowed c O x then 1 else 0)*orderedKernelProduct c O K x) := by
  unfold orderedMass orderedFullTerm
  apply Finset.sum_congr rfl
  intro x _
  rw [Factorization.prod_gate,Finset.prod_pow_eq_pow_sum]
  have hh:=OrderedSource.signed_unary_masks c O K hsym hsupport x
  change (if ∀ i,Domain r (r+d) 4 (orderedVertex c O i) ((x i).val+1) then (1:ℝ) else 0)*
    orderedKernelProduct c O K x = (if orderedBoundaryAllowed c O x then 1 else 0)*
    orderedKernelProduct c O K x at hh
  calc
    _=radius^(∑i,((x i).val+1))*
      ((if ∀i,Domain r (r+d) 4 (orderedVertex c O i) ((x i).val+1) then (1:ℝ) else 0)*
        orderedKernelProduct c O K x) := by split_ifs <;> simp
    _=_ := congrArg (fun v => radius^(∑i,((x i).val+1))*v) hh

lemma orderedMass_path_boundary
    (hsym : ∀i j v w,K i j v w=K j i w v)
    (hsupport : ∀i j,StrongRuns.CarryStep r (r+d) i j→∀v w,K i j v w≠0→v.val+1≤3)
    (hc : O.cycle=false) :
    orderedMass c O K=boundaryPathSource O.edges (fun _ => halfWeight) (orderedPathEdges c O K)
      (fun v => Domain r (r+d) 4 (orderedVertex c O 0) (v.val+1))
      (fun v => Domain r (r+d) 4 (orderedVertex c O (Fin.last _)) (v.val+1)) := by
  rw [orderedMass_boundary c O K hsym hsupport]
  unfold boundaryPathSource
  apply Finset.sum_congr rfl
  intro x _
  simp only [orderedBoundaryAllowed,hc,forall_const,orderedKernelProduct,Bool.false_eq_true,
    if_false,mul_one,sourceTerm,halfWeight_sq,orderedPathEdges_fin,Finset.prod_pow_eq_pow_sum]
  split_ifs <;> simp_all

lemma orderedMass_cycle_source
    (hsym : ∀i j v w,K i j v w=K j i w v)
    (hsupport : ∀i j,StrongRuns.CarryStep r (r+d) i j→∀v w,K i j v w≠0→v.val+1≤3)
    (hc : O.cycle=true) :
    orderedMass c O K=cycleSource O.edges (fun _ v => (halfWeight v)^2)
      (orderedPathEdges c O K) (K (orderedVertex c O (Fin.last _)) (orderedVertex c O 0)) := by
  rw [orderedMass_boundary c O K hsym hsupport]
  unfold cycleSource
  apply Finset.sum_congr rfl
  intro x _
  simp only [orderedBoundaryAllowed,hc,Bool.true_eq_false,false_implies,if_true,one_mul,
    orderedKernelProduct,sourceTerm,halfWeight_sq,orderedPathEdges_fin,Finset.prod_pow_eq_pow_sum]
  ring

end General

section Actual
variable {r N d : ℕ} (hr : 0<r) (hd : 0<d) (hN : d<N)
variable (choice : Option (CarryRepresentative N d hN)→Mode)
variable (c : SourceComponent r N d) (O : OrderedComponent c.toSimpleGraph)

def orderedHalf (j : Fin (O.edges+1)) (v : State) : ℝ :=
  if Domain r (r+d) 4 (orderedVertex c O j) (v.val+1) then halfWeight v else 0

include hr in
lemma ordered_normalized_path :
    matrixRun O.edges (splitMatrix (fun _ => halfWeight) (orderedPathEdges c O (sourceSignedKernel hd hN choice)))=
      ((pathTags hd hN (orderedVertex c O)).map (TaggedEdge.matrixWith (labelledModeMatrix choice))).prod := by
  rw [matrixRun_eq_ofFn_prod]
  simp only [pathTags,List.map_ofFn,Function.comp_def]
  congr 2
  funext j
  ext v w
  simp only [splitMatrix,orderedPathEdges_fin]
  have he : (rawGraph (r+N) r (r+d)).Adj (orderedVertex c O j.castSucc) (orderedVertex c O j.succ) :=
    (O.adjacent_iff _ _).mpr (Or.inl rfl)
  rw [sourceSignedKernel,normalizedSignedKernel_split,sourceSignedMatrix_adj hd hN choice he]
  exact congrArg (fun e => e.matrixWith (labelledModeMatrix choice) v w)
    (edgeTag_eq_source hr hd hN (O.label j.castSucc).val (O.label j.succ).val).symm

include hr in
/-- Exact supplied-order signed path evaluation; the tag word is computable. -/
theorem orderedMass_path_eq_tags (hc : O.cycle=false) :
    orderedMass c O (sourceSignedKernel hd hN choice)=
      orderedHalf c O 0 ⬝ᵥ ((((pathTags hd hN (orderedVertex c O)).map
        (TaggedEdge.matrixWith (labelledModeMatrix choice))).prod)*ᵥ orderedHalf c O (Fin.last _)) := by
  rw [orderedMass_path_boundary c O _ (sourceSignedKernel_symmetric hr hd hN choice)
    (fun _ _ h v w => sourceSignedKernel_carry_support hr hd hN choice h v w) hc,
    boundaryPathSource_eq_matrix,ordered_normalized_path hr hd hN choice c O]
  rfl

include hr in
/-- Exact supplied-order signed cyclic evaluation including its closing edge. -/
theorem orderedMass_cycle_eq_tags (hc : O.cycle=true) :
    orderedMass c O (sourceSignedKernel hd hN choice)=
      (((cycleTags hd hN (orderedVertex c O)).map
        (TaggedEdge.matrixWith (labelledModeMatrix choice))).prod).trace := by
  rw [orderedMass_cycle_source c O _ (sourceSignedKernel_symmetric hr hd hN choice)
    (fun _ _ h v w => sourceSignedKernel_carry_support hr hd hN choice h v w) hc,
    cycleSource_split_exact,ordered_normalized_path hr hd hN choice c O]
  have he : closeMatrix O.edges (fun _ => halfWeight)
      (sourceSignedKernel hd hN choice (orderedVertex c O (Fin.last _)) (orderedVertex c O 0))=
      (edgeTag hd hN (orderedVertex c O (Fin.last _)) (orderedVertex c O 0)).matrixWith
        (labelledModeMatrix choice) := by
    ext v w
    simp only [closeMatrix]
    have ha : (rawGraph (r+N) r (r+d)).Adj (orderedVertex c O (Fin.last _)) (orderedVertex c O 0) :=
      (O.adjacent_iff _ _).mpr (Or.inr (Or.inr ⟨hc,Or.inr ⟨rfl,rfl⟩⟩))
    rw [sourceSignedKernel,normalizedSignedKernel_split,sourceSignedMatrix_adj hd hN choice ha]
    exact congrArg (fun e => e.matrixWith (labelledModeMatrix choice) v w)
      (edgeTag_eq_source hr hd hN (O.label (Fin.last _)).val (O.label 0).val).symm
  rw [he]
  simp only [cycleTags,List.map_append,List.map_cons,List.map_nil,List.prod_append,
    List.prod_cons,List.prod_nil,mul_one]

end Actual
end SubmittedGenus.CapFourMass.ExecutableModes
