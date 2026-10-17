import Results.Genus.CapFourMass.SignedPhysicalKernel
import Results.Genus.CapFourMass.SourceExact

/-! A signed complete physical assignment source has one full weight per
coordinate and exactly the actual tagged matrix-word contraction. -/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFourMass.ActualComponent
open RawGraph RawGraph.SourceModel RawGraph.Topology RawGraph.Transfer CapFiveMass.MatrixSource FixedPivot
attribute [local instance] Classical.propDecidable Classical.decEq

section General
variable {m r p : ℕ} (K : Fin (m-1)→Fin (m-1)→State→State→ℝ)

def physicalSignedMass (c : Component m r p) : ℝ :=
  ∑x : Fin (edgeCount c+1)→State,
    (∏i,if Domain r p 4 (vertex c i) ((x i).val+1) then radius^((x i).val+1) else 0)*
      signedKernelProduct K c x

def signedPathEdges (c : Component m r p) (j : ℕ) : State→State→ℝ :=
  if hj : j<edgeCount c then K (vertex c (Fin.castSucc ⟨j,hj⟩)) (vertex c (Fin.succ ⟨j,hj⟩))
  else fun _ _ => 0

@[simp] lemma signedPathEdges_fin (c : Component m r p) (j : Fin (edgeCount c)) :
    signedPathEdges K c j.val=K (vertex c j.castSucc) (vertex c j.succ) := by
  simp only [signedPathEdges,dif_pos j.isLt]

lemma physicalSignedMass_boundary
    (hsym : ∀i j v w,K i j v w=K j i w v)
    (hsupport : ∀i j,StrongRuns.CarryStep r p i j→∀v w,K i j v w≠0→v.val+1≤3)
    (c : Component m r p) :
    physicalSignedMass K c=∑x : Fin (edgeCount c+1)→State,
      radius^(∑i,((x i).val+1))*
        ((if BoundaryAllowed c x then 1 else 0)*signedKernelProduct K c x) := by
  unfold physicalSignedMass
  apply Finset.sum_congr rfl
  intro x _
  rw [Factorization.prod_gate,Finset.prod_pow_eq_pow_sum]
  have hh:=signed_unary_masks K hsym hsupport c x
  calc
    _=radius^(∑i,((x i).val+1))*
      ((if ∀i,Domain r p 4 (vertex c i) ((x i).val+1) then (1:ℝ) else 0)*signedKernelProduct K c x) := by
        split_ifs <;> simp
    _=_ := by
      by_cases hu : ∀i,Domain r p 4 (vertex c i) ((x i).val+1) <;>
        by_cases hb : BoundaryAllowed c x <;>
        simpa [hu,hb] using congrArg (fun v => radius^(∑i,((x i).val+1))*v) hh


lemma physicalSignedMass_path_boundary
    (hsym : ∀i j v w,K i j v w=K j i w v)
    (hsupport : ∀i j,StrongRuns.CarryStep r p i j→∀v w,K i j v w≠0→v.val+1≤3)
    (c : Component m r p) (hc : (freeComponentOrder m r p c).cycle=false) :
    physicalSignedMass K c=boundaryPathSource (edgeCount c) (fun _ => halfWeight) (signedPathEdges K c)
      (fun v => Domain r p 4 (vertex c 0) (v.val+1))
      (fun v => Domain r p 4 (vertex c (Fin.last _)) (v.val+1)) := by
  rw [physicalSignedMass_boundary K hsym hsupport]
  unfold boundaryPathSource
  apply Finset.sum_congr rfl
  intro x _
  simp only [BoundaryAllowed,hc,forall_const,signedKernelProduct,Bool.false_eq_true,if_false,mul_one,
    sourceTerm,halfWeight_sq,signedPathEdges_fin,Finset.prod_pow_eq_pow_sum]
  split_ifs <;> simp_all

lemma physicalSignedMass_cycle_source
    (hsym : ∀i j v w,K i j v w=K j i w v)
    (hsupport : ∀i j,StrongRuns.CarryStep r p i j→∀v w,K i j v w≠0→v.val+1≤3)
    (c : Component m r p) (hc : (freeComponentOrder m r p c).cycle=true) :
    physicalSignedMass K c=cycleSource (edgeCount c) (fun _ v => (halfWeight v)^2)
      (signedPathEdges K c) (K (vertex c (Fin.last _)) (vertex c 0)) := by
  rw [physicalSignedMass_boundary K hsym hsupport]
  unfold cycleSource
  apply Finset.sum_congr rfl
  intro x _
  simp only [BoundaryAllowed,hc,Bool.true_eq_false,false_implies,if_true,one_mul,
    signedKernelProduct,sourceTerm,halfWeight_sq,signedPathEdges_fin,
    Finset.prod_pow_eq_pow_sum]
  ring

end General

lemma normalizedSignedKernel_split {m : ℕ} (A : Fin (m-1)→Fin (m-1)→State→State→ℝ)
    (i j : Fin (m-1)) (v w : State) :
    halfWeight v*normalizedSignedKernel A i j v w*halfWeight w=A i j v w := by
  unfold normalizedSignedKernel
  field_simp [ne_of_gt (halfWeight_pos v),ne_of_gt (halfWeight_pos w)]

section Actual
variable {r N d : ℕ} (hr : 0<r) (hd : 0<d) (hN : d<N)
variable (choice : Option (CarryRepresentative N d hN)→Mode)

lemma normalized_tagged_path (c : Component (r+N) r (r+d)) :
    matrixRun (edgeCount c) (splitMatrix (fun _ => halfWeight) (signedPathEdges (sourceSignedKernel hd hN choice) c))=
      ((taggedPathWord hd hN c).map (TaggedEdge.matrixWith (labelledModeMatrix choice))).prod := by
  rw [matrixRun_eq_ofFn_prod]
  simp only [taggedPathWord,List.map_ofFn,Function.comp_def]
  congr 2
  funext j
  ext v w
  simp only [splitMatrix,signedPathEdges_fin]
  rw [sourceSignedKernel,normalizedSignedKernel_split,sourceSignedMatrix_adj hd hN choice (consecutive_adj c j)]
  rfl

include hr in
/-- Exact signed word for the actual physical source, before absolute values. -/
theorem physicalSignedMass_path_eq_tagged (c : Component (r+N) r (r+d))
    (hc : (freeComponentOrder (r+N) r (r+d) c).cycle=false) :
    physicalSignedMass (sourceSignedKernel hd hN choice) c=
      domainHalf c 0 ⬝ᵥ ((((taggedPathWord hd hN c).map
        (TaggedEdge.matrixWith (labelledModeMatrix choice))).prod)*ᵥ domainHalf c (Fin.last _)) := by
  rw [physicalSignedMass_path_boundary _ (sourceSignedKernel_symmetric hr hd hN choice)
    (fun _ _ h v w => sourceSignedKernel_carry_support hr hd hN choice h v w) c hc,
    boundaryPathSource_eq_matrix,normalized_tagged_path]
  rfl

include hr in
/-- The actual closing edge and state are retained in the signed cyclic source. -/
theorem physicalSignedMass_cycle_eq_tagged (c : Component (r+N) r (r+d))
    (hc : (freeComponentOrder (r+N) r (r+d) c).cycle=true) :
    physicalSignedMass (sourceSignedKernel hd hN choice) c=
      (((taggedClosedWord hd hN c).map (TaggedEdge.matrixWith (labelledModeMatrix choice))).prod).trace := by
  rw [physicalSignedMass_cycle_source _ (sourceSignedKernel_symmetric hr hd hN choice)
    (fun _ _ h v w => sourceSignedKernel_carry_support hr hd hN choice h v w) c hc,
    cycleSource_split_exact,normalized_tagged_path]
  have he : closeMatrix (edgeCount c) (fun _ => halfWeight)
      (sourceSignedKernel hd hN choice (vertex c (Fin.last _)) (vertex c 0))=
      (taggedEdge hd hN (sourceFreeVertex c (Fin.last _)) (sourceFreeVertex c 0)).matrixWith
        (labelledModeMatrix choice) := by
    ext v w
    simp only [closeMatrix]
    rw [sourceSignedKernel,normalizedSignedKernel_split,sourceSignedMatrix_adj hd hN choice (closing_adj c hc)]
    rfl
  rw [he]
  simp only [taggedClosedWord,List.map_append,List.map_cons,List.map_nil,List.prod_append,
    List.prod_cons,List.prod_nil,mul_one]

end Actual
end SubmittedGenus.CapFourMass.ActualComponent
