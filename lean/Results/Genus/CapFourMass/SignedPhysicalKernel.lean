import Results.Genus.CapFourMass.SourceModeSlots
import Results.Genus.CapFourMass.SignedUnaryMasks
import Results.Genus.CapFourMass.PhysicalModeWeights

/-! The actual complete-mode signed matrix attached to each physical source
edge, normalized by exactly its two incidence half-weights. -/
noncomputable section
open scoped Matrix
namespace SubmittedGenus.CapFourMass.ActualComponent
open RawGraph RawGraph.SourceModel RawGraph.Topology FixedPivot CarryLocalization
attribute [local instance] Classical.propDecidable Classical.decEq

lemma modeVector_last (j : Mode) : modeVector j (3 : State)=0 := by
  fin_cases j <;> simp [modeVector,qplus,qminus,plusRaw,minusRaw,plusVector,minusVector,halfScale]

lemma labelledModeMatrix_symmetric {B : Type*} (choice : B→Mode) (b : B) (v w : State) :
    labelledModeMatrix choice b v w=labelledModeMatrix choice b w v := by
  simp only [labelledModeMatrix,modeProjector,Matrix.smul_apply,smul_eq_mul]
  ring

lemma tagged_matrix_symmetric {B : Type*} (choice : B→Mode) (e : TaggedEdge B) (v w : State) :
    e.matrixWith (labelledModeMatrix choice) v w=e.matrixWith (labelledModeMatrix choice) w v := by
  cases e with
  | strong => exact congrFun (congrFun (transfer_symmetric 4 4) w) v
  | restricted => exact congrFun (congrFun (transfer_symmetric 4 3) w) v
  | carry b => exact labelledModeMatrix_symmetric choice b v w

section Kernel
variable {r N d : ℕ} (hr : 0<r) (hd : 0<d) (hN : d<N)
variable (choice : Option (CarryRepresentative N d hN)→Mode)

def sourceSignedMatrix (i j : Fin (r+N-1)) : Matrix State State ℝ :=
  if h : (rawGraph (r+N) r (r+d)).Adj i j then
    (taggedEdge hd hN ⟨i,h.2.1⟩ ⟨j,h.2.2.1⟩).matrixWith (labelledModeMatrix choice)
  else 0

def sourceSignedKernel : Fin (r+N-1)→Fin (r+N-1)→State→State→ℝ :=
  normalizedSignedKernel (sourceSignedMatrix hd hN choice)

lemma sourceSignedMatrix_adj {i j : Fin (r+N-1)}
    (h : (rawGraph (r+N) r (r+d)).Adj i j) :
    sourceSignedMatrix hd hN choice i j=
      (taggedEdge hd hN ⟨i,h.2.1⟩ ⟨j,h.2.2.1⟩).matrixWith (labelledModeMatrix choice) := by
  rw [sourceSignedMatrix,dif_pos h]

include hr in
lemma sourceSignedMatrix_symmetric (i j : Fin (r+N-1)) (v w : State) :
    sourceSignedMatrix hd hN choice i j v w=sourceSignedMatrix hd hN choice j i w v := by
  by_cases h : (rawGraph (r+N) r (r+d)).Adj i j
  · rw [sourceSignedMatrix_adj hd hN choice h,sourceSignedMatrix_adj hd hN choice h.symm]
    rw [taggedEdge_symm hr hd hN (u:=⟨i,h.2.1⟩) (v:=⟨j,h.2.2.1⟩) h,tagged_matrix_symmetric]
  · have hn : ¬(rawGraph (r+N) r (r+d)).Adj j i:=fun hh => h hh.symm
    simp only [sourceSignedMatrix,dif_neg h,dif_neg hn,Matrix.zero_apply]

lemma sourceSignedMatrix_carry {i j : Fin (r+N-1)}
    (h : StrongRuns.CarryStep r (r+d) i j) :
    sourceSignedMatrix hd hN choice i j=
      labelledModeMatrix choice (some (runOf hd hN ⟨i,h.1.2.1⟩
        (StrongRuns.carry_endpoint_gt_r (canonicalParameters hr hd hN) h))) := by
  rw [sourceSignedMatrix_adj hd hN choice h.1,taggedEdge_carry hr hd hN h]
  rfl

include hr in
lemma sourceSignedMatrix_carry_support {i j : Fin (r+N-1)}
    (h : StrongRuns.CarryStep r (r+d) i j) (v w : State)
    (hne : sourceSignedMatrix hd hN choice i j v w≠0) : v.val+1≤3 := by
  by_contra hv
  have hv3 : v=(3 : State):=Fin.ext (by have:=v.isLt; omega)
  rw [sourceSignedMatrix_carry hr hd hN choice h,hv3] at hne
  simp only [labelledModeMatrix,modeProjector,Matrix.smul_apply,smul_eq_mul,modeVector_last,zero_mul,mul_zero] at hne
  exact hne rfl

include hr in
lemma sourceSignedKernel_symmetric (i j : Fin (r+N-1)) (v w : State) :
    sourceSignedKernel hd hN choice i j v w=sourceSignedKernel hd hN choice j i w v :=
  normalizedSignedKernel_symmetric _ (sourceSignedMatrix_symmetric hr hd hN choice) i j v w

include hr in
lemma sourceSignedKernel_carry_support {i j : Fin (r+N-1)}
    (h : StrongRuns.CarryStep r (r+d) i j) (v w : State)
    (hne : sourceSignedKernel hd hN choice i j v w≠0) : v.val+1≤3 :=
  normalizedSignedKernel_support _ (fun _ _ h v w => sourceSignedMatrix_carry_support hr hd hN choice h v w) i j h v w hne

include hr in
/-- Every signed occupied physical assignment has exactly the original unary
source masks; the carry threshold itself is expanded spectrally. -/
theorem sourceSignedKernel_masks (c : Component (r+N) r (r+d))
    (x : Fin (edgeCount c+1)→State) :
    (if ∀i,Domain r (r+d) 4 (vertex c i) ((x i).val+1) then (1:ℝ) else 0)*
      signedKernelProduct (sourceSignedKernel hd hN choice) c x=
    (if BoundaryAllowed c x then 1 else 0)*signedKernelProduct (sourceSignedKernel hd hN choice) c x := by
  have hh:=signed_unary_masks _ (sourceSignedKernel_symmetric hr hd hN choice)
    (fun _ _ h v w => sourceSignedKernel_carry_support hr hd hN choice h v w) c x
  by_cases hu : ∀i,Domain r (r+d) 4 (vertex c i) ((x i).val+1) <;>
    by_cases hb : BoundaryAllowed c x <;> simpa only [hu,hb,if_true,if_false] using hh

end Kernel
end SubmittedGenus.CapFourMass.ActualComponent
