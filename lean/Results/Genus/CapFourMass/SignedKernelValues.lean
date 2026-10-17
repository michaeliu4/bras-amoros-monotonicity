import Results.Genus.CapFourMass.SignedPhysicalKernel
import Results.Genus.CapFourMass.CarryEdgePartition

/-! Exact ordinary and carried values of the physical signed source kernel. -/
noncomputable section
open scoped Matrix
namespace SubmittedGenus.CapFourMass.ActualComponent
open RawGraph RawGraph.SourceModel RawGraph.Topology FixedPivot CarryLocalization
attribute [local instance] Classical.propDecidable Classical.decEq

lemma normalized_transfer (t cap : ℕ) (v w : State) :
    transfer t cap v w/(halfWeight v*halfWeight w)=if gate t cap v w then 1 else 0 := by
  unfold transfer
  split_ifs
  · exact div_self (mul_ne_zero (ne_of_gt (halfWeight_pos v)) (ne_of_gt (halfWeight_pos w)))
  · exact zero_div _

section Kernel
variable {r N d : ℕ} (hr : 0<r) (hd : 0<d) (hN : d<N)
variable (choice : Option (CarryRepresentative N d hN)→Mode)

lemma sourceSignedMatrix_strong {i j : Fin (r+N-1)}
    (h : StrongRuns.StrongStep r (r+d) i j) :
    sourceSignedMatrix hd hN choice i j=baseMatrix r (r+d) i j := by
  rw [sourceSignedMatrix_adj hd hN choice h.1]
  unfold taggedEdge kind baseMatrix
  simp only [h.2,if_true]
  split_ifs <;> simp_all [TaggedEdge.matrixWith]

lemma sourceSignedKernel_strong_domains {i j : Fin (r+N-1)}
    (h : StrongRuns.StrongStep r (r+d) i j) (v w : State)
    (hv : Domain r (r+d) 4 i (v.val+1)) (hw : Domain r (r+d) 4 j (w.val+1)) :
    sourceSignedKernel hd hN choice i j v w=
      if 4≤(v.val+1)+(w.val+1) then 1 else 0 := by
  unfold sourceSignedKernel normalizedSignedKernel
  rw [sourceSignedMatrix_strong hd hN choice h]
  unfold baseMatrix
  rw [if_pos h.2]
  by_cases hh : r<physical i ∧ r<physical j
  · rw [if_pos hh]
    have hv' := (((domain_iff_unary i (v.val+1)).mp hv).2 h.1.2.1).2.1
    have hw' := (((domain_iff_unary j (w.val+1)).mp hw).2 h.1.2.2.1).2.1
    have hui : upper r 4 i=3:=by unfold upper; rw [if_neg (by omega)]
    have huj : upper r 4 j=3:=by unfold upper; rw [if_neg (by omega)]
    rw [hui] at hv'
    rw [huj] at hw'
    rw [restrictedMatrix,normalized_transfer]
    simp only [gate,hv',hw',true_and]
  · rw [if_neg hh,strongMatrix,normalized_transfer]
    have hv4 : v.val+1≤4:=by have:=v.isLt; omega
    have hw4 : w.val+1≤4:=by have:=w.isLt; omega
    simp only [gate,hv4,hw4,true_and]

lemma sourceSignedMatrix_run (a : CarryRepresentative N d hN)
    (t s : Fin (freeCarrySize N d hN a)) (hts : t.val+1=s.val ∨ s.val+1=t.val) :
    sourceSignedMatrix hd hN choice (runVertex hr hN a t).val (runVertex hr hN a s).val=
      labelledModeMatrix choice (some a) := by
  have hc:=(run_carry_adj_iff hr hd hN a t s).mpr hts
  have hs : StrongRuns.CarryStep r (r+d) (runVertex hr hN a t).val (runVertex hr hN a s).val:=⟨hc.adj,hc.2⟩
  rw [sourceSignedMatrix_carry hr hd hN choice hs]
  have he : (⟨(runVertex hr hN a t).val,hs.1.2.1⟩ : FreeVertex (r+N) r (r+d))=runVertex hr hN a t:=rfl
  simp only [he,runOf_runVertex]

lemma sourceSignedKernel_run (a : CarryRepresentative N d hN)
    (t s : Fin (freeCarrySize N d hN a)) (hts : t.val+1=s.val ∨ s.val+1=t.val) (v w : State) :
    sourceSignedKernel hd hN choice (runVertex hr hN a t).val (runVertex hr hN a s).val v w=
      modeRoot (choice (some a))*modeVector (choice (some a)) v*modeVector (choice (some a)) w/
        (halfWeight v*halfWeight w) := by
  unfold sourceSignedKernel normalizedSignedKernel
  rw [sourceSignedMatrix_run hr hd hN choice a t s hts]
  simp only [labelledModeMatrix,modeProjector,Matrix.smul_apply,smul_eq_mul]
  ring

end Kernel
end SubmittedGenus.CapFourMass.ActualComponent
