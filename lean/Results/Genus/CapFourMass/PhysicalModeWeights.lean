import Results.Genus.CapFourMass.ModeVertexPartition
import Results.Genus.CapFourMass.SourcePorts

/-! Exact physical unary weights at core ports and canonical tail endpoints. -/
noncomputable section
open scoped Matrix
namespace SubmittedGenus.CapFourMass.CarryLocalization
open RawGraph RawGraph.SourceModel RawGraph.Topology FixedPivot SourceCoreFactorization
attribute [local instance] Classical.propDecidable Classical.decEq

def physicalHalf {m : ℕ} (r p : ℕ) (i : Fin (m-1)) (v : State) : ℝ :=
  if Domain r p 4 i (v.val+1) then halfWeight v else 0

lemma physicalHalf_tail {m r p : ℕ} (hrp : r<p) (i : Fin (m-1))
    (hi : p<physical i) :
    physicalHalf r p i=if SourceModel.CarryLoop r p i then loopBoundary else freeBoundary := by
  have hf : IsFree r p i := by unfold IsFree IsPivot; omega
  have hs : ¬SourceModel.StrongLoop r p i := by unfold SourceModel.StrongLoop; omega
  have hu : upper r 4 i=3 := by unfold upper; rw [if_neg (by omega)]
  funext v
  unfold physicalHalf
  simp only [domain_iff_unary,Unary,show ¬IsPivot r p i from hf,
    false_implies,true_and,hf,forall_const,hu,hs]
  by_cases hc : SourceModel.CarryLoop r p i
  · rw [if_pos hc]
    fin_cases v <;> norm_num [hc,loopBoundary,halfScale]
  · rw [if_neg hc]
    fin_cases v <;> norm_num [hc,freeBoundary,halfScale]

lemma physical_core_domain {r N d : ℕ} (hN : d<N) (hbig : r+2*d<N)
    (k : CoreFree r (r+d)) (v : ℕ) :
    Domain r (r+d) 4 (coreVertex hN k).val v ↔ CoreDomain r (r+d) k.val v := by
  have hk:=k.val.isLt
  have hc : ¬SourceModel.CarryLoop r (r+d) (coreVertex hN k).val := by
    unfold SourceModel.CarryLoop
    rw [coreVertex_physical]
    omega
  rw [domain_iff_unary]
  simp only [Unary,IsFree,IsPivot,StrongLoop,upper,coreVertex_physical,hc,
    false_implies,and_true,CoreDomain]
  rfl

section Ports
variable {r N d : ℕ} (hr : 0<r) (hd : 0<d) (hN : d<N) (hbig : 2*d<N)
variable (c : SourceComponent r N d)

lemma core_port_state {x : CoreAt hN c→State} (hx : componentCoreAllowed hN c x)
    (q : PortAt hr hN hbig c) (hq : q.val.val+1≠d) :
    (portStateAt hr hd hN hbig x q hq).castSucc=x (portCoreAt hr hd hN hbig q hq) := by
  have hh:=hx.1 (portCoreAt hr hd hN hbig q hq)
  have hf : ¬((portCoreAt hr hd hN hbig q hq).val.val.val+1=r ∨
      (portCoreAt hr hd hN hbig q hq).val.val.val+1=r+d):=
    (portCoreAt hr hd hN hbig q hq).val.property
  have hu:=(hh.2 hf).2.1
  have hhi : ¬(portCoreAt hr hd hN hbig q hq).val.val.val+1<r := by
    change ¬r+q.val.val+1<r
    omega
  rw [if_neg hhi] at hu
  apply Fin.ext
  change (x (portCoreAt hr hd hN hbig q hq)).val%3=(x (portCoreAt hr hd hN hbig q hq)).val
  exact Nat.mod_eq_of_lt (by omega)

lemma componentPortFactor_physical {x : CoreAt hN c→State}
    (hx : componentCoreAllowed hN c x) (b : ModeFiber hr hN hbig c→Bool)
    (q : PortAt hr hN hbig c) (hq : q.val.val+1≠d) :
    componentPortFactor hr hd hN hbig c x b q=
      modeRoot (portModeAt hr hN hbig b q)*
        modeVector (portModeAt hr hN hbig b q) (x (portCoreAt hr hd hN hbig q hq))/
          halfWeight (x (portCoreAt hr hd hN hbig q hq)) := by
  rw [componentPortFactor,dif_neg hq,core_port_state hr hd hN hbig c hx q hq]

/-- A port's full physical weight cancels exactly one half-weight denominator. -/
lemma port_full_weight (j : Mode) (v : State) :
    radius^(v.val+1)*(modeRoot j*modeVector j v/halfWeight v)=
      halfWeight v*(modeRoot j*modeVector j v) := by
  rw [←halfWeight_sq]
  field_simp [ne_of_gt (halfWeight_pos v)]

end Ports
end SubmittedGenus.CapFourMass.CarryLocalization
