import Results.Genus.CapFourMass.IsolatedCarryRun
import Results.Genus.CapFourMass.SourceModeFactorization
import Results.Genus.CapFourMass.ModeRunEnvelope

/-! The actual isolated carry-loop component has the complete two-mode source
sum, including the negative mode, with the core contracted before absolute value. -/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFourMass.CarryLocalization
open RawGraph RawGraph.Topology FixedPivot SourceCoreFactorization
attribute [local instance] Classical.propDecidable Classical.decEq

section Isolated
variable {r N d : ℕ} (hr : 0<r) (hd : 0<d) (hN : d<N) (hbig : 2*d<N)
variable (a : CarryRepresentative N d hN) (hz : freeCarrySize N d hN a=1)

include hd hz in
lemma singleton_mode_owner (b : CarryRepresentative N d hN)
    (hb : owner hr hN hbig b=owner hr hN hbig a) : b=a := by
  let t : Fin (freeCarrySize N d hN a):=⟨0,by omega⟩
  let s : Fin (freeCarrySize N d hN b):=⟨0,freeCarrySize_positive N d hN hbig b⟩
  have he : runVertex hr hN b s=runVertex hr hN a t :=
    singleton_owner_vertices hr hd hN hbig a hz t _ ((run_owner hr hd hN hbig b s).trans hb)
  exact congrArg Sigma.fst (runVertex_injective hr hd hN (a₁:=⟨b,s⟩) (a₂:=⟨a,t⟩) he)

include hd hz in
lemma singleton_core_empty : IsEmpty (CoreAt hN (owner hr hN hbig a)) := by
  refine ⟨fun k => ?_⟩
  let t : Fin (freeCarrySize N d hN a):=⟨0,by omega⟩
  have he:=singleton_owner_vertices hr hd hN hbig a hz t (coreVertex hN k.val) k.property
  have hhi:=singleton_run_gt_p hr hN hbig a hz t
  rw [←he,coreVertex_physical] at hhi
  have hk:=k.val.val.isLt
  omega

include hd hz in
lemma singleton_port_eq (q : PortAt hr hN hbig (owner hr hN hbig a)) : q.val=a.val := by
  have hb : carryRepresentative N d hN q.val=a :=
    singleton_mode_owner hr hd hN hbig a hz _ q.property
  have hf:=(freeCarry_zero_edge N d hN hbig a hz).2.1
  have hv:=congrArg Subtype.val hb
  change max q.val (portPartner N d hN q.val)=a.val at hv
  by_cases hq : q.val≤portPartner N d hN q.val
  · rw [max_eq_right hq] at hv
    have hh:=congrArg (portPartner N d hN) hv
    rw [portPartner_involutive,←hf] at hh
    exact hh
  · rwa [max_eq_left (le_of_not_ge hq)] at hv

/-- A fixed singleton component has one mode variable, rather than an empty
mode assignment. -/
def singletonMode : ModeFiber hr hN hbig (owner hr hN hbig a) := ⟨a,rfl⟩

def singletonPort : PortAt hr hN hbig (owner hr hN hbig a) :=
  ⟨a.val,by simp only [portOwner,carryRepresentative_of_rep]⟩

include hd hz in
lemma singleton_component_term
    (x : CoreAt hN (owner hr hN hbig a)→State)
    (b : ModeFiber hr hN hbig (owner hr hN hbig a)→Bool) :
    componentModeTerm hr hd hN hbig (owner hr hN hbig a) x b=
      (freeBoundary ⬝ᵥ modeVector (choiceMode (b (singletonMode hr hN hbig a))))*
        (loopBoundary ⬝ᵥ modeVector (choiceMode (b (singletonMode hr hN hbig a)))) := by
  letI : IsEmpty (CoreAt hN (owner hr hN hbig a)):=singleton_core_empty hr hd hN hbig a hz
  letI : Unique (ModeFiber hr hN hbig (owner hr hN hbig a)):=
    ⟨⟨singletonMode hr hN hbig a⟩,fun b => Subtype.ext (singleton_mode_owner hr hd hN hbig a hz b.val b.property)⟩
  letI : Unique (PortAt hr hN hbig (owner hr hN hbig a)):=
    ⟨⟨singletonPort hr hN hbig a⟩,fun q => Subtype.ext (singleton_port_eq hr hd hN hbig a hz q)⟩
  obtain ⟨ha,hf,ht⟩:=freeCarry_zero_edge N d hN hbig a hz
  have hc : componentCoreTerm hN radius (owner hr hN hbig a) x=1 := by
    simp [componentCoreTerm,componentCoreAllowed]
  rw [componentModeTerm,hc,one_mul]
  simp only [componentCarryFactor,Fintype.prod_unique,componentPortFactor]
  change (modeRoot (choiceMode (b (singletonMode hr hN hbig a)))^(carryTailSize N d hN a-1)*
      (if a.val=portPartner N d hN a.val then loopBoundary ⬝ᵥ modeVector (choiceMode (b (singletonMode hr hN hbig a))) else 1))*
    (if hq : a.val.val+1=d then freeBoundary ⬝ᵥ modeVector (portModeAt hr hN hbig b (singletonPort hr hN hbig a)) else _)=_
  rw [if_pos hf,ht,Nat.sub_self,pow_zero,one_mul,dif_pos ha]
  have hp : portModeAt hr hN hbig b (singletonPort hr hN hbig a)=
      choiceMode (b (singletonMode hr hN hbig a)) := by
    unfold portModeAt singletonPort singletonMode
    congr 2
    apply Subtype.ext
    exact carryRepresentative_of_rep N d hN a
  rw [hp,mul_comm]

include hd hz in
/-- The complete actual source sum retains both signs even though this
component has no ordinary edge and no free core variable. -/
theorem singleton_component_absolute :
    (∑ b : ModeFiber hr hN hbig (owner hr hN hbig a)→Bool,
      |∑ x : CoreAt hN (owner hr hN hbig a)→State,
        componentModeTerm hr hd hN hbig (owner hr hN hbig a) x b|)=
      carryAbsolute 0 freeBoundary loopBoundary := by
  letI : IsEmpty (CoreAt hN (owner hr hN hbig a)):=singleton_core_empty hr hd hN hbig a hz
  letI : Unique (ModeFiber hr hN hbig (owner hr hN hbig a)):=
    ⟨⟨singletonMode hr hN hbig a⟩,fun b => Subtype.ext (singleton_mode_owner hr hd hN hbig a hz b.val b.property)⟩
  simp_rw [singleton_component_term hr hd hN hbig a hz]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_eq_zero,pow_zero,
    one_nsmul]
  have he:=(Equiv.funUnique (ModeFiber hr hN hbig (owner hr hN hbig a)) Bool).sum_comp
    (fun b => |(freeBoundary ⬝ᵥ modeVector (choiceMode b))*(loopBoundary ⬝ᵥ modeVector (choiceMode b))|)
  change (∑ b : ModeFiber hr hN hbig (owner hr hN hbig a)→Bool,
    |(freeBoundary ⬝ᵥ modeVector (choiceMode (b (singletonMode hr hN hbig a))))*
      (loopBoundary ⬝ᵥ modeVector (choiceMode (b (singletonMode hr hN hbig a))))|)=_ at ⊢
  simp only [Equiv.funUnique_apply] at he
  have hdefault : (default : ModeFiber hr hN hbig (owner hr hN hbig a))=singletonMode hr hN hbig a := Subsingleton.elim _ _
  rw [hdefault] at he
  rw [he]
  simp [carryAbsolute,Fin.sum_univ_succ,choiceMode,dotProduct_comm,mul_comm,add_comm]

include hd hz in
/-- The exceptional source component satisfies the same global endpoint/edge
budget, using its actual one-free-incidence count. -/
theorem singleton_component_absolute_le :
    (∑ b : ModeFiber hr hN hbig (owner hr hN hbig a)→Bool,
      |∑ x : CoreAt hN (owner hr hN hbig a)→State,
        componentModeTerm hr hd hN hbig (owner hr hN hbig a) x b|)≤
      ActualComponent.modeEndpointBudget (owner hr hN hbig a)*
        ActualComponent.edgeCost (owner hr hN hbig a) := by
  rw [singleton_component_absolute hr hd hN hbig a hz]
  have hn:=singleton_owner_edgeCount hr hd hN hbig a hz
  have hc : (freeComponentOrder (r+N) r (r+d) (owner hr hN hbig a)).cycle=false := by
    cases h : (freeComponentOrder (r+N) r (r+d) (owner hr hN hbig a)).cycle
    · rfl
    · have hh:=(freeComponentOrder (r+N) r (r+d) (owner hr hN hbig a)).cycle_min h
      change 3≤ActualComponent.edgeCount (owner hr hN hbig a) at hh
      omega
  have hw : ActualComponent.sourceWord (owner hr hN hbig a)=[] := by
    rw [ActualComponent.sourceWord,hc]
    simp only [Bool.false_eq_true,if_false]
    apply List.eq_nil_of_length_eq_zero
    rw [ActualComponent.pathWord_length,hn]
  apply ActualComponent.isolated_loop_le_edgeCost
  · simp [hw,ActualComponent.strongLength]
  · simp [hw,ActualComponent.carryLength]
  · simp [hw,ActualComponent.restrictedLength]
  · rw [singleton_owner_free_incidence hr hd hN hbig a hz]

end Isolated
end SubmittedGenus.CapFourMass.CarryLocalization
