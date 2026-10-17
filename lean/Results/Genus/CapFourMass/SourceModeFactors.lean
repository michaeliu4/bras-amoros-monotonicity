import Results.Genus.CapFourMass.SourceCoreFactorization
import Results.Genus.CapFourMass.CarryLocalization
import Results.Genus.CapFourMass.ModePortProduct

/-! Every unary carry-mode factor is localized in the component of its actual
physical port. The removed pivot port is assigned to its own carry tail. -/
namespace SubmittedGenus.CapFourMass.SourceCoreFactorization
open RawGraph RawGraph.SourceModel RawGraph.Topology FixedPivot CarryLocalization
open scoped BigOperators Matrix
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

def portCore {r d : ℕ} (q : Fin d) (hq : q.val+1≠d) : CoreFree r (r+d) :=
  ⟨canonicalPortIndex r d q,by
    change ¬(r+q.val+1=r ∨ r+q.val+1=r+d)
    omega⟩

section Geometry
variable {r N d : ℕ} (hr : 0<r) (hd : 0<d) (hN : d<N) (hbig : 2*d<N)

include hd in
lemma portCore_owner (q : Fin d) (hq : q.val+1≠d) :
    coreOwner hN (portCore (r:=r) q hq)=owner hr hN hbig (carryRepresentative N d hN q) := by
  exact port_owner hr hd hN hbig q hq

def portOwner (q : Fin d) : SourceComponent r N d :=
  owner hr hN hbig (carryRepresentative N d hN q)

abbrev PortAt (c : SourceComponent r N d) := {q : Fin d // portOwner hr hN hbig q=c}

def portCoreAt {c : SourceComponent r N d} (q : PortAt hr hN hbig c) (hq : q.val.val+1≠d) :
    CoreAt hN c :=
  ⟨portCore q.val hq,(portCore_owner hr hd hN hbig q.val hq).trans q.property⟩

def portModeAt {c : SourceComponent r N d} (b : ModeFiber hr hN hbig c→Bool)
    (q : PortAt hr hN hbig c) : Mode :=
  choiceMode (b ⟨carryRepresentative N d hN q.val,q.property⟩)

/-- Total local three-state restriction, agreeing with the actual canonical
port state even on assignments subsequently killed by their unary gate. -/
def portStateAt {c : SourceComponent r N d} (x : CoreAt hN c→State)
    (q : PortAt hr hN hbig c) (hq : q.val.val+1≠d) : Fin 3 :=
  ⟨(x (portCoreAt hr hd hN hbig q hq)).val%3,Nat.mod_lt _ (by omega)⟩

def componentPortFactor (c : SourceComponent r N d) (x : CoreAt hN c→State)
    (b : ModeFiber hr hN hbig c→Bool) (q : PortAt hr hN hbig c) : ℝ :=
  if hq : q.val.val+1=d then freeBoundary ⬝ᵥ modeVector (portModeAt hr hN hbig b q)
  else modeRoot (portModeAt hr hN hbig b q)*
    modeVector (portModeAt hr hN hbig b q) (portStateAt hr hd hN hbig x q hq).castSucc/
      halfWeight (portStateAt hr hd hN hbig x q hq).castSucc

lemma canonicalPortState_extend (x : CoreFree r (r+d)→State) (q : Fin d) (hq : q.val+1≠d) :
    canonicalPortState (extendCore hr (show r<r+d by omega) x) q=
      ⟨(x (portCore (r:=r) q hq)).val%3,Nat.mod_lt _ (by omega)⟩ := by
  apply Fin.ext
  change ((extendCore hr (show r<r+d by omega) x (portCore q hq).val).val-1)%3=_
  rw [extendCore_free]
  simp only [corePositive,Nat.add_sub_cancel]

lemma componentPortFactor_eq (x : CoreFree r (r+d)→State)
    (b : CarryRepresentative N d hN→Bool) (c : SourceComponent r N d)
    (q : PortAt hr hN hbig c) :
    componentPortFactor hr hd hN hbig c (coreAssignmentEquiv hN x c)
      (modeAssignmentEquiv hr hN hbig b c) q=
      sourcePortFactor hd hN (extendCore hr (show r<r+d by omega) x) b q.val := by
  unfold componentPortFactor sourcePortFactor
  by_cases hq : q.val.val+1=d
  · simp only [hq,if_pos ((eq_pivotPort_iff hd q.val).mpr hq)]
    rfl
  · simp only [hq,if_neg (fun h => hq ((eq_pivotPort_iff hd q.val).mp h))]
    rw [canonicalPortState_extend (N:=N) hr hd x q.val hq]
    rfl

def componentCarryFactor (c : SourceComponent r N d) (b : ModeFiber hr hN hbig c→Bool) : ℝ :=
  ∏ a : ModeFiber hr hN hbig c,
    modeRoot (choiceMode (b a))^(carryTailSize N d hN a.val-1)*
      (if a.val.val=portPartner N d hN a.val.val then loopBoundary ⬝ᵥ modeVector (choiceMode (b a)) else 1)

lemma sourceCarryFactor_factor (b : CarryRepresentative N d hN→Bool) :
    sourceCarryFactor N d hN b=
      ∏ c : SourceComponent r N d,componentCarryFactor hr hN hbig c (modeAssignmentEquiv hr hN hbig b c) := by
  unfold sourceCarryFactor sourceLoopFactor componentCarryFactor
  rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_fiberwise (owner hr hN hbig)
    (fun a : CarryRepresentative N d hN =>
      modeRoot (choiceMode (b a))^(carryTailSize N d hN a-1)*
        (if a.val=portPartner N d hN a.val then loopBoundary ⬝ᵥ modeVector (choiceMode (b a)) else 1))).symm

lemma sourcePortFactor_factor (x : CoreFree r (r+d)→State) (b : CarryRepresentative N d hN→Bool) :
    (∏ q : Fin d,sourcePortFactor hd hN (extendCore hr (show r<r+d by omega) x) b q)=
      ∏ c : SourceComponent r N d,∏ q : PortAt hr hN hbig c,
        componentPortFactor hr hd hN hbig c (coreAssignmentEquiv hN x c)
          (modeAssignmentEquiv hr hN hbig b c) q := by
  simp_rw [componentPortFactor_eq]
  exact (Fintype.prod_fiberwise (portOwner hr hN hbig)
    (fun q => sourcePortFactor hd hN (extendCore hr (show r<r+d by omega) x) b q)).symm

/-- A local signed factor: ordinary core gates, each full core vertex weight,
all owned carry tails, and every associated free, loop, or surviving port. -/
def componentModeTerm (c : SourceComponent r N d) (x : CoreAt hN c→State)
    (b : ModeFiber hr hN hbig c→Bool) : ℝ :=
  componentCoreTerm hN radius c x*componentCarryFactor hr hN hbig c b*
    ∏ q : PortAt hr hN hbig c,componentPortFactor hr hd hN hbig c x b q

lemma source_mode_term_factor (x : CoreFree r (r+d)→State) (b : CarryRepresentative N d hN→Bool) :
    freeCoreTerm radius x*sourceCarryFactor N d hN b*
      (∏ q : Fin d,sourcePortFactor hd hN (extendCore hr (show r<r+d by omega) x) b q)=
      ∏ c : SourceComponent r N d,componentModeTerm hr hd hN hbig c
        (coreAssignmentEquiv hN x c) (modeAssignmentEquiv hr hN hbig b c) := by
  rw [freeCoreTerm_factor hN radius,sourceCarryFactor_factor hr hN hbig,sourcePortFactor_factor hr hd hN hbig]
  simp only [componentModeTerm,Finset.prod_mul_distrib]

end Geometry
end
end SubmittedGenus.CapFourMass.SourceCoreFactorization
