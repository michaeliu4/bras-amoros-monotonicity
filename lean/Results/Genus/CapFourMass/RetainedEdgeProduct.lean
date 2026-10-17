import Results.Genus.CapFourMass.PhysicalAssignmentValues
import Results.Genus.CapFourMass.SignedKernelValues
import Results.Genus.CapFourMass.RetainedTailExplicit

/-! Every retained carry-run edge splits into internal tail edges and the
surviving initial and terminal core-port edges, exactly once. -/
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators
namespace SubmittedGenus.CapFourMass.CarryLocalization
open RawGraph RawGraph.Topology FixedPivot SourceCoreFactorization ActualComponent
attribute [local instance] Classical.propDecidable Classical.decEq

lemma product_optional_ends {R : Type*} [CommMonoid R] (n : ℕ) (free loop : Prop) [Decidable free] [Decidable loop] (f : ℕ→R) :
    (∏k : Fin (n+(if free then 0 else 1)+(if loop then 0 else 1)),f k.val)=
      (∏k : Fin n,f (k.val+(if free then 0 else 1)))*
        (if free then 1 else f 0)*(if loop then 1 else f (n+(if free then 0 else 1))) := by
  have hi : (∏k : Fin n,f (k.val+(if free then 0 else 1)))=
      ∏k ∈ Finset.range n,f (k+(if free then 0 else 1)) := by
    exact Fin.prod_univ_eq_prod_range (fun k : ℕ => f (k+(if free then 0 else 1))) n
  rw [hi,Fin.prod_univ_eq_prod_range]
  by_cases hf : free <;> by_cases hl : loop
  · simp [hf,hl]
  · simp [hf,hl,Finset.prod_range_succ]
  · simp [hf,hl,Finset.prod_range_succ',mul_comm]
  · simp only [if_neg hf,if_neg hl]
    rw [Finset.prod_range_succ,Finset.prod_range_succ']

section Run
variable {r N d : ℕ} (hr : 0<r) (hd : 0<d) (hN : d<N) (hbig : 2*d<N)
variable (c : SourceComponent r N d) (a : ModeFiber hr hN hbig c)

lemma freeCarry_edges_optional :
    freeCarrySize N d hN a.val-1=
      (carryTailSize N d hN a.val-1)+(if a.val.val.val+1=d then 0 else 1)+
        (if a.val.val=portPartner N d hN a.val.val then 0 else 1) := by
  have h:=freeCarry_edge_count N d hN hbig a.val
  unfold carryPortArity deletedPrefix at h
  split_ifs at h ⊢ <;> omega

/-- A natural-number accessor used only at the proved finite run positions. -/
def runState (x : c→State) (k : ℕ) : State :=
  if hk : k<freeCarrySize N d hN a.val then x (ownedRunVertex hr hd hN hbig c a ⟨k,hk⟩) else 0

lemma runState_at (x : c→State) (t : Fin (freeCarrySize N d hN a.val)) :
    runState hr hd hN hbig c a x t.val=x (ownedRunVertex hr hd hN hbig c a t) := by
  rw [runState,dif_pos t.isLt]

lemma runEdgeProduct_normalized (choice : Option (CarryRepresentative N d hN)→Mode) (x : c→State) :
    runEdgeProduct hr hd hN hbig c (sourceSignedKernel hd hN choice) x a=
      ∏k : Fin (freeCarrySize N d hN a.val-1),
        normalizedModeEdge (choice (some a.val)) (runState hr hd hN hbig c a x k.val)
          (runState hr hd hN hbig c a x (k.val+1)) := by
  unfold runEdgeProduct
  apply Finset.prod_congr rfl
  intro k _
  rw [sourceSignedKernel_run hr hd hN choice a.val _ _ (Or.inl rfl)]
  change normalizedModeEdge (choice (some a.val))
    (x (ownedRunVertex hr hd hN hbig c a (carryEdgeLeft hr hN hbig c a k)))
    (x (ownedRunVertex hr hd hN hbig c a (carryEdgeRight hr hN hbig c a k)))=_
  exact congrArg₂ (normalizedModeEdge (choice (some a.val)))
    (runState_at hr hd hN hbig c a x (carryEdgeLeft hr hN hbig c a k)).symm
    (runState_at hr hd hN hbig c a x (carryEdgeRight hr hN hbig c a k)).symm


lemma runEdgeProduct_split (choice : Option (CarryRepresentative N d hN)→Mode) (x : c→State) :
    runEdgeProduct hr hd hN hbig c (sourceSignedKernel hd hN choice) x a=
      (∏k : Fin (carryTailSize N d hN a.val-1),
        normalizedModeEdge (choice (some a.val))
          (runState hr hd hN hbig c a x (k.val+(if a.val.val.val+1=d then 0 else 1)))
          (runState hr hd hN hbig c a x (k.val+(if a.val.val.val+1=d then 0 else 1)+1)))*
      (if a.val.val.val+1=d then 1 else normalizedModeEdge (choice (some a.val))
        (runState hr hd hN hbig c a x 0) (runState hr hd hN hbig c a x 1))*
      (if a.val.val=portPartner N d hN a.val.val then 1 else normalizedModeEdge (choice (some a.val))
        (runState hr hd hN hbig c a x ((carryTailSize N d hN a.val-1)+(if a.val.val.val+1=d then 0 else 1)))
        (runState hr hd hN hbig c a x ((carryTailSize N d hN a.val-1)+(if a.val.val.val+1=d then 0 else 1)+1))) := by
  rw [runEdgeProduct_normalized]
  calc
    _=∏ k : Fin ((carryTailSize N d hN a.val-1)+(if a.val.val.val+1=d then 0 else 1)+
        (if a.val.val=portPartner N d hN a.val.val then 0 else 1)),
        normalizedModeEdge (choice (some a.val)) (runState hr hd hN hbig c a x k.val)
          (runState hr hd hN hbig c a x (k.val+1)) :=
      Fintype.prod_equiv (finCongr (freeCarry_edges_optional hr hN hbig c a)) _ _ (fun _ => rfl)
    _=_ := by
      simpa only [Nat.zero_add] using (product_optional_ends
        (carryTailSize N d hN a.val-1) (a.val.val.val+1=d)
        (a.val.val=portPartner N d hN a.val.val)
        (fun k => normalizedModeEdge (choice (some a.val))
          (runState hr hd hN hbig c a x k) (runState hr hd hN hbig c a x (k+1))))

variable (core : CoreAt hN c→State)
variable (tail : (a : ModeFiber hr hN hbig c)→Fin (carryTailSize N d hN a.val)→State)

lemma runState_tail (t : Fin (carryTailSize N d hN a.val)) :
    runState hr hd hN hbig c a ((physicalAssignmentEquiv hr hd hN hbig c).symm (core,tail))
      (t.val+(if a.val.val.val+1=d then 0 else 1))=tail a t := by
  have he : t.val+(if a.val.val.val+1=d then 0 else 1)=
      (retainedTailPosition N d hN a.val t).val := by
    change t.val+(if a.val.val.val+1=d then 0 else 1)=t.val+1-deletedPrefix N d hN a.val
    unfold deletedPrefix
    split_ifs <;> omega
  rw [he,runState_at,physicalAssignment_run_tail]

lemma runState_first (hp : a.val.val.val+1≠d) :
    runState hr hd hN hbig c a ((physicalAssignmentEquiv hr hd hN hbig c).symm (core,tail)) 0=
      localPortState hr hd hN hbig c core (firstModePort hr hN hbig c a) := by
  let t : Fin (freeCarrySize N d hN a.val):=⟨0,freeCarrySize_positive N d hN hbig a.val⟩
  have ht : freeCarryLabel N d hN a.val t.val=(firstModePort hr hN hbig c a).val.val+1 := by
    change carryComponentLabel N d hN a.val (0+deletedPrefix N d hN a.val)=a.val.val.val+1
    rw [deletedPrefix,if_neg hp,Nat.zero_add,carryComponentLabel_first]
  exact (runState_at hr hd hN hbig c a _ t).trans
    (physicalAssignment_run_port hr hd hN hbig c core tail a t _ hp ht)

lemma runState_last (hf : a.val.val≠portPartner N d hN a.val.val) :
    runState hr hd hN hbig c a ((physicalAssignmentEquiv hr hd hN hbig c).symm (core,tail))
      ((carryTailSize N d hN a.val-1)+(if a.val.val.val+1=d then 0 else 1)+1)=
      localPortState hr hd hN hbig c core (lastModePort hr hN hbig c a) := by
  have hsize:=freeCarry_edges_optional hr hN hbig c a
  rw [if_neg hf] at hsize
  have hn:=freeCarrySize_positive N d hN hbig a.val
  let t : Fin (freeCarrySize N d hN a.val):=⟨freeCarrySize N d hN a.val-1,by omega⟩
  have he : (carryTailSize N d hN a.val-1)+(if a.val.val.val+1=d then 0 else 1)+1=t.val := by
    dsimp [t]
    omega
  have hp:=deletedPrefix_le_one N d hN a.val
  have hfull:=componentSize_two N d hN hbig a.val
  have ht : freeCarryLabel N d hN a.val t.val=(lastModePort hr hN hbig c a).val.val+1 := by
    change carryComponentLabel N d hN a.val (freeCarrySize N d hN a.val-1+deletedPrefix N d hN a.val)=
      (portPartner N d hN a.val.val).val+1
    have hi : freeCarrySize N d hN a.val-1+deletedPrefix N d hN a.val=carryComponentSize N d hN a.val-1 := by
      unfold freeCarrySize
      omega
    rw [hi,carryComponentLabel_last_paired N d hN a.val hf]
  rw [he,runState_at]
  exact physicalAssignment_run_port hr hd hN hbig c core tail a t _
    (paired_last_not_pivot hr hN hbig c a hf) ht

end Run
end SubmittedGenus.CapFourMass.CarryLocalization
