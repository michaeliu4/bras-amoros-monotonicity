import Results.Genus.CapFourMass.CarryEdgePartition

/-! Exact tail positions inside the retained canonical carry run. -/
noncomputable section
namespace SubmittedGenus.CapFourMass.CarryLocalization
open RawGraph RawGraph.Topology FixedPivot

section Positions
variable (N d : ℕ) (hN : d<N)

def retainedTailPosition (a : CarryRepresentative N d hN) (t : Fin (carryTailSize N d hN a)) :
    Fin (freeCarrySize N d hN a) :=
  ⟨t.val+1-deletedPrefix N d hN a,by
    have hp:=deletedPrefix_le_one N d hN a
    have ht:=carryTail_position N d hN a t.isLt
    unfold freeCarrySize
    omega⟩

lemma retainedTailPosition_label (a : CarryRepresentative N d hN)
    (t : Fin (carryTailSize N d hN a)) :
    freeCarryLabel N d hN a (retainedTailPosition N d hN a t).val=carryTailLabel N d hN a t.val := by
  have hp:=deletedPrefix_le_one N d hN a
  simp only [retainedTailPosition,freeCarryLabel,carryTailLabel]
  rw [Nat.sub_add_cancel (by omega)]

lemma retainedTailPosition_injective (a : CarryRepresentative N d hN) :
    Function.Injective (retainedTailPosition N d hN a) := by
  intro t s he
  have hh:=congrArg Fin.val he
  have hp:=deletedPrefix_le_one N d hN a
  change t.val+1-deletedPrefix N d hN a=s.val+1-deletedPrefix N d hN a at hh
  apply Fin.ext
  omega

/-- The tail is precisely the nonport positions of the retained run. -/
lemma retainedTailPosition_surjective (a : CarryRepresentative N d hN)
    (s : Fin (freeCarrySize N d hN a)) (hs : d<freeCarryLabel N d hN a s.val) :
    ∃t : Fin (carryTailSize N d hN a),retainedTailPosition N d hN a t=s := by
  have hp:=deletedPrefix_le_one N d hN a
  have hs':=freeCarry_position N d hN a s.isLt
  have hport:=carryComponentLabel_port_iff N d hN a hs'
  have hnot : ¬(s.val+deletedPrefix N d hN a=0 ∨
      (a.val≠portPartner N d hN a.val ∧ s.val+deletedPrefix N d hN a=carryComponentSize N d hN a-1)) := by
    intro h
    have hh:=hport.mpr h
    change carryComponentLabel N d hN a (s.val+deletedPrefix N d hN a)≤d at hh
    change d<carryComponentLabel N d hN a (s.val+deletedPrefix N d hN a) at hs
    omega
  have ht : s.val+deletedPrefix N d hN a-1<carryTailSize N d hN a := by
    unfold carryTailSize carryPortArity
    split_ifs with hf <;> omega
  refine ⟨⟨s.val+deletedPrefix N d hN a-1,ht⟩,Fin.ext ?_⟩
  change s.val+deletedPrefix N d hN a-1+1-deletedPrefix N d hN a=s.val
  omega

def retainedTailEquiv (a : CarryRepresentative N d hN) :
    Fin (carryTailSize N d hN a)≃
      {s : Fin (freeCarrySize N d hN a) // d<freeCarryLabel N d hN a s.val} :=
  Equiv.ofBijective (fun t => ⟨retainedTailPosition N d hN a t,by
    rw [retainedTailPosition_label]
    exact (carryTailLabel_vertex N d hN a t.isLt).1⟩)
    ⟨fun _ _ he => retainedTailPosition_injective N d hN a (congrArg Subtype.val he),by
      intro s
      obtain ⟨t,ht⟩:=retainedTailPosition_surjective N d hN a s.val s.property
      exact ⟨t,Subtype.ext ht⟩⟩

end Positions

lemma retainedTailPosition_vertex {r N d : ℕ} (hr : 0<r) (hN : d<N)
    (a : CarryRepresentative N d hN) (t : Fin (carryTailSize N d hN a)) :
    runVertex hr hN a (retainedTailPosition N d hN a t)=tailVertex hr hN a t := by
  apply Subtype.ext
  apply Fin.ext
  have hh:=runVertex_physical hr hN a (retainedTailPosition N d hN a t)
  rw [retainedTailPosition_label] at hh
  have ht:=tailVertex_physical hr hN a t
  unfold physical at *
  omega

end SubmittedGenus.CapFourMass.CarryLocalization
