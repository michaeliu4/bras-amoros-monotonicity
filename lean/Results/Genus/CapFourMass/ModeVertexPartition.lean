import Results.Genus.CapFourMass.SourceModeFactors

/-! Every physical vertex of an actual component is exactly one free core
coordinate or one owned canonical tail coordinate. -/
noncomputable section
namespace SubmittedGenus.CapFourMass.CarryLocalization
open RawGraph RawGraph.Topology FixedPivot SourceCoreFactorization

section Partition
variable {r N d : ℕ} (hr : 0<r) (hd : 0<d) (hN : d<N) (hbig : 2*d<N)

include hd in
lemma tailVertex_sigma_injective : Function.Injective
    (fun v : Σ a : CarryRepresentative N d hN,Fin (carryTailSize N d hN a) =>
      tailVertex hr hN v.1 v.2) := by
  intro v w he
  have hv:=congrArg (fun i : FreeVertex (r+N) r (r+d) => physical i.val) he
  rw [tailVertex_physical,tailVertex_physical] at hv
  apply carryTailMap_injective N d hd hN
  apply Subtype.ext
  change carryTailLabel N d hN v.1 v.2.val=carryTailLabel N d hN w.1 w.2.val
  omega

lemma tailVertex_gt_p (a : CarryRepresentative N d hN) (t : Fin (carryTailSize N d hN a)) :
    r+d<physical (tailVertex hr hN a t).val := by
  rw [tailVertex_physical]
  have hh:=carryTailLabel_vertex N d hN a t.isLt
  omega

lemma coreVertex_le_p (k : CoreFree r (r+d)) : physical (coreVertex hN k).val≤r+d := by
  rw [coreVertex_physical]
  have hh:=k.val.isLt
  omega

abbrev OwnedVertex (c : SourceComponent r N d) :=
  {v : FreeVertex (r+N) r (r+d) // (freeGraph (r+N) r (r+d)).connectedComponentMk v=c}

abbrev ModeVertices (c : SourceComponent r N d) :=
  CoreAt hN c ⊕ (Σ a : ModeFiber hr hN hbig c,Fin (carryTailSize N d hN a.val))

def componentVertexMap (c : SourceComponent r N d) : ModeVertices hr hN hbig c→OwnedVertex c
  | .inl k => ⟨coreVertex hN k.val,k.property⟩
  | .inr ⟨a,t⟩ => ⟨tailVertex hr hN a.val t,(tail_owner hr hN hbig a.val t).trans a.property⟩

include hd in
lemma componentVertexMap_injective (c : SourceComponent r N d) :
    Function.Injective (componentVertexMap hr hN hbig c) := by
  intro u v he
  cases u with
  | inl k =>
    cases v with
    | inl l =>
      congr 1
      apply Subtype.ext
      apply Subtype.ext
      apply Fin.ext
      exact congrArg (fun w : OwnedVertex c => w.val.val.val) he
    | inr v =>
      have hh:=congrArg (fun w : OwnedVertex c => physical w.val.val) he
      have hk:=coreVertex_le_p hN k.val
      have hv:=tailVertex_gt_p hr hN v.1.val v.2
      change physical (coreVertex hN k.val).val=physical (tailVertex hr hN v.1.val v.2).val at hh
      omega
  | inr u =>
    cases v with
    | inl k =>
      have hh:=congrArg (fun w : OwnedVertex c => physical w.val.val) he
      have hk:=coreVertex_le_p hN k.val
      have hu:=tailVertex_gt_p hr hN u.1.val u.2
      change physical (tailVertex hr hN u.1.val u.2).val=physical (coreVertex hN k.val).val at hh
      omega
    | inr v =>
      have hh:=tailVertex_sigma_injective hr hd hN
        (a₁:=⟨u.1.val,u.2⟩) (a₂:=⟨v.1.val,v.2⟩) (congrArg Subtype.val he)
      cases u with
      | mk a t =>
        cases v with
        | mk b s =>
          have hab : a=b := Subtype.ext (congrArg Sigma.fst hh)
          subst b
          have hts : t=s := by cases hh; rfl
          subst s
          rfl

include hd in
lemma componentVertexMap_surjective (c : SourceComponent r N d) :
    Function.Surjective (componentVertexMap hr hN hbig c) := by
  intro v
  by_cases hv : physical v.val.val≤r+d
  · let k : CoreFree r (r+d):=⟨⟨v.val.val.val,by unfold physical at hv; omega⟩,v.val.property⟩
    have he : coreVertex hN k=v.val := by apply Subtype.ext; apply Fin.ext; rfl
    have hk : coreOwner hN k=c := by unfold coreOwner; rw [he]; exact v.property
    exact ⟨.inl ⟨k,hk⟩,Subtype.ext he⟩
  · have hi:=v.val.val.isLt
    have hx : d<physical v.val.val-r ∧ physical v.val.val-r<N := by
      unfold physical at *
      omega
    obtain ⟨⟨a,t⟩,ht⟩:=(carryTailEquiv N d hd hN).surjective ⟨physical v.val.val-r,hx⟩
    have hl : carryTailLabel N d hN a t.val=physical v.val.val-r:=congrArg Subtype.val ht
    have he : tailVertex hr hN a t=v.val := by
      apply Subtype.ext
      apply Fin.ext
      have hh:=tailVertex_physical hr hN a t
      unfold physical at *
      omega
    have ha : owner hr hN hbig a=c := by
      rw [←tail_owner hr hN hbig a t,he]
      exact v.property
    exact ⟨.inr ⟨⟨a,ha⟩,t⟩,Subtype.ext he⟩

/-- A genuine componentwise coordinate equivalence; it introduces no assumed
layout or stored component certificate. -/
def componentVertexEquiv (c : SourceComponent r N d) :
    ModeVertices hr hN hbig c≃OwnedVertex c :=
  Equiv.ofBijective (componentVertexMap hr hN hbig c)
    ⟨componentVertexMap_injective hr hd hN hbig c,componentVertexMap_surjective hr hd hN hbig c⟩

@[simp] lemma componentVertexEquiv_core (c : SourceComponent r N d) (k : CoreAt hN c) :
    (componentVertexEquiv hr hd hN hbig c (.inl k)).val=coreVertex hN k.val := rfl

@[simp] lemma componentVertexEquiv_tail (c : SourceComponent r N d)
    (a : ModeFiber hr hN hbig c) (t : Fin (carryTailSize N d hN a.val)) :
    (componentVertexEquiv hr hd hN hbig c (.inr ⟨a,t⟩)).val=tailVertex hr hN a.val t := rfl

end Partition
end SubmittedGenus.CapFourMass.CarryLocalization
