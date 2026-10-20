import Results.Genus.RawGraph.PackedAcceptance.Signatures

/-! Fieldwise finite checks avoid kernel reduction through function-equality
casts in derived dependent-structure equality. Every source field is retained. -/
namespace SubmittedGenus.RawGraph.PackedAcceptance

def SameSignature {a : ℕ} (s t : ComponentSignature a) : Prop :=
  s.edges=t.edges ∧ s.cycle=t.cycle ∧ s.close=t.close ∧
  (∀j : Fin (s.edges+1),∀v,s.mask j v=
    if h:j.val<t.edges+1 then t.mask ⟨j.val,h⟩ v else false) ∧
  (∀j : Fin s.edges,s.bound j=
    if h:j.val<t.edges then t.bound ⟨j.val,h⟩ else 0)

instance {a : ℕ} (s t : ComponentSignature a) : Decidable (SameSignature s t) := by
  unfold SameSignature
  infer_instance

/-- Acceptance proves equality of the entire ordered signature, not merely
agreement of a precomputed component endpoint. -/
theorem sameSignature_sound {a : ℕ} {s t : ComponentSignature a}
    (h : SameSignature s t) : s=t := by
  obtain ⟨se,sm,sb,sc,sz⟩:=s
  obtain ⟨te,tm,tb,tc,tz⟩:=t
  obtain ⟨he,hc,hz,hm,hb⟩:=h
  dsimp only at he hc hz hm hb
  subst te
  have hmask : sm=tm := by
    funext j v
    simpa only [dif_pos j.isLt] using hm j v
  have hbound : sb=tb := by
    funext j
    simpa only [dif_pos j.isLt] using hb j
  subst tm
  subst tb
  subst tc
  subst tz
  rfl

end SubmittedGenus.RawGraph.PackedAcceptance
