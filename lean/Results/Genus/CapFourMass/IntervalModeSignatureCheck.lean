import Results.Genus.CapFourMass.IntervalModeSignatureCache

/-! Fieldwise signature check avoids dependent transports on function-valued
mask equality. All four entries of each mask are checked explicitly. -/
namespace SubmittedGenus.CapFourMass.Interval.ModeSignatures
open ActualComponent ExecutableModes

def Signature.FieldsEq (a b : Signature) : Prop :=
  a.program=b.program ∧ (∀i,a.leftMask i=b.leftMask i) ∧ ∀i,a.rightMask i=b.rightMask i

instance (a b : Signature) : Decidable (a.FieldsEq b) := by unfold Signature.FieldsEq; infer_instance

theorem Signature.eq_of_fields {a b : Signature} (h : a.FieldsEq b) : a=b := by
  rcases a with ⟨ap,al,ar⟩
  rcases b with ⟨bp,bl,br⟩
  rcases h with ⟨hp,hl,hr⟩
  have hl':al=bl:=funext hl
  have hr':ar=br:=funext hr
  cases hp
  cases hl'
  cases hr'
  rfl

def matchesCheck {m r p k : ℕ} {B : Type*} (L : FreeLayout m r p)
    (program : Fin L.count→ModeProgram B) (entries : Fin k→Entry) (key : Fin L.count→Fin k) : Bool :=
  decide (∀c,(physicalSignature L program c).FieldsEq (entries (key c)).signature)

theorem matchesCheck_sound {m r p k : ℕ} {B : Type*} (L : FreeLayout m r p)
    (program : Fin L.count→ModeProgram B) (entries : Fin k→Entry) (key : Fin L.count→Fin k)
    (h : matchesCheck L program entries key=true) : Matches L program entries key := by
  have hf : ∀c,(physicalSignature L program c).FieldsEq (entries (key c)).signature := of_decide_eq_true h
  intro c
  exact Signature.eq_of_fields (hf c)

end SubmittedGenus.CapFourMass.Interval.ModeSignatures
