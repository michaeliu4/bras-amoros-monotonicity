import Results.Genus.CapFourMass.CompactModeFamily
import Results.Genus.CapFourMass.IntervalModeSignatureCheck

/-! Compact source-bound numeric certificates. Natural cache keys are bounded,
all endpoint/run signatures match the original labelled program, and each
requested normalized series box is checked. Optional boxes allow the pure
P400 and mixed P100 ranges to retain their distinct original base sets. -/
namespace SubmittedGenus.CapFourMass.Interval.ModeSignatures
open ActualComponent ExecutableModes RationalTables FixedPivot

structure CompactCertificate where
  base : CompactModeBase
  keys : Array ℕ
  pure : Option Box
  mixed : Option Box

namespace CompactCertificate

def KeysValid {k : ℕ} (A : CompactCertificate) : Prop :=
  A.keys.size=A.base.layout.count ∧
  ∀c : Fin A.base.layout.count,A.keys[c.val]?.getD k<k

instance {k : ℕ} (A : CompactCertificate) : Decidable (A.KeysValid (k:=k)) := by
  unfold KeysValid
  infer_instance

def key {k : ℕ} (A : CompactCertificate) (h : A.KeysValid (k:=k))
    (c : Fin A.base.layout.count) : Fin k := ⟨A.keys[c.val]?.getD k,h.2 c⟩

def optionCheck (expected actual : Option Box) : Bool :=
  match expected with
  | none=>true
  | some b=>decide (actual=some b)

theorem optionCheck_sound {expected actual : Option Box}
    (h : optionCheck expected actual=true) {b : Box} (hb : expected=some b) : actual=some b := by
  subst expected
  exact of_decide_eq_true h

def check (C : CachedContext) {k : ℕ} (entries : Fin k→Entry) (A : CompactCertificate) : Bool :=
  if hb : A.base.check=true then
    if hk : A.KeysValid (k:=k) then
      let L:=A.base.acceptedLayout hb
      let key:=A.key hk
      matchesCheck L A.base.program entries key &&
      (A.pure.isSome || A.mixed.isSome) &&
      optionCheck A.pure (pureSeries C L entries key) &&
      optionCheck A.mixed (mixedSeries C L entries key)
    else false
  else false

theorem base_of_check (C : CachedContext) {k : ℕ} (entries : Fin k→Entry)
    {A : CompactCertificate} (h : A.check C entries=true) : A.base.check=true := by
  unfold check at h
  split at h
  · assumption
  · contradiction

theorem keys_of_check (C : CachedContext) {k : ℕ} (entries : Fin k→Entry)
    {A : CompactCertificate} (h : A.check C entries=true) : A.KeysValid (k:=k) := by
  unfold check at h
  split at h
  · split at h
    · assumption
    · contradiction
  · contradiction

theorem fields_of_check (C : CachedContext) {k : ℕ} (entries : Fin k→Entry)
    {A : CompactCertificate} (h : A.check C entries=true) :
    let hb:=base_of_check C entries h
    let hk:=keys_of_check C entries h
    let L:=A.base.acceptedLayout hb
    let key:=A.key hk
    ((matchesCheck L A.base.program entries key=true ∧
      (A.pure.isSome || A.mixed.isSome)=true) ∧
      optionCheck A.pure (pureSeries C L entries key)=true) ∧
      optionCheck A.mixed (mixedSeries C L entries key)=true := by
  have hb:=base_of_check C entries h
  have hk:=keys_of_check C entries h
  simpa only [check,dif_pos hb,dif_pos hk,Bool.and_eq_true] using h

theorem pure_contains (C : CachedContext) {k : ℕ} (entries : Fin k→Entry)
    {A : CompactCertificate} (h : A.check C entries=true) {b : Box} (hb : A.pure=some b) :
    Contains b (sourcePureSeries A.base.r A.base.d A.base.n) := by
  have hs:=base_of_check C entries h
  have hk:=keys_of_check C entries h
  have hf:=fields_of_check C entries h
  have hp:=A.base.parameters_of_check hs
  exact pureSeries_contains C hp.1 hp.2 (A.base.acceptedLayout hs)
    (A.base.acceptedLayout_valid hs) A.base.program (A.base.programs_of_check hs).2
    entries (A.key hk) (matchesCheck_sound _ _ _ _ hf.1.1.1)
    (optionCheck_sound hf.1.2 hb)

theorem mixed_contains (C : CachedContext) {k : ℕ} (entries : Fin k→Entry)
    {A : CompactCertificate} (h : A.check C entries=true) {b : Box} (hb : A.mixed=some b) :
    Contains b (sourceMixedSeries A.base.r A.base.d A.base.n) := by
  have hs:=base_of_check C entries h
  have hk:=keys_of_check C entries h
  have hf:=fields_of_check C entries h
  have hp:=A.base.parameters_of_check hs
  exact mixedSeries_contains C hp.1 hp.2 (A.base.acceptedLayout hs)
    (A.base.acceptedLayout_valid hs) A.base.program (A.base.programs_of_check hs).2
    entries (A.key hk) (matchesCheck_sound _ _ _ _ hf.1.1.1)
    (optionCheck_sound hf.2 hb)

end CompactCertificate
end SubmittedGenus.CapFourMass.Interval.ModeSignatures
