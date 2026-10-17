import Results.Genus.CapFourMass.CompactModeLayout
import Results.Genus.CapFourMass.ExecutableModeGlobal
import Results.Genus.CapFourMass.SourceMultiplicitySums

/-! Indexed original source-base certificates. A single array can store a
bounded prefix or row; all topology and shared-label program obligations are
checked by one reusable interface. Numerical caches and normalizations remain
separate and can consume these exact accepted layouts/programs. -/
namespace SubmittedGenus.CapFourMass.ExecutableModes
open FixedPivot ActualComponent

lemma compactLongN_lt (r d n : ℕ) : d<longTailN r d n := by
  have:=longTailN_large r d n
  omega

/-- Canonical labels remain typed and shared inside the complete source base.
No per-case forward/backward functions or per-vertex proof declarations are
stored. The original base number n is retained without changing its range. -/
structure CompactModeBase where
  r : ℕ
  d : ℕ
  n : ℕ
  layout : CompactLayout
  programs : Array (ModeProgram
    (Option (CarryRepresentative (longTailN r d n) d (compactLongN_lt r d n))))

namespace CompactModeBase

def program (B : CompactModeBase) (c : Fin B.layout.count) : ModeProgram
    (Option (CarryRepresentative (longTailN B.r B.d B.n) B.d
      (compactLongN_lt B.r B.d B.n))) :=
  B.programs[c.val]?.getD .isolated

/-- Program count is exact; no missing program is accepted via the total
accessor's fallback. Every retained label is checked against physical words. -/
def check (B : CompactModeBase) : Bool :=
  if 0<B.r then
    if hd : 0<B.d then
      if hl : B.layout.check (longMultiplicity B.r B.d B.n) B.r (B.r+B.d)=true then
        decide (B.programs.size=B.layout.count ∧
          ∀c, (B.program c).check hd (compactLongN_lt B.r B.d B.n)
            (B.layout.acceptedLayout hl) c=true)
      else false
    else false
  else false

theorem parameters_of_check {B : CompactModeBase} (h : B.check=true) : 0<B.r ∧ 0<B.d := by
  unfold check at h
  split at h
  · split at h
    · exact ⟨by assumption,by assumption⟩
    · contradiction
  · contradiction

theorem layoutCheck_of_check {B : CompactModeBase} (h : B.check=true) :
    B.layout.check (longMultiplicity B.r B.d B.n) B.r (B.r+B.d)=true := by
  unfold check at h
  split at h
  · split at h
    · split at h
      · assumption
      · contradiction
    · contradiction
  · contradiction

def acceptedLayout (B : CompactModeBase) (h : B.check=true) :
    FreeLayout (longMultiplicity B.r B.d B.n) B.r (B.r+B.d) :=
  B.layout.acceptedLayout (layoutCheck_of_check h)

theorem acceptedLayout_valid (B : CompactModeBase) (h : B.check=true) :
    (B.acceptedLayout h).Valid := B.layout.acceptedLayout_valid _

theorem programs_of_check {B : CompactModeBase} (h : B.check=true) :
    B.programs.size=B.layout.count ∧ ∀c,
      (B.program c).check (parameters_of_check h).2 (compactLongN_lt B.r B.d B.n)
        (B.acceptedLayout h) c=true := by
  have hr:=(parameters_of_check h).1
  have hd:=(parameters_of_check h).2
  have hl:=layoutCheck_of_check h
  have hh:=h
  unfold check at hh
  rw [if_pos hr,dif_pos hd,dif_pos hl] at hh
  exact of_decide_eq_true hh

/-- The same exact pure equality and complete mixed upper bound as the old
literal interface, now for an arbitrary accepted indexed original base. -/
theorem accepted_source_values (B : CompactModeBase) (h : B.check=true) :
    sourcePure B.r (longTailN B.r B.d B.n) B.d (compactLongN_lt B.r B.d B.n)=
      programPure (B.acceptedLayout h) B.program ∧
    sourceAbsolute B.r (longTailN B.r B.d B.n) B.d (compactLongN_lt B.r B.d B.n)≤
      programAbsolute (B.acceptedLayout h) B.program ∧
    sourceMixed B.r (longTailN B.r B.d B.n) B.d (compactLongN_lt B.r B.d B.n)≤
      programMixed (B.acceptedLayout h) B.program := by
  have hr:=(parameters_of_check h).1
  have hd:=(parameters_of_check h).2
  have hl:=B.acceptedLayout_valid h
  have hp:=(programs_of_check h).2
  exact ⟨sourcePure_eq_program hr hd _ (longTailN_large B.r B.d B.n) _ hl B.program hp,
    sourceAbsolute_le_program hr hd _ (longTailN_large B.r B.d B.n) _ hl B.program hp,
    sourceMixed_le_program hr hd _ (longTailN_large B.r B.d B.n) _ hl B.program hp⟩

end CompactModeBase

abbrev CompactModeFamily := Array CompactModeBase

namespace CompactModeFamily

def check (F : CompactModeFamily) : Bool := decide (∀i : Fin F.size, F[i].check=true)

@[simp] theorem check_eq_true (F : CompactModeFamily) :
    F.check=true ↔ ∀i : Fin F.size, F[i].check=true := by simp [check]

theorem accepted (F : CompactModeFamily) (h : F.check=true) (i : Fin F.size) :
    F[i].check=true := (F.check_eq_true.mp h) i

def layout (F : CompactModeFamily) (h : F.check=true) (i : Fin F.size) :
    FreeLayout (longMultiplicity F[i].r F[i].d F[i].n) F[i].r (F[i].r+F[i].d) :=
  F[i].acceptedLayout (F.accepted h i)

theorem layout_valid (F : CompactModeFamily) (h : F.check=true) (i : Fin F.size) :
    (F.layout h i).Valid := F[i].acceptedLayout_valid _

end CompactModeFamily
end SubmittedGenus.CapFourMass.ExecutableModes
