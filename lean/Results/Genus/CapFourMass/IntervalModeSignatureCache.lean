import Results.Genus.CapFourMass.IntervalModeSignatures

/-! Whole-source interval products from locally certified numeric component
entries. Cache-key equality checks all run fields and both endpoint masks;
source-program validation retains the original canonical labels separately. -/
namespace SubmittedGenus.CapFourMass.Interval.ModeSignatures
open ActualComponent ExecutableModes RationalTables FixedPivot

variable (C : CachedContext)

def pureProgram {m r p k : ℕ} (L : FreeLayout m r p)
    (entries : Fin k→Entry) (key : Fin L.count→Fin k) : Box :=
  mul C.pivot (prodBoxes (fun c=>(entries (key c)).pureBox))

def absoluteProgram {m r p k : ℕ} (L : FreeLayout m r p)
    (entries : Fin k→Entry) (key : Fin L.count→Fin k) : Box :=
  mul C.pivot (prodBoxes (fun c=>(entries (key c)).absoluteBox))

def mixedProgram {m r p k : ℕ} (L : FreeLayout m r p)
    (entries : Fin k→Entry) (key : Fin L.count→Fin k) : Box :=
  sub (absoluteProgram C L entries key) (pureProgram C L entries key)

def Matches {m r p k : ℕ} {B : Type*} (L : FreeLayout m r p)
    (program : Fin L.count→ModeProgram B) (entries : Fin k→Entry) (key : Fin L.count→Fin k) : Prop :=
  ∀c,physicalSignature L program c=(entries (key c)).signature

instance {m r p k : ℕ} {B : Type*} (L : FreeLayout m r p)
    (program : Fin L.count→ModeProgram B) (entries : Fin k→Entry) (key : Fin L.count→Fin k) :
    Decidable (Matches L program entries key) := by unfold Matches; infer_instance

section Core
variable {r N d k : ℕ} {hN : d<N} (L : FreeLayout (r+N) r (r+d))
variable (program : Fin L.count→ModeProgram (Option (CarryRepresentative N d hN)))
variable (entries : Fin k→Entry) (key : Fin L.count→Fin k) (hk : Matches L program entries key)
include hk

theorem pureProgram_contains : Contains (pureProgram C L entries key) (ExecutableModes.programPure L program) := by
  rw [ExecutableModes.programPure_eq_rational]
  apply mul_contains C.pivot_contains
  apply prodBoxes_contains
  intro c
  have h:=(entries (key c)).pure_contains
  rw [←hk c,physicalSignature_pure] at h
  exact h

theorem absoluteProgram_contains : Contains (absoluteProgram C L entries key) (ExecutableModes.programAbsolute L program) := by
  rw [ExecutableModes.programAbsolute_eq_rational]
  apply mul_contains C.pivot_contains
  apply prodBoxes_contains
  intro c
  have h:=(entries (key c)).absolute_contains
  rw [←hk c,physicalSignature_absolute] at h
  exact h

theorem mixedProgram_contains : Contains (mixedProgram C L entries key) (ExecutableModes.programMixed L program) :=
  sub_contains (absoluteProgram_contains C L program entries key hk)
    (pureProgram_contains C L program entries key hk)

variable (hr : 0<r) (hd : 0<d) (hfar : r+2*d<N) (hL : L.Valid)
variable (hcheck : ∀c,(program c).check hd hN L c=true)
include hr hd hfar hL hcheck

theorem sourcePure_contains : Contains (pureProgram C L entries key) (sourcePure r N d hN) := by
  rw [sourcePure_eq_program hr hd hN hfar L hL program hcheck]
  exact pureProgram_contains C L program entries key hk

theorem sourceMixed_contains : Contains (zeroLower (mixedProgram C L entries key)) (sourceMixed r N d hN) :=
  zeroLower_contains (sourceMixed_nonneg r N d hN)
    (sourceMixed_le_program hr hd hN hfar L hL program hcheck)
    (mixedProgram_contains C L program entries key hk)

end Core

def pureSeries {r d n k : ℕ} (L : FreeLayout (longMultiplicity r d n) r (r+d))
    (entries : Fin k→Entry) (key : Fin L.count→Fin k) : Option Box :=
  normalized r d n (pureProgram C L entries key)

def mixedSeries {r d n k : ℕ} (L : FreeLayout (longMultiplicity r d n) r (r+d))
    (entries : Fin k→Entry) (key : Fin L.count→Fin k) : Option Box :=
  normalized r d n (zeroLower (mixedProgram C L entries key))

private theorem longN_lt (r d n : ℕ) : d<longTailN r d n := by
  have:=longTailN_large r d n
  omega

section Series
variable {r d n k : ℕ} (hr : 0<r) (hd : 0<d)
variable (L : FreeLayout (longMultiplicity r d n) r (r+d)) (hL : L.Valid)
variable (program : Fin L.count→ModeProgram (Option (CarryRepresentative (longTailN r d n) d (longN_lt r d n))))
variable (hcheck : ∀c,(program c).check hd (longN_lt r d n) L c=true)
variable (entries : Fin k→Entry) (key : Fin L.count→Fin k) (hk : Matches L program entries key)
include hk
include hr hd hL hcheck

theorem pureSeries_contains {b : Box} (he : pureSeries C L entries key=some b) :
    Contains b (sourcePureSeries r d n) :=
  normalized_contains (sourcePure_contains C (r:=r) (N:=longTailN r d n) (d:=d)
    L program entries key hk hr hd (longTailN_large r d n) hL hcheck) he

theorem mixedSeries_contains {b : Box} (he : mixedSeries C L entries key=some b) :
    Contains b (sourceMixedSeries r d n) :=
  normalized_contains (sourceMixed_contains C (r:=r) (N:=longTailN r d n) (d:=d)
    L program entries key hk hr hd (longTailN_large r d n) hL hcheck) he

end Series
end SubmittedGenus.CapFourMass.Interval.ModeSignatures
