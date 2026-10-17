import Results.Genus.CapFourMass.IntervalProgramTables
import Results.Genus.CapFourMass.IntervalRefinedInputs
import Results.Genus.CapFourMass.IntervalSourceSyntax

/-! Positive normalization of the original long bases. The mixed source gets
its known zero lower bound only after the shared-label source inequality; the
upper endpoint still comes from signed absolute-minus-pure evaluation. -/
namespace SubmittedGenus.CapFourMass.Interval.RationalTables
open ActualComponent ExecutableModes FixedPivot

def zeroLower (b : Box) : Box := ⟨0,b.hi⟩

theorem zeroLower_contains {b : Box} {x y : ℝ} (hx : 0≤x) (hxy : x≤y) (hy : Contains b y) :
    Contains (zeroLower b) x := by
  constructor
  · simpa only [zeroLower,Int.cast_zero] using mul_nonneg unit_pos.le hx
  · exact (mul_le_mul_of_nonneg_left hxy unit_pos.le).trans hy.2

def normalizerBox : Box := divPos (point 70651823329321825) (point 72057594037927936)

theorem normalizerBox_contains : Contains normalizerBox normalizer := by
  have h:=divPos_contains (point_contains 70651823329321825) (point_contains 72057594037927936) (by decide)
  simpa only [normalizerBox,normalizer,Int.cast_ofNat] using h

def scale (r d n : ℕ) : Option Box :=
  divide (fastPower feedbackRefined (feedbackExponent r (r+d)))
    (fastPower normalizerBox (2*(r+d)+(longMultiplicity r d n-1)%2))

theorem scale_contains {r d n : ℕ} {b : Box} (he : scale r d n=some b) :
    Contains b (normalizationK (longMultiplicity r d n) r (r+d)) :=
  divide_sound (fastPower_contains feedbackRefined_contains _)
    (fastPower_contains normalizerBox_contains _) he

def normalized (r d n : ℕ) (x : Box) : Option Box := do
  let s←scale r d n
  return mul s (mul (fastPower normalizerBox (longMultiplicity r d n-1)) x)

theorem normalized_contains {r d n : ℕ} {xb b : Box} {x : ℝ}
    (hx : Contains xb x) (he : normalized r d n xb=some b) :
    Contains b (normalizationK (longMultiplicity r d n) r (r+d)*
      normalizedMass (longMultiplicity r d n) x) := by
  unfold normalized at he
  cases hs : scale r d n with
  | none => simp [hs] at he
  | some s =>
    simp [hs] at he
    subst b
    exact mul_contains (scale_contains hs)
      (mul_contains (fastPower_contains normalizerBox_contains _) hx)

namespace CachedContext
variable (C : CachedContext)

def pureSeries {r d n : ℕ} (L : FreeLayout (longMultiplicity r d n) r (r+d))
    {B : Type*} (program : Fin L.count→ModeProgram B) : Option Box :=
  normalized r d n (C.programPure L program)

def mixedSeries {r d n : ℕ} (L : FreeLayout (longMultiplicity r d n) r (r+d))
    {B : Type*} (program : Fin L.count→ModeProgram B) : Option Box :=
  normalized r d n (zeroLower (C.programMixed L program))

private theorem longN_lt (r d n : ℕ) : d<longTailN r d n := by
  have:=longTailN_large r d n
  omega

section Source
variable {r d n : ℕ} (hr : 0<r) (hd : 0<d)
variable (L : FreeLayout (longMultiplicity r d n) r (r+d)) (hL : L.Valid)
variable (program : Fin L.count→ModeProgram (Option (CarryRepresentative (longTailN r d n) d (longN_lt r d n))))
variable (hcheck : ∀c,(program c).check hd (longN_lt r d n) L c=true)
include hr hd hL hcheck

theorem pureSeries_contains {b : Box} (he : C.pureSeries L program=some b) :
    Contains b (sourcePureSeries r d n) :=
  normalized_contains (C.sourcePure_contains (r:=r) (N:=longTailN r d n) (d:=d)
    L program hr hd (longTailN_large r d n) hL hcheck) he

theorem mixedSeries_contains {b : Box} (he : C.mixedSeries L program=some b) :
    Contains b (sourceMixedSeries r d n) :=
  normalized_contains (zeroLower_contains (sourceMixed_nonneg r (longTailN r d n) d _)
    (sourceMixed_le_program hr hd _ (longTailN_large r d n) L hL program hcheck)
    (C.programMixed_contains (r:=r) (N:=longTailN r d n) (d:=d) L program)) he

end Source
end CachedContext
end SubmittedGenus.CapFourMass.Interval.RationalTables
