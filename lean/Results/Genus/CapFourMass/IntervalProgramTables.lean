import Results.Genus.CapFourMass.IntervalMatrixChain
import Results.Genus.CapFourMass.RationalModeProgram
import Results.Genus.CapFourMass.ExecutableModeGlobal
import Results.Genus.CapFourMass.IntervalBounds

/-! Source-bound signed interval programs with certified matrix caches. The
shared labels survive in the checked program; erasure occurs only in the
proved independent absolute majorant, before exact all-plus subtraction. -/
open scoped Matrix BigOperators
namespace SubmittedGenus.CapFourMass.Interval.RationalTables
open ActualComponent ExecutableModes FixedPivot MatrixTables

namespace CachedContext
variable (C : CachedContext) {B : Type*}

def pathPure (q : TaggedPathCode B) (x y : Vector 4) : Box :=
  match q with
  | .pure s => C.toContext.weightedDot x (action (C.toContext.frame s) y)
  | .carried pre _ n _ bs post =>
    mul (mul (C.toContext.start pre n x 0)
      (scalarProduct (bs.map (fun b=>C.toContext.block b.run 0 0))))
      (C.toContext.finish post y 0)

def pathAbs (q : TaggedPathCode B) (x y : Vector 4) : Box :=
  match q with
  | .pure s => absolute (C.toContext.weightedDot x (action (C.toContext.frame s) y))
  | .carried pre _ n _ bs post => C.pathAbsolute pre post n (bs.map TaggedBlock.run) x y

def cyclePure (bs : List (TaggedBlock B)) : Box :=
  scalarProduct (bs.map (fun b=>C.toContext.block b.run 0 0))

def freeBoxes : Vector 4 := ![point 1,point 1,point 1,point 0]
def loopBoxes : Vector 4 := ![point 0,point 1,point 1,point 0]

private theorem freeBoxes_contains : VContains freeBoxes ![1,1,1,0] := by
  intro i
  fin_cases i <;> first | simpa [freeBoxes] using point_contains 1 | simpa [freeBoxes] using point_contains 0

private theorem loopBoxes_contains : VContains loopBoxes ![0,1,1,0] := by
  intro i
  fin_cases i <;> first | simpa [loopBoxes] using point_contains 1 | simpa [loopBoxes] using point_contains 0

def isolatedPure : Box :=
  mul (C.toContext.start none 0 freeBoxes 0) (C.toContext.finish none loopBoxes 0)

def isolatedAbsolute : Box := C.pathAbsolute none none 0 [] freeBoxes loopBoxes

theorem pathPure_contains (q : TaggedPathCode B) {xb yb : Vector 4} {x y : State→ℝ}
    (hx : VContains xb x) (hy : VContains yb y) :
    Contains (C.pathPure q xb yb) (RationalRuns.pathPure q x y) := by
  cases q with
  | pure s =>
      exact C.toContext.weightedDot_contains hx
        (action_contains (C.toContext.frame_contains s) hy)
  | carried pre tag n hn bs post =>
      exact mul_contains
        (mul_contains (C.toContext.start_contains pre n hx 0)
          (scalarProduct_contains bs (fun b=>C.toContext.block b.run 0 0)
            (fun b=>RationalRuns.block b.run 0 0) (fun b=>C.toContext.block_contains b.run 0 0)))
        (C.toContext.finish_contains post hy 0)

theorem pathAbs_contains (q : TaggedPathCode B) {xb yb : Vector 4} {x y : State→ℝ}
    (hx : VContains xb x) (hy : VContains yb y) :
    Contains (C.pathAbs q xb yb) (RationalRuns.pathAbs q x y) := by
  cases q with
  | pure s =>
      exact Interval.absolute_contains (C.toContext.weightedDot_contains hx
        (action_contains (C.toContext.frame_contains s) hy))
  | carried pre tag n hn bs post => exact C.pathAbsolute_contains pre post n (bs.map TaggedBlock.run) hx hy

theorem cyclePure_contains (bs : List (TaggedBlock B)) :
    Contains (C.cyclePure bs) (RationalRuns.cyclePure bs) :=
  scalarProduct_contains bs (fun b=>C.toContext.block b.run 0 0)
    (fun b=>RationalRuns.block b.run 0 0) (fun b=>C.toContext.block_contains b.run 0 0)

theorem isolatedPure_contains : Contains C.isolatedPure RationalRuns.isolatedPure :=
  mul_contains (C.toContext.start_contains none 0 freeBoxes_contains 0)
    (C.toContext.finish_contains none loopBoxes_contains 0)

theorem isolatedAbsolute_contains : Contains C.isolatedAbsolute RationalRuns.isolatedAbsolute :=
  C.pathAbsolute_contains none none 0 [] freeBoxes_contains loopBoxes_contains

def pure (q : ModeProgram B) (x y : Vector 4) : Box :=
  match q with
  | .path p => C.pathPure p x y
  | .cycle _ b bs => C.cyclePure (b::bs)
  | .isolated => C.isolatedPure

def absolute (q : ModeProgram B) (x y : Vector 4) : Box :=
  match q with
  | .path p => C.pathAbs p x y
  | .cycle _ b bs => C.cycleAbsolute ((b::bs).map TaggedBlock.run)
  | .isolated => C.isolatedAbsolute

theorem pure_contains (q : ModeProgram B) {xb yb : Vector 4} {x y : State→ℝ}
    (hx : VContains xb x) (hy : VContains yb y) :
    Contains (C.pure q xb yb) (q.rationalPure x y) := by
  cases q with
  | path q => exact C.pathPure_contains q hx hy
  | cycle k b bs => exact C.cyclePure_contains (b::bs)
  | isolated => exact C.isolatedPure_contains

theorem absolute_contains (q : ModeProgram B) {xb yb : Vector 4} {x y : State→ℝ}
    (hx : VContains xb x) (hy : VContains yb y) :
    Contains (C.absolute q xb yb) (q.rationalAbsolute x y) := by
  cases q with
  | path q => exact C.pathAbs_contains q hx hy
  | cycle k b bs => exact C.cycleAbsolute_contains ((b::bs).map TaggedBlock.run)
  | isolated => exact C.isolatedAbsolute_contains

def mask {m r p : ℕ} (L : FreeLayout m r p) (c : Fin L.count)
    (i : Fin (L.edges c+1)) : Vector 4 :=
  fun v=>if RawGraph.SourceModel.Domain r p 4 (L.vertex c i) (v.val+1) then point 1 else point 0

theorem mask_contains {m r p : ℕ} (L : FreeLayout m r p) (c : Fin L.count)
    (i : Fin (L.edges c+1)) : VContains (mask L c i) (L.mask c i) := by
  intro v
  unfold mask FreeLayout.mask
  split_ifs
  · simpa using point_contains 1
  · simpa using point_contains 0

def pivot : Box := fastPower (C.weights 0) 8

theorem pivot_contains : Contains C.pivot (radius^8) := by
  have h:=C.weights_contains 0
  have hz : Contains (C.weights 0) radius := by simpa only [Fin.val_zero,zero_add,pow_one] using h
  exact fastPower_contains hz 8

def programPure {m r p : ℕ} (L : FreeLayout m r p) (program : Fin L.count→ModeProgram B) : Box :=
  mul C.pivot (prodBoxes (fun c=>C.pure (program c) (mask L c 0) (mask L c (Fin.last _))))

def programAbsolute {m r p : ℕ} (L : FreeLayout m r p) (program : Fin L.count→ModeProgram B) : Box :=
  mul C.pivot (prodBoxes (fun c=>C.absolute (program c) (mask L c 0) (mask L c (Fin.last _))))

def programMixed {m r p : ℕ} (L : FreeLayout m r p) (program : Fin L.count→ModeProgram B) : Box :=
  sub (C.programAbsolute L program) (C.programPure L program)

section Source
variable {r N d : ℕ} {hN : d<N} (L : FreeLayout (r+N) r (r+d))
variable (program : Fin L.count→ModeProgram (Option (CarryRepresentative N d hN)))

theorem programPure_contains : Contains (C.programPure L program) (ExecutableModes.programPure L program) := by
  rw [ExecutableModes.programPure_eq_rational]
  exact mul_contains C.pivot_contains (prodBoxes_contains (fun c=>C.pure_contains (program c)
    (mask_contains L c 0) (mask_contains L c (Fin.last _))))

theorem programAbsolute_contains : Contains (C.programAbsolute L program) (ExecutableModes.programAbsolute L program) := by
  rw [ExecutableModes.programAbsolute_eq_rational]
  exact mul_contains C.pivot_contains (prodBoxes_contains (fun c=>C.absolute_contains (program c)
    (mask_contains L c 0) (mask_contains L c (Fin.last _))))

theorem programMixed_contains : Contains (C.programMixed L program) (ExecutableModes.programMixed L program) :=
  sub_contains (C.programAbsolute_contains L program) (C.programPure_contains L program)

variable (hr : 0<r) (hd : 0<d) (hfar : r+2*d<N) (hL : L.Valid)
variable (hcheck : ∀c,(program c).check hd hN L c=true)
include hr hd hfar hL hcheck

theorem sourcePure_contains : Contains (C.programPure L program) (sourcePure r N d hN) := by
  rw [sourcePure_eq_program hr hd hN hfar L hL program hcheck]
  exact C.programPure_contains L program

theorem sourceMixed_upper {n q : ℤ} (hq : 0<q)
    (hi : (C.programMixed L program).hi*q≤n*unit) : sourceMixed r N d hN≤(n:ℝ)/(q:ℝ) :=
  (sourceMixed_le_program hr hd hN hfar L hL program hcheck).trans
    (upper_of_contains (C.programMixed_contains L program) hq hi)

end Source
end CachedContext
end SubmittedGenus.CapFourMass.Interval.RationalTables
