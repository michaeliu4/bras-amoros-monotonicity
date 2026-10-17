import Results.Genus.CapFourMass.IntervalMatrixTables
import Results.Genus.CapFourMass.IntervalPower
import Results.Genus.CapFourMass.RationalRunGauge

/-! Signed Box-level run evaluation. The strong matrices are supplied through
an independently proved cache interface, so evaluation never expands a matrix
power into a duplicated arithmetic expression tree. -/
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFourMass.Interval.RationalTables
open MatrixTables

abbrev Vector (n : ℕ) := Fin n→Box

def VContains {n : ℕ} (a : Vector n) (x : Fin n→ℝ) : Prop := ∀i,Contains (a i) (x i)

def dot {n : ℕ} (x y : Vector n) : Box := sumBoxes (fun i=>mul (x i) (y i))
def vectorAbsolute {n : ℕ} (x : Vector n) : Vector n := fun i=>absolute (x i)
def matrixAbsolute {n : ℕ} (A : Boxes n) : Boxes n := fun i j=>absolute (A i j)

def listProduct {n : ℕ} : List (Boxes n)→Boxes n
  | [] => identity n
  | a::as => product a (listProduct as)

def scalarProduct : List Box→Box
  | [] => point 1
  | a::as => mul a (scalarProduct as)

theorem dot_contains {n : ℕ} {xb yb : Vector n} {x y : Fin n→ℝ}
    (hx : VContains xb x) (hy : VContains yb y) : Contains (dot xb yb) (x ⬝ᵥ y) :=
  sumBoxes_contains (fun i=>mul_contains (hx i) (hy i))

theorem vectorAbsolute_contains {n : ℕ} {xb : Vector n} {x : Fin n→ℝ}
    (hx : VContains xb x) : VContains (vectorAbsolute xb) (fun i=>|x i|) :=
  fun i=>absolute_contains (hx i)

theorem matrixAbsolute_contains {n : ℕ} {ab : Boxes n} {A : Matrix (Fin n) (Fin n) ℝ}
    (ha : Encloses ab A) : Encloses (matrixAbsolute ab) (fun i j=>|A i j|) :=
  fun i j=>absolute_contains (ha i j)

theorem listProduct_contains {n : ℕ} {B : Type*} (bs : List B)
    (ab : B→Boxes n) (A : B→Matrix (Fin n) (Fin n) ℝ)
    (ha : ∀b,Encloses (ab b) (A b)) :
    Encloses (listProduct (bs.map ab)) (bs.map A).prod := by
  induction bs with
  | nil => exact identity_contains n
  | cons b bs ih => exact product_contains (ha b) ih

theorem scalarProduct_contains {B : Type*} (bs : List B) (ab : B→Box) (a : B→ℝ)
    (ha : ∀b,Contains (ab b) (a b)) : Contains (scalarProduct (bs.map ab)) (bs.map a).prod := by
  induction bs with
  | nil => simpa [scalarProduct] using point_contains 1
  | cons b bs ih => exact mul_contains (ha b) ih

/-- All primitive boxes refer to the same original radius and two signed roots.
Norm positivity is checked before selecting the positive-division branch. -/
structure Context where
  weights : Vector 4
  right : Mode→Vector 4
  norm : Mode→Box
  root : Mode→Box
  strong : StrongRun→Boxes 4
  weights_contains : ∀i,Contains (weights i) (radius^(i.val+1))
  right_contains : ∀j,VContains (right j) (RationalRuns.rightVector j)
  norm_contains : ∀j,Contains (norm j) (RationalRuns.norm j)
  norm_positive : ∀j,0<(norm j).lo
  root_contains : ∀j,Contains (root j) (modeRoot j)
  strong_contains : ∀s,Encloses (strong s) (RationalRuns.strong s)

namespace Context
variable (C : Context)

def weightedDot (x y : Vector 4) : Box :=
  sumBoxes (fun i=>mul (mul (C.weights i) (x i)) (y i))

def frame : Option StrongRun→Boxes 4
  | none => identity 4
  | some s => C.strong s

def block (b : CoupledRun) : Boxes 2 := fun i j=>
  mul (divPos (C.weightedDot (C.right i) (action (C.strong b.strong) (C.right j))) (C.norm i))
    (fastPower (C.root j) b.carryLength)

def start (pre : Option StrongRun) (n : ℕ) (x : Vector 4) : Vector 2 := fun j=>
  mul (C.weightedDot x (action (C.frame pre) (C.right j))) (fastPower (C.root j) n)

def finish (post : Option StrongRun) (y : Vector 4) : Vector 2 := fun j=>
  divPos (C.weightedDot (C.right j) (action (C.frame post) y)) (C.norm j)

def pathAbsolute (pre post : Option StrongRun) (n : ℕ) (bs : List CoupledRun)
    (x y : Vector 4) : Box :=
  dot (vectorAbsolute (C.start pre n x))
    (action (listProduct (bs.map (fun b=>matrixAbsolute (C.block b))))
      (vectorAbsolute (C.finish post y)))

def cycleAbsolute (bs : List CoupledRun) : Box :=
  trace (listProduct (bs.map (fun b=>matrixAbsolute (C.block b))))

theorem weightedDot_contains {xb yb : Vector 4} {x y : State→ℝ}
    (hx : VContains xb x) (hy : VContains yb y) :
    Contains (C.weightedDot xb yb) (RationalRuns.weightedDot x y) :=
  sumBoxes_contains (fun i=>mul_contains (mul_contains (C.weights_contains i) (hx i)) (hy i))

theorem frame_contains (s : Option StrongRun) : Encloses (C.frame s) (RationalRuns.frame s) := by
  cases s with
  | none => exact identity_contains 4
  | some s => exact C.strong_contains s

theorem block_contains (b : CoupledRun) : Encloses (C.block b) (RationalRuns.block b) := by
  intro i j
  exact mul_contains
    (divPos_contains (C.weightedDot_contains (C.right_contains i)
      (action_contains (C.strong_contains b.strong) (C.right_contains j)))
      (C.norm_contains i) (C.norm_positive i))
    (fastPower_contains (C.root_contains j) b.carryLength)

theorem start_contains (pre : Option StrongRun) (n : ℕ) {xb : Vector 4} {x : State→ℝ}
    (hx : VContains xb x) : VContains (C.start pre n xb) (RationalRuns.start pre n x) := by
  intro j
  exact mul_contains
    (C.weightedDot_contains hx (action_contains (C.frame_contains pre) (C.right_contains j)))
    (fastPower_contains (C.root_contains j) n)

theorem finish_contains (post : Option StrongRun) {yb : Vector 4} {y : State→ℝ}
    (hy : VContains yb y) : VContains (C.finish post yb) (RationalRuns.finish post y) := by
  intro j
  exact divPos_contains
    (C.weightedDot_contains (C.right_contains j) (action_contains (C.frame_contains post) hy))
    (C.norm_contains j) (C.norm_positive j)

theorem pathAbsolute_contains (pre post : Option StrongRun) (n : ℕ) (bs : List CoupledRun)
    {xb yb : Vector 4} {x y : State→ℝ} (hx : VContains xb x) (hy : VContains yb y) :
    Contains (C.pathAbsolute pre post n bs xb yb) (RationalRuns.pathAbsolute pre post n bs x y) := by
  apply dot_contains (vectorAbsolute_contains (C.start_contains pre n hx))
  apply action_contains _ (vectorAbsolute_contains (C.finish_contains post hy))
  exact listProduct_contains bs (fun b=>matrixAbsolute (C.block b))
    (fun b=>absoluteMatrix (RationalRuns.block b))
    (fun b=>matrixAbsolute_contains (C.block_contains b))

theorem cycleAbsolute_contains (bs : List CoupledRun) :
    Contains (C.cycleAbsolute bs) (RationalRuns.cycleAbsolute bs) :=
  trace_contains (listProduct_contains bs (fun b=>matrixAbsolute (C.block b))
    (fun b=>absoluteMatrix (RationalRuns.block b))
    (fun b=>matrixAbsolute_contains (C.block_contains b)))

end Context
end SubmittedGenus.CapFourMass.Interval.RationalTables
