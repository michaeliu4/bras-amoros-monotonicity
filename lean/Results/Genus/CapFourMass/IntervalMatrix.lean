import Results.Genus.CapFourMass.IntervalClosed
import Results.Genus.RawGraph.PackedAcceptance.TransferTable
import Mathlib.LinearAlgebra.Matrix.Trace

/-! Arithmetic syntax for finite matrix and physical transfer calculations.
This is an arithmetic adapter; source geometry remains in certified Layouts. -/
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFourMass.Interval
namespace Expr

def sumList : List Expr → Expr
  | [] => 0
  | a::as => a+sumList as

theorem sumList_real (xs : ℕ → ℝ) (as : List Expr) :
    (sumList as).real xs=(as.map (fun e => e.real xs)).sum := by
  induction as with
  | nil => simp [sumList]
  | cons a as ih => simp [sumList,ih]

def sumFin {n : ℕ} (f : Fin n → Expr) : Expr := sumList (List.ofFn f)

@[simp] theorem sumFin_real (xs : ℕ → ℝ) {n : ℕ} (f : Fin n → Expr) :
    (sumFin f).real xs=∑i,(f i).real xs := by
  rw [sumFin,sumList_real,List.map_ofFn,List.sum_ofFn]
  rfl

def prodList : List Expr → Expr
  | [] => 1
  | a::as => a*prodList as

theorem prodList_real (xs : ℕ → ℝ) (as : List Expr) :
    (prodList as).real xs=(as.map (fun e => e.real xs)).prod := by
  induction as with
  | nil => simp [prodList]
  | cons a as ih => simp [prodList,ih]

def prodFin {n : ℕ} (f : Fin n → Expr) : Expr := prodList (List.ofFn f)

@[simp] theorem prodFin_real (xs : ℕ → ℝ) {n : ℕ} (f : Fin n → Expr) :
    (prodFin f).real xs=∏i,(f i).real xs := by
  rw [prodFin,prodList_real,List.map_ofFn,List.prod_ofFn]
  rfl

abbrev EMatrix (n : ℕ) := Fin n → Fin n → Expr
abbrev EVector (n : ℕ) := Fin n → Expr

noncomputable def matrixReal (xs : ℕ → ℝ) {n : ℕ} (A : EMatrix n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (A i j).real xs

def matrixMul {n : ℕ} (A B : EMatrix n) : EMatrix n :=
  fun i j => sumFin (fun k => A i k*B k j)
def matrixVec {n : ℕ} (A : EMatrix n) (v : EVector n) : EVector n :=
  fun i => sumFin (fun j => A i j*v j)
def vecMatrix {n : ℕ} (v : EVector n) (A : EMatrix n) : EVector n :=
  fun j => sumFin (fun i => v i*A i j)
def dot {n : ℕ} (v w : EVector n) : Expr := sumFin (fun i => v i*w i)
def trace {n : ℕ} (A : EMatrix n) : Expr := sumFin (fun i => A i i)
def matrixId (n : ℕ) : EMatrix n := fun i j => if i=j then 1 else 0

theorem matrixMul_real (xs : ℕ → ℝ) {n : ℕ} (A B : EMatrix n) :
    matrixReal xs (matrixMul A B)=
      matrixReal xs A*matrixReal xs B := by
  funext i j
  simp [matrixMul,matrixReal,Matrix.mul_apply]
theorem matrixVec_real (xs : ℕ → ℝ) {n : ℕ} (A : EMatrix n) (v : EVector n) :
    (fun i => (matrixVec A v i).real xs)=
      matrixReal xs A*ᵥ(fun i => (v i).real xs) := by
  funext i
  simp [matrixVec,matrixReal,Matrix.mulVec,dotProduct]
theorem vecMatrix_real (xs : ℕ → ℝ) {n : ℕ} (v : EVector n) (A : EMatrix n) :
    (fun j => (vecMatrix v A j).real xs)=
      (fun i => (v i).real xs)ᵥ*matrixReal xs A := by
  funext j
  simp [vecMatrix,matrixReal,Matrix.vecMul,dotProduct]
theorem dot_real (xs : ℕ → ℝ) {n : ℕ} (v w : EVector n) :
    (dot v w).real xs=(fun i => (v i).real xs) ⬝ᵥ (fun i => (w i).real xs) := by
  simp [dot,dotProduct]
theorem trace_real (xs : ℕ → ℝ) {n : ℕ} (A : EMatrix n) :
    (trace A).real xs=Matrix.trace (matrixReal xs A) := by
  simp [trace,matrixReal,Matrix.trace]
theorem matrixId_real (xs : ℕ → ℝ) (n : ℕ) :
    matrixReal xs (matrixId n)=(1:Matrix (Fin n) (Fin n) ℝ) := by
  funext i j
  by_cases h:i=j <;> simp [matrixReal,matrixId,h,Matrix.one_apply]

def matrixPower {n : ℕ} (A : EMatrix n) : ℕ → EMatrix n
  | 0 => matrixId n
  | k+1 => matrixMul (matrixPower A k) A

theorem matrixPower_real (xs : ℕ → ℝ) {n : ℕ} (A : EMatrix n) (k : ℕ) :
    matrixReal xs (matrixPower A k)=matrixReal xs A^k := by
  induction k with
  | zero => simpa only [matrixPower,pow_zero] using matrixId_real xs n
  | succ k ih => rw [matrixPower,matrixMul_real,ih,pow_succ]

/-- Small reference transfer. Larger cases use locally checked tables to avoid unfolding this tree. -/
def run {a : ℕ} : ℕ → (ℕ → Fin a → Expr) → (ℕ → Fin a → Fin a → Expr) →
    (Fin a → Expr) → Fin a → Expr
  | 0,w,_,finish,first => w 0 first*finish first
  | n+1,w,edge,finish,first => w 0 first*sumFin (fun next =>
      edge 0 first next*run n (RawGraph.Transfer.shift w) (RawGraph.Transfer.shift edge) finish next)

theorem run_real (xs : ℕ → ℝ) {a : ℕ} (n : ℕ) (w : ℕ → Fin a → Expr)
    (edge : ℕ → Fin a → Fin a → Expr) (finish : Fin a → Expr) (first : Fin a) :
    (run n w edge finish first).real xs=RawGraph.Transfer.run n
      (fun j i => (w j i).real xs) (fun j i k => (edge j i k).real xs)
      (fun i => (finish i).real xs) first := by
  induction n generalizing w edge first with
  | zero => simp [run,RawGraph.Transfer.run]
  | succ n ih =>
    simp only [run,real_mul,sumFin_real,ih,RawGraph.Transfer.run,RawGraph.Transfer.shift]
    rfl

def pathRun {a : ℕ} (n : ℕ) (w : ℕ → Fin a → Expr)
    (edge : ℕ → Fin a → Fin a → Expr) : Expr :=
  sumFin (fun first => run n w edge (fun _ => 1) first)
def cycleRun {a : ℕ} (n : ℕ) (w : ℕ → Fin a → Expr)
    (edge : ℕ → Fin a → Fin a → Expr) (close : Fin a → Fin a → Expr) : Expr :=
  sumFin (fun first => run n w edge (fun last => close last first) first)

theorem pathRun_real (xs : ℕ → ℝ) {a : ℕ} (n : ℕ) (w : ℕ → Fin a → Expr)
    (edge : ℕ → Fin a → Fin a → Expr) :
    (pathRun n w edge).real xs=RawGraph.Transfer.pathRun n
      (fun j i => (w j i).real xs) (fun j i k => (edge j i k).real xs) := by
  simp [pathRun,RawGraph.Transfer.pathRun,run_real]
theorem cycleRun_real (xs : ℕ → ℝ) {a : ℕ} (n : ℕ) (w : ℕ → Fin a → Expr)
    (edge : ℕ → Fin a → Fin a → Expr) (close : Fin a → Fin a → Expr) :
    (cycleRun n w edge close).real xs=RawGraph.Transfer.cycleRun n
      (fun j i => (w j i).real xs) (fun j i k => (edge j i k).real xs)
      (fun i j => (close i j).real xs) := by
  simp [cycleRun,RawGraph.Transfer.cycleRun,run_real]

end Expr
end SubmittedGenus.CapFourMass.Interval
