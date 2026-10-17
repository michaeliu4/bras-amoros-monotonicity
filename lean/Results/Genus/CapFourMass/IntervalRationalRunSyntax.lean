import Results.Genus.CapFourMass.IntervalMatrixSyntax
import Results.Genus.CapFourMass.IntervalSourceSyntax
import Results.Genus.CapFourMass.RationalRunGauge

/-! Rational expression syntax for the exact positive-gauge run evaluator.
Every strong-block contraction is formed before its absolute value. -/
open scoped Matrix BigOperators
namespace SubmittedGenus.CapFourMass.Interval.RationalRunSyntax
open Expr
open SourceSyntax (z l m values)

def rightVector (j : Mode) : EVector 4 :=
  if j=0 then ![(z^2+z^3)/l,1,1,0] else ![l/z,0-1,0-1,0]

def norm (j : Mode) : Expr := sumFin (fun i : State => z^(i.val+1)*(rightVector j i)^2)
def weightedDot (x y : EVector 4) : Expr := sumFin (fun i => z^(i.val+1)*x i*y i)
def root (j : Mode) : Expr := if j=0 then l else m

def transfer (threshold cap : ℕ) : EMatrix 4 :=
  fun i j => if gate threshold cap i j then z^(j.val+1) else 0

def strong : StrongRun→EMatrix 4
  | .full n _ => matrixPower (transfer 4 4) n
  | .restricted => transfer 4 3

def frame : Option StrongRun→EMatrix 4
  | none => matrixId 4
  | some s => strong s

def block (b : CoupledRun) : EMatrix 2 := fun i j =>
  weightedDot (rightVector i) (matrixVec (strong b.strong) (rightVector j))/norm i *
    root j^b.carryLength

def start (pre : Option StrongRun) (n : ℕ) (x : EVector 4) : EVector 2 :=
  fun j => weightedDot x (matrixVec (frame pre) (rightVector j))*root j^n

def finish (post : Option StrongRun) (y : EVector 4) : EVector 2 :=
  fun j => weightedDot (rightVector j) (matrixVec (frame post) y)/norm j

def pathAbsolute (pre post : Option StrongRun) (n : ℕ) (bs : List CoupledRun)
    (x y : EVector 4) : Expr :=
  dot (vectorAbsolute (start pre n x))
    (matrixVec (matrixProduct (bs.map (fun b => matrixAbsolute (block b))))
      (vectorAbsolute (finish post y)))

def cycleAbsolute (bs : List CoupledRun) : Expr :=
  trace (matrixProduct (bs.map (fun b => matrixAbsolute (block b))))

@[simp] theorem rightVector_real (j : Mode) :
    vectorReal values (rightVector j)=RationalRuns.rightVector j := by
  ext i
  fin_cases j <;> fin_cases i <;>
    simp [rightVector,vectorReal,RationalRuns.rightVector,carryB]

@[simp] theorem norm_real (j : Mode) : (norm j).real values=RationalRuns.norm j := by
  simp only [norm,sumFin_real,real_mul,real_pow,SourceSyntax.z_real,RationalRuns.norm]
  exact Finset.sum_congr rfl (fun i _ => by rw [show (rightVector j i).real values=RationalRuns.rightVector j i from congrFun (rightVector_real j) i])

@[simp] theorem weightedDot_real (x y : EVector 4) :
    (weightedDot x y).real values=RationalRuns.weightedDot (vectorReal values x) (vectorReal values y) := by
  simp [weightedDot,RationalRuns.weightedDot,vectorReal]

@[simp] theorem root_real (j : Mode) : (root j).real values=modeRoot j := by
  fin_cases j <;> simp [root,modeRoot]

@[simp] theorem transfer_real (threshold cap : ℕ) :
    matrixReal values (transfer threshold cap)=rationalTransfer threshold cap := by
  ext i j
  simp only [transfer,matrixReal,rationalTransfer]
  split_ifs <;> simp

@[simp] theorem strong_real (s : StrongRun) :
    matrixReal values (strong s)=RationalRuns.strong s := by
  cases s with
  | full n hn => simp only [strong,matrixPower_real,transfer_real,RationalRuns.strong]
  | restricted => exact transfer_real 4 3

@[simp] theorem frame_real (s : Option StrongRun) :
    matrixReal values (frame s)=RationalRuns.frame s := by
  cases s with
  | none => exact matrixId_real values 4
  | some s => exact strong_real s

@[simp] theorem matrixVec_vectorReal {k : ℕ} (A : EMatrix k) (x : EVector k) :
    vectorReal values (matrixVec A x)=matrixReal values A*ᵥvectorReal values x :=
  matrixVec_real values A x

@[simp] theorem block_real (b : CoupledRun) :
    matrixReal values (block b)=RationalRuns.block b := by
  ext i j
  change (block b i j).real values=RationalRuns.block b i j
  simp only [block,real_mul,real_div,real_pow,weightedDot_real,norm_real,root_real,
    matrixVec_vectorReal,strong_real,rightVector_real,RationalRuns.block]

@[simp] theorem start_real (pre : Option StrongRun) (n : ℕ) (x : EVector 4) :
    vectorReal values (start pre n x)=RationalRuns.start pre n (vectorReal values x) := by
  ext j
  change (start pre n x j).real values=RationalRuns.start pre n (vectorReal values x) j
  simp only [start,real_mul,weightedDot_real,real_pow,root_real,
    matrixVec_vectorReal,frame_real,rightVector_real,RationalRuns.start]

@[simp] theorem finish_real (post : Option StrongRun) (y : EVector 4) :
    vectorReal values (finish post y)=RationalRuns.finish post (vectorReal values y) := by
  ext j
  change (finish post y j).real values=RationalRuns.finish post (vectorReal values y) j
  simp only [finish,real_div,weightedDot_real,norm_real,rightVector_real,
    matrixVec_vectorReal,frame_real,RationalRuns.finish]

@[simp] theorem pathAbsolute_real (pre post : Option StrongRun) (n : ℕ)
    (bs : List CoupledRun) (x y : EVector 4) :
    (pathAbsolute pre post n bs x y).real values=
      RationalRuns.pathAbsolute pre post n bs (vectorReal values x) (vectorReal values y) := by
  rw [pathAbsolute,dot_real,matrixVec_real,matrixProduct_real]
  change vectorReal values (vectorAbsolute (start pre n x)) ⬝ᵥ
    (((bs.map (fun b => matrixAbsolute (block b))).map (matrixReal values)).prod*ᵥ
      vectorReal values (vectorAbsolute (finish post y)))=_
  simp only [vectorAbsolute_real,start_real,finish_real,List.map_map,Function.comp_def,
    matrixAbsolute_real,block_real,RationalRuns.pathAbsolute]
  rfl

@[simp] theorem cycleAbsolute_real (bs : List CoupledRun) :
    (cycleAbsolute bs).real values=RationalRuns.cycleAbsolute bs := by
  rw [cycleAbsolute,trace_real,matrixProduct_real]
  simp only [List.map_map,Function.comp_def,matrixAbsolute_real,block_real,
    RationalRuns.cycleAbsolute]
  rfl

end SubmittedGenus.CapFourMass.Interval.RationalRunSyntax
