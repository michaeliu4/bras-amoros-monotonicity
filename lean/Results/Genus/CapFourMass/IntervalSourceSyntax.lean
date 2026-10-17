import Results.Genus.CapFourMass.IntervalCoreModeSyntax
import Results.Genus.CapFourMass.IntervalRefinedInputs
import Results.Genus.CapFourMass.IntervalInputCheck
import Results.Genus.CapFourMass.SourceMultiplicitySums

/-! Direct source-exact pure and mixed syntax for bounded validation fixtures.
The absolute value is applied to the entire core coefficient for each complete
mode assignment. This pilot deliberately does not use a graph run shortcut. -/
open scoped BigOperators
namespace SubmittedGenus.CapFourMass.Interval
namespace SourceSyntax
open Expr FixedPivot

def inputs (i : ℕ) : Box := if i=0 then lambdaRefined else if i=1 then feedbackRefined else point 0
noncomputable def values (i : ℕ) : ℝ := if i=0 then lam else if i=1 then feedbackT else 0

theorem inputs_contain (i : ℕ) : Contains (inputs i) (values i) := by
  unfold inputs values
  split_ifs
  · exact lambdaRefined_contains
  · exact feedbackRefined_contains
  · simpa using point_contains 0

def z : Expr := Expr.rational 1247 2000
def l : Expr := .input 0
def m : Expr := z^2+z^3-l
def t : Expr := .input 1
def w : Expr := Expr.rational 70651823329321825 72057594037927936

@[simp] theorem z_real : z.real values=radius := by norm_num [z,Expr.rational,Expr.real,radius]
@[simp] theorem l_real : l.real values=lam := by simp [l,Expr.real,values]
@[simp] theorem m_real : m.real values=mu := by simp [m,mu,carryB]
@[simp] theorem t_real : t.real values=feedbackT := by simp [t,Expr.real,values]
@[simp] theorem w_real : w.real values=normalizer := by norm_num [w,Expr.rational,Expr.real,normalizer]

def coefficient {r N d k : ℕ} (hN : d<N) (reps : Fin k ≃ CarryRepresentative N d hN)
    (choice : CarryRepresentative N d hN→Bool) : Expr :=
  CoreModeSyntax.coefficient (r:=r) hN reps z l m (1/l) (1/m) (1/(l-m)) choice

theorem coefficient_real {r N d k : ℕ} (hN : d<N)
    (reps : Fin k ≃ CarryRepresentative N d hN) (choice : CarryRepresentative N d hN→Bool) :
    (coefficient (r:=r) hN reps choice).real values=sourceCoefficient r N d hN choice := by
  rw [coefficient,CoreModeSyntax.coefficient_real]
  simp only [z_real,l_real,m_real,Expr.real_div,Expr.real_one,Expr.real_sub,one_div]
  rfl

def pure {r N d k : ℕ} (hN : d<N) (reps : Fin k ≃ CarryRepresentative N d hN) : Expr :=
  coefficient (r:=r) hN reps (fun _=>false)

theorem pure_real {r N d k : ℕ} (hN : d<N) (reps : Fin k ≃ CarryRepresentative N d hN) :
    (pure (r:=r) hN reps).real values=sourcePure r N d hN := by
  rw [pure,coefficient_real,sourcePure_eq_coefficient]

def bitEquiv : Fin 2 ≃ Bool where
  toFun i := decide (i.val=1)
  invFun b := if b then 1 else 0
  left_inv := by decide
  right_inv := by decide

def choiceEnum {N d k : ℕ} {hN : d<N} (reps : Fin k ≃ CarryRepresentative N d hN) :
    Fin (2^k) ≃ (CarryRepresentative N d hN→Bool) :=
  finFunctionFinEquiv.symm.trans (Equiv.arrowCongr reps bitEquiv)

def mixed {r N d k : ℕ} (hN : d<N) (reps : Fin k ≃ CarryRepresentative N d hN) : Expr :=
  Expr.sumFin (fun i : Fin (2^k)=>
    if choiceEnum reps i=(fun _=>false) then 0 else .abs (coefficient (r:=r) hN reps (choiceEnum reps i)))

theorem mixed_real {r N d k : ℕ} (hN : d<N) (reps : Fin k ≃ CarryRepresentative N d hN) :
    (mixed (r:=r) hN reps).real values=sourceMixed r N d hN := by
  rw [mixed,Expr.sumFin_real,sourceMixed,←(choiceEnum reps).sum_comp]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs
  · exact Expr.real_zero _
  · change |(coefficient hN reps (choiceEnum reps i)).real values|=|_|
    rw [coefficient_real]

def normalized (r d n : ℕ) (X : Expr) : Expr :=
  (t^(feedbackExponent r (r+d))/w^(2*(r+d)+(longMultiplicity r d n-1)%2))*
    (w^(longMultiplicity r d n-1)*X)

theorem normalized_real (r d n : ℕ) (X : Expr) :
    (normalized r d n X).real values=
      normalizationK (longMultiplicity r d n) r (r+d)*
        normalizedMass (longMultiplicity r d n) (X.real values) := by
  simp [normalized,normalizationK,normalizedMass]

def pureSeries {r d n k : ℕ}
    (reps : Fin k ≃ CarryRepresentative (longTailN r d n) d (by have:=longTailN_large r d n; omega)) : Expr :=
  normalized r d n (pure (r:=r) _ reps)

def mixedSeries {r d n k : ℕ}
    (reps : Fin k ≃ CarryRepresentative (longTailN r d n) d (by have:=longTailN_large r d n; omega)) : Expr :=
  normalized r d n (mixed (r:=r) _ reps)

theorem pureSeries_real {r d n k : ℕ}
    (reps : Fin k ≃ CarryRepresentative (longTailN r d n) d (by have:=longTailN_large r d n; omega)) :
    (pureSeries reps).real values=sourcePureSeries r d n := by
  rw [pureSeries,normalized_real,pure_real]
  rfl

theorem mixedSeries_real {r d n k : ℕ}
    (reps : Fin k ≃ CarryRepresentative (longTailN r d n) d (by have:=longTailN_large r d n; omega)) :
    (mixedSeries reps).real values=sourceMixedSeries r d n := by
  rw [mixedSeries,normalized_real,mixed_real]
  rfl

end SourceSyntax
end SubmittedGenus.CapFourMass.Interval
