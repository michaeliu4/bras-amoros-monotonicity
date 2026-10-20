import Results.Genus.CapFourMass.IntervalMatrix
import Results.Genus.CapFourMass.SourceProgression

/-! A direct rational syntax for small complete source-mode fixtures. The core
sum is completed before any caller takes its absolute value. No component
ordering, square-root approximation, or assumed run identity is needed. -/
open scoped BigOperators
namespace SubmittedGenus.CapFourMass.Interval
namespace CoreModeSyntax
open Expr FixedPivot

def step (z : Expr) (v : Fin 3→Expr) : Fin 3→Expr :=
  ![z^2*v 1+z^3*v 2,z*v 0+z^2*v 1+z^3*v 2,z*v 0+z^2*v 1+z^3*v 2]

def projector (z other ti di : Expr) (v : Fin 3→Expr) (i : Fin 3) : Expr :=
  ti*di*(step z (step z v) i-other*step z v i)

def amplitude (z theta other ti di : Expr) (n : ℕ) (start finish : Fin 3→Expr) : Expr :=
  Expr.sumFin (fun i : Fin 3=>z^(i.val+1)*start i*(theta^n*projector z other ti di finish i))

def canonicalAmplitude {r N d : ℕ} (hN : d<N) (z theta other ti di : Expr)
    (x : Fin (r+d)→Fin 5) (c : CarryRepresentative N d hN) : Expr :=
  amplitude z theta other ti di (carryTailSize N d hN c-1)
    (fun v=>if canonicalStartAllowed x c v then 1 else 0)
    (fun v=>if canonicalFinishAllowed x c v then 1 else 0)

def term {r N d k : ℕ} (hN : d<N) (reps : Fin k ≃ CarryRepresentative N d hN)
    (z lam mu li mi di : Expr) (x : Fin (r+d)→Fin 5)
    (choice : CarryRepresentative N d hN→Bool) : Expr :=
  if StableCoreAllowed r (r+d) x then z^(∑i,(x i).val)*
    Expr.prodFin (fun j=>if choice (reps j) then
      canonicalAmplitude hN z mu lam mi (0-di) x (reps j)
      else canonicalAmplitude hN z lam mu li di x (reps j))
  else 0

def coefficient {r N d k : ℕ} (hN : d<N) (reps : Fin k ≃ CarryRepresentative N d hN)
    (z lam mu li mi di : Expr) (choice : CarryRepresentative N d hN→Bool) : Expr :=
  Expr.sumFin (fun i : Fin (5^(r+d))=>term hN reps z lam mu li mi di
    (finFunctionFinEquiv.symm i) choice)

theorem step_real (xs : ℕ→ℝ) (z : Expr) (v : Fin 3→Expr) (i : Fin 3) :
    (step z v i).real xs=carryStep (z.real xs) (fun j=>(v j).real xs) i := by
  fin_cases i <;> simp [step,carryStep]

theorem projector_real (xs : ℕ→ℝ) (z theta other ti di : Expr)
    (v : Fin 3→Expr) (i : Fin 3) :
    (projector z other ti di v i).real xs=
      carryProjector (z.real xs) (theta.real xs) (other.real xs) (ti.real xs) (di.real xs)
        (fun j=>(v j).real xs) i := by
  simp [projector,carryProjector,step_real]

theorem amplitude_real (xs : ℕ→ℝ) (z theta other ti di : Expr) (n : ℕ)
    (start finish : Fin 3→Expr) :
    (amplitude z theta other ti di n start finish).real xs=
      weightedModeAmplitude (z.real xs) (theta.real xs) (other.real xs) (ti.real xs) (di.real xs)
        n (fun j=>(start j).real xs) (fun j=>(finish j).real xs) := by
  simp only [amplitude,Expr.sumFin_real,Expr.real_mul,Expr.real_pow]
  unfold weightedModeAmplitude carryWeight
  apply Finset.sum_congr rfl
  intro i _
  rw [projector_real xs z theta]

theorem canonicalAmplitude_real (xs : ℕ→ℝ) {r N d : ℕ} (hN : d<N)
    (z theta other ti di : Expr) (x : Fin (r+d)→Fin 5) (c : CarryRepresentative N d hN) :
    (canonicalAmplitude hN z theta other ti di x c).real xs=
      canonicalModeAmplitude hN (z.real xs) (theta.real xs) (other.real xs)
        (ti.real xs) (di.real xs) x c := by
  unfold canonicalAmplitude canonicalModeAmplitude
  rw [amplitude_real]
  congr 1 <;> funext v <;> split_ifs <;> simp

theorem term_real (xs : ℕ→ℝ) {r N d k : ℕ} (hN : d<N)
    (reps : Fin k ≃ CarryRepresentative N d hN) (z lam mu li mi di : Expr)
    (x : Fin (r+d)→Fin 5) (choice : CarryRepresentative N d hN→Bool) :
    (term hN reps z lam mu li mi di x choice).real xs=
      sourceModeCoefficient hN (z.real xs) (lam.real xs) (mu.real xs) (li.real xs)
        (mi.real xs) (di.real xs) (x,choice) := by
  unfold term sourceModeCoefficient stableCoreTerm
  split_ifs with hc
  · simp only [Expr.real_mul,Expr.real_pow,Polynomial.eval₂_pow,Polynomial.eval₂_X,
      Expr.prodFin_real]
    congr 1
    rw [←reps.prod_comp]
    apply Finset.prod_congr rfl
    intro j _
    split_ifs <;> simp [canonicalAmplitude_real]
  · simp

/-- The syntax is the complete source coefficient for each full shared mode assignment. -/
theorem coefficient_real (xs : ℕ→ℝ) {r N d k : ℕ} (hN : d<N)
    (reps : Fin k ≃ CarryRepresentative N d hN) (z lam mu li mi di : Expr)
    (choice : CarryRepresentative N d hN→Bool) :
    (coefficient (r:=r) hN reps z lam mu li mi di choice).real xs=
      ∑x : Fin (r+d)→Fin 5,sourceModeCoefficient hN (z.real xs) (lam.real xs)
        (mu.real xs) (li.real xs) (mi.real xs) (di.real xs) (x,choice) := by
  simp only [coefficient,Expr.sumFin_real,term_real]
  exact (finFunctionFinEquiv : (Fin (r+d)→Fin 5) ≃ Fin (5^(r+d))).symm.sum_comp
    (fun x=>sourceModeCoefficient hN (z.real xs) (lam.real xs) (mu.real xs)
      (li.real xs) (mi.real xs) (di.real xs) (x,choice))

end CoreModeSyntax
end SubmittedGenus.CapFourMass.Interval
