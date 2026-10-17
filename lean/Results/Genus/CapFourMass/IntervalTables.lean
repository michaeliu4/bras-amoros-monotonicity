import Results.Genus.CapFourMass.IntervalCompute
import Results.Genus.RawGraph.PackedAcceptance.TransferTable

/-! Locally checked interval transfer tables avoid recursive source expansion.
The arithmetic checks are on supplied integer endpoint boxes; soundness refers
to the exact physical transfer and retains signed values and cycle endpoints. -/
open scoped BigOperators
namespace SubmittedGenus.CapFourMass.Interval

def sumBoxes : {n : ℕ} → (Fin n → Box) → Box
  | 0,_ => point 0
  | _+1,f => add (f 0) (sumBoxes (fun i => f i.succ))

theorem sumBoxes_contains {n : ℕ} {bs : Fin n → Box} {xs : Fin n → ℝ}
    (h : ∀i,Contains (bs i) (xs i)) : Contains (sumBoxes bs) (∑i,xs i) := by
  induction n with
  | zero => simpa [sumBoxes] using point_contains 0
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    exact add_contains (h 0) (ih (fun i => h i.succ))

def prodBoxes : {n : ℕ} → (Fin n → Box) → Box
  | 0,_ => point 1
  | _+1,f => mul (f 0) (prodBoxes (fun i => f i.succ))

theorem prodBoxes_contains {n : ℕ} {bs : Fin n → Box} {xs : Fin n → ℝ}
    (h : ∀i,Contains (bs i) (xs i)) : Contains (prodBoxes bs) (∏i,xs i) := by
  induction n with
  | zero => simpa [prodBoxes] using point_contains 1
  | succ n ih =>
    rw [Fin.prod_univ_succ]
    exact mul_contains (h 0) (ih (fun i => h i.succ))

/-- Every source row is verified from the supplied next row, never recomputed recursively. -/
def TableValid {a : ℕ} (n : ℕ) (w : ℕ → Fin a → Box)
    (edge : ℕ → Fin a → Fin a → Box) (finish : Fin a → Box)
    (table : Fin (n+1) → Fin a → Box) : Prop :=
  (∀i,table (Fin.last n) i=mul (w n i) (finish i)) ∧
  ∀j : Fin n,∀i,table j.castSucc i=
    mul (w j.val i) (sumBoxes (fun k => mul (edge j.val i k) (table j.succ k)))

instance {a : ℕ} (n : ℕ) (w : ℕ → Fin a → Box)
    (edge : ℕ → Fin a → Fin a → Box) (finish : Fin a → Box)
    (table : Fin (n+1) → Fin a → Box) : Decidable (TableValid n w edge finish table) := by
  unfold TableValid
  infer_instance

theorem table_contains {a : ℕ} (n : ℕ)
    (wb : ℕ → Fin a → Box) (eb : ℕ → Fin a → Fin a → Box) (fb : Fin a → Box)
    (w : ℕ → Fin a → ℝ) (e : ℕ → Fin a → Fin a → ℝ) (f : Fin a → ℝ)
    (hw : ∀j i,Contains (wb j i) (w j i)) (he : ∀j i k,Contains (eb j i k) (e j i k))
    (hf : ∀i,Contains (fb i) (f i)) (table : Fin (n+1) → Fin a → Box)
    (ht : TableValid n wb eb fb table) (first : Fin a) :
    Contains (table 0 first) (RawGraph.Transfer.run n w e f first) := by
  induction n generalizing wb eb w e first with
  | zero =>
    have hs:=ht.1 first
    change table 0 first=mul (wb 0 first) (fb first) at hs
    rw [hs]
    exact mul_contains (hw 0 first) (hf first)
  | succ n ih =>
    let tail : Fin (n+1) → Fin a → Box := fun j => table j.succ
    have hv : TableValid n (RawGraph.Transfer.shift wb) (RawGraph.Transfer.shift eb) fb tail := by
      exact ⟨ht.1,fun j i => ht.2 j.succ i⟩
    have hs := ht.2 (0:Fin (n+1)) first
    change table 0 first=mul (wb 0 first)
      (sumBoxes (fun k => mul (eb 0 first k) (tail 0 k))) at hs
    rw [hs,RawGraph.Transfer.run]
    apply mul_contains (hw 0 first)
    apply sumBoxes_contains
    intro k
    apply mul_contains (he 0 first k)
    exact ih (RawGraph.Transfer.shift wb) (RawGraph.Transfer.shift eb)
      (RawGraph.Transfer.shift w) (RawGraph.Transfer.shift e)
      (fun j i => hw (j+1) i) (fun j i k => he (j+1) i k) tail hv k

theorem path_table_contains {a : ℕ} (n : ℕ)
    (wb : ℕ → Fin a → Box) (eb : ℕ → Fin a → Fin a → Box)
    (w : ℕ → Fin a → ℝ) (e : ℕ → Fin a → Fin a → ℝ)
    (hw : ∀j i,Contains (wb j i) (w j i)) (he : ∀j i k,Contains (eb j i k) (e j i k))
    (table : Fin (n+1) → Fin a → Box) (ht : TableValid n wb eb (fun _ => point 1) table) :
    Contains (sumBoxes (table 0)) (RawGraph.Transfer.pathRun n w e) := by
  apply sumBoxes_contains
  intro first
  exact table_contains n wb eb (fun _ => point 1) w e (fun _ => 1) hw he
    (fun _ => by simpa using point_contains 1) table ht first

theorem cycle_table_contains {a : ℕ} (n : ℕ)
    (wb : ℕ → Fin a → Box) (eb : ℕ → Fin a → Fin a → Box) (cb : Fin a → Fin a → Box)
    (w : ℕ → Fin a → ℝ) (e : ℕ → Fin a → Fin a → ℝ) (c : Fin a → Fin a → ℝ)
    (hw : ∀j i,Contains (wb j i) (w j i)) (he : ∀j i k,Contains (eb j i k) (e j i k))
    (hc : ∀i k,Contains (cb i k) (c i k)) (table : Fin a → Fin (n+1) → Fin a → Box)
    (ht : ∀first,TableValid n wb eb (fun last => cb last first) (table first)) :
    Contains (sumBoxes (fun first => table first 0 first)) (RawGraph.Transfer.cycleRun n w e c) := by
  apply sumBoxes_contains
  intro first
  exact table_contains n wb eb (fun last => cb last first) w e (fun last => c last first)
    hw he (fun last => hc last first) (table first) (ht first) first

end SubmittedGenus.CapFourMass.Interval
