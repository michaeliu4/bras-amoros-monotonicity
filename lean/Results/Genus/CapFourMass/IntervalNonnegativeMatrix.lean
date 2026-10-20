import Results.Genus.CapFourMass.IntervalNonnegative
import Results.Genus.CapFourMass.IntervalMatrixTables

open scoped BigOperators Matrix
namespace SubmittedGenus.CapFourMass.Interval.MatrixTables

def Nonnegative {n : ℕ} (A : Boxes n) : Prop := ∀i j,0≤(A i j).lo
instance {n : ℕ} (A : Boxes n) : Decidable (Nonnegative A) := by unfold Nonnegative; infer_instance

def nonnegativeProduct {n : ℕ} (A B : Boxes n) : Boxes n :=
  fun i j=>sumBoxes (fun k=>nonnegativeMul (A i k) (B k j))

theorem nonnegativeProduct_contains {n : ℕ} {ab bb : Boxes n}
    {A B : Matrix (Fin n) (Fin n) ℝ} (ha : Encloses ab A) (hb : Encloses bb B)
    (ha0 : Nonnegative ab) (hb0 : Nonnegative bb) : Encloses (nonnegativeProduct ab bb) (A*B) := by
  intro i j
  exact sumBoxes_contains (fun k=>nonnegativeMul_contains (ha i k) (hb k j) (ha0 i k) (hb0 k j))

/-- Every nonnegativity side condition is checked, including the supplied
base matrix and every cached entry. Signed inputs cannot use this branch. -/
def NonnegativePowerValid {n : ℕ} (N : ℕ) (A : Boxes n) (ts : Fin (N+1)→Boxes n) : Prop :=
  Nonnegative A ∧ (∀k,Nonnegative (ts k)) ∧
  (∀i j,ts 0 i j=identity n i j) ∧
  ∀k : Fin N,∀i j,ts k.succ i j=nonnegativeProduct (ts k.castSucc) A i j

instance {n : ℕ} (N : ℕ) (A : Boxes n) (ts : Fin (N+1)→Boxes n) :
    Decidable (NonnegativePowerValid N A ts) := by unfold NonnegativePowerValid; infer_instance

theorem nonnegative_powers_contain {n N : ℕ} {ab : Boxes n}
    {A : Matrix (Fin n) (Fin n) ℝ} (ha : Encloses ab A) (ts : Fin (N+1)→Boxes n)
    (ht : NonnegativePowerValid N ab ts) (k : Fin (N+1)) : Encloses (ts k) (A^k.val) := by
  have hs : ∀j : ℕ,∀hj : j≤N,Encloses (ts ⟨j,by omega⟩) (A^j) := by
    intro j
    induction j with
    | zero =>
      intro hj i k
      rw [show (⟨0,by omega⟩:Fin (N+1))=0 from rfl,ht.2.2.1,pow_zero]
      exact identity_contains n i k
    | succ j ih =>
      intro hj i k
      have hlt : j<N := by omega
      have he:=ht.2.2.2 ⟨j,hlt⟩ i k
      change ts ⟨j+1,by omega⟩ i k=nonnegativeProduct (ts ⟨j,by omega⟩) ab i k at he
      rw [he,pow_succ]
      exact nonnegativeProduct_contains (ih (by omega)) ha (ht.2.1 _) ht.1 i k
  exact hs k.val (by omega)

end SubmittedGenus.CapFourMass.Interval.MatrixTables
