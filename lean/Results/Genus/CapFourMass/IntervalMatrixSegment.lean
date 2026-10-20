import Results.Genus.CapFourMass.IntervalNonnegativeMatrix

/-! A local cached-power segment starts from an already enclosed power. This
permits bounded independently accepted chunks without one giant kernel proof. -/
open scoped Matrix
namespace SubmittedGenus.CapFourMass.Interval.MatrixTables

def SegmentValid {n : ℕ} (N : ℕ) (first A : Boxes n) (ts : Fin (N+1)→Boxes n) : Prop :=
  Nonnegative A ∧ (∀k,Nonnegative (ts k)) ∧
  (∀i j,ts 0 i j=first i j) ∧
  ∀k : Fin N,∀i j,ts k.succ i j=nonnegativeProduct (ts k.castSucc) A i j

instance {n : ℕ} (N : ℕ) (first A : Boxes n) (ts : Fin (N+1)→Boxes n) :
    Decidable (SegmentValid N first A ts) := by unfold SegmentValid; infer_instance

theorem segment_contains {n N offset : ℕ} {ab first : Boxes n}
    {A : Matrix (Fin n) (Fin n) ℝ} (ha : Encloses ab A) (hf : Encloses first (A^offset))
    (ts : Fin (N+1)→Boxes n) (ht : SegmentValid N first ab ts) (k : Fin (N+1)) :
    Encloses (ts k) (A^(offset+k.val)) := by
  have hs : ∀j : ℕ,∀hj : j≤N,Encloses (ts ⟨j,by omega⟩) (A^(offset+j)) := by
    intro j
    induction j with
    | zero =>
      intro hj i k
      rw [show (⟨0,by omega⟩:Fin (N+1))=0 from rfl,ht.2.2.1,Nat.add_zero]
      exact hf i k
    | succ j ih =>
      intro hj i k
      have hlt : j<N := by omega
      have he:=ht.2.2.2 ⟨j,hlt⟩ i k
      change ts ⟨j+1,by omega⟩ i k=nonnegativeProduct (ts ⟨j,by omega⟩) ab i k at he
      rw [he,show offset+(j+1)=(offset+j)+1 by omega,pow_succ]
      exact nonnegativeProduct_contains (ih (by omega)) ha (ht.2.1 _) ht.1 i k
  exact hs k.val (by omega)

end SubmittedGenus.CapFourMass.Interval.MatrixTables
