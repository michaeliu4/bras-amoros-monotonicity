import Results.Genus.RawGraph.PackedAcceptance.ReflectionDelete

namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionPath
open LayoutCompiler SourceModel ReflectionConsecutive ReflectionDelete

abbrev singletonLabel (n : ℕ) : (Σ_ : Fin 1,Fin (n+1)) ≃ Fin (n+1) where
  toFun := fun v=>v.2
  invFun := fun j=>⟨0,j⟩
  left_inv := by rintro ⟨c,j⟩; fin_cases c; rfl
  right_inv := by intro j; rfl

/-- All physical vertices in one path, with the zero residue removed.
Pivots remain present with their exact source unary and zero-edge factors. -/
abbrev layout {n : ℕ} (e : Fin (n+2)≃Fin (n+2)) (cut : Fin (n+1))
    (hz : e cut.castSucc=0) : Layout (n+2) where
  count := 1
  edges := fun _=>n
  cycle := fun _=>false
  label := (singletonLabel n).trans (removeZero e cut hz)

lemma physical_cast {n : ℕ} (e : Fin (n+2)≃Fin (n+2)) (cut : Fin (n+1))
    (hz : e cut.castSucc=0) (j : Fin (n+1)) :
    ((physical ((layout e cut hz).label ⟨0,j⟩):ℕ):ZMod (n+2))=
      asResidue (n+1) (e (cut.castSucc.succAbove j)) := by
  have he := removeZero_succ e cut hz j
  have hc := congrArg (asResidue (n+1)) he
  have hcast := ZMod.natCast_zmod_val (n:=n+2)
    (asResidue (n+1) (removeZero e cut hz j).succ)
  exact hcast.trans hc

/-- A source-exact physical coverage adapter for an explicit full residue
order. The reflection adjacency hypothesis is proved by the family clients. -/
theorem covers {n r p a : ℕ} (e : Fin (n+2)≃Fin (n+2)) (cut : Fin (n+1))
    (hz : e cut.castSucc=0) (hr : r<n+2) (hp : p<n+2)
    (hpath : ∀i j : Fin (n+2),i≠j →
      (asResidue (n+1) (e i)+asResidue (n+1) (e j)=(r:ZMod (n+2)) ∨
        asResidue (n+1) (e i)+asResidue (n+1) (e j)=(p:ZMod (n+2))) →
      i.val+1=j.val ∨ j.val+1=i.val) : Covers (layout e cut hz) r p a := by
  intro u v hb
  have hne : u≠v := by intro h; subst v; simp [edgeBound] at hb
  have ht : TargetPair r u v ∨ TargetPair p u v := by
    unfold edgeBound at hb
    split_ifs at hb with h0 hs hc
    · omega
    · rcases hs with hs|hs
      · exact Or.inl (Or.inl hs)
      · exact Or.inr (Or.inl hs)
    · rcases hc with hc|hc
      · exact Or.inl (Or.inr hc)
      · exact Or.inr (Or.inr hc)
    · omega
  obtain ⟨⟨c,i⟩,rfl⟩ := (layout e cut hz).label.surjective u
  obtain ⟨⟨d,j⟩,rfl⟩ := (layout e cut hz).label.surjective v
  fin_cases c
  fin_cases d
  apply adjacent_of_positions (layout e cut hz) 0 i j
  apply Or.imp id Or.inl
  apply adjacent_after_delete cut i j
  apply hpath
  · intro h
    have hh := congrArg cut.predAbove h
    simp only [Fin.predAbove_succAbove] at hh
    subst j
    exact hne rfl
  · rcases ht with ht|ht
    · left
      have hh := (targetPair_iff_zmod hr _ _).mp ht
      exact (congrArg₂ (·+·) (physical_cast e cut hz i) (physical_cast e cut hz j)).symm.trans hh
    · right
      have hh := (targetPair_iff_zmod hp _ _).mp ht
      exact (congrArg₂ (·+·) (physical_cast e cut hz i) (physical_cast e cut hz j)).symm.trans hh

/-- Complete executable layouts for all consecutive physical pivots. -/
abbrev consecutiveLayout (n : ℕ) (r : Fin (n+1)) : Layout (n+2) :=
  layout (order (n+1) r.val) r (order_zero (n+1) r.castSucc)

theorem consecutive_covers (n a : ℕ) (r : Fin (n+1)) :
    Covers (consecutiveLayout n r) r.val (r.val+1) a := by
  apply covers (order (n+1) r.val) r (order_zero (n+1) r.castSucc)
    (by have := r.isLt; omega) (by have := r.isLt; omega)
  intro i j hne h
  exact ReflectionConsecutive.adjacent_of_pair (n+1) r.val (by omega) i j hne h

#print axioms physical_cast
#print axioms covers
#print axioms consecutive_covers
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionPath
