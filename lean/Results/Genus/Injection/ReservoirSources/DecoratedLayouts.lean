import Results.Genus.FiniteArithmetic.Reservoir.Presentations
import Results.Genus.FiniteArithmetic.Reservoir.DecoratedWords
import Mathlib.Data.Fintype.Sum

noncomputable section
namespace SubmittedGenus.FiniteArithmetic.Reservoir
open scoped BigOperators

/-- A literal base with a finite collection of independent decoration slots.
The index set is retained until the final physical-distance identification. -/
structure DecorationLayout (A : Type) where
  weight : A → ℕ
  Index : A → Type
  finite : ∀ a, Fintype (Index a)

attribute [instance] DecorationLayout.finite

abbrev DecorationLayout.Object {A : Type} (L : DecorationLayout A) (D : Decoration) :=
  Σ a : A, L.Index a → D.Letter

def DecorationLayout.objectWeight {A : Type} (L : DecorationLayout A) (D : Decoration)
    (a : L.Object D) : ℕ := L.weight a.1 + ∑ i, D.weight (a.2 i)

def DecorationLayout.plain {A : Type} (w : A → ℕ) : DecorationLayout A :=
  ⟨w,fun _ => Fin 0,fun _ => inferInstance⟩

def DecorationLayout.slots (k : ℕ) : DecorationLayout Unit :=
  ⟨fun _ => 0,fun _ => Fin k,fun _ => inferInstance⟩

def DecorationLayout.product {A B : Type} (L : DecorationLayout A) (M : DecorationLayout B) :
    DecorationLayout (A×B) :=
  ⟨fun a => L.weight a.1+M.weight a.2,
    fun a => L.Index a.1 ⊕ M.Index a.2,fun _ => inferInstance⟩

def DecorationLayout.shift {A : Type} (L : DecorationLayout A) (k : ℕ) : DecorationLayout A :=
  ⟨fun a => L.weight a+k,L.Index,L.finite⟩

def DecorationLayout.sum {A B : Type} (L : DecorationLayout A) (M : DecorationLayout B) :
    DecorationLayout (A⊕B) where
  weight := Sum.elim L.weight M.weight
  Index := Sum.elim L.Index M.Index
  finite a := by cases a <;> dsimp <;> infer_instance

def DecorationLayout.words {A : Type} (w : A → ℕ) (k : ℕ) : DecorationLayout (List A) :=
  ⟨fun l => (l.map w).sum,fun l => Fin l.length × Fin k,fun _ => inferInstance⟩

def plainObjectEquiv {A : Type} (D : Decoration) (w : A → ℕ) :
    A ≃ (DecorationLayout.plain w).Object D where
  toFun a := ⟨a,Fin.elim0⟩
  invFun a := a.1
  left_inv _ := rfl
  right_inv a := by
    rcases a with ⟨a,f⟩
    dsimp only
    apply congrArg (Sigma.mk _)
    funext i
    exact Fin.elim0 i

lemma plainObjectEquiv_weight {A : Type} (D : Decoration) (w : A → ℕ) (a : A) :
    (DecorationLayout.plain w).objectWeight D (plainObjectEquiv D w a)=w a := by
  change w a + (∑i:Fin 0,D.weight (Fin.elim0 i))=w a
  simp

def slotsObjectEquiv (D : Decoration) (k : ℕ) :
    (Fin k → D.Letter) ≃ (DecorationLayout.slots k).Object D where
  toFun f := ⟨(),f⟩
  invFun f := f.2
  left_inv _ := rfl
  right_inv f := by rcases f with ⟨⟨⟩,f⟩; rfl

lemma slotsObjectEquiv_weight (D : Decoration) (k : ℕ) (f : Fin k → D.Letter) :
    (DecorationLayout.slots k).objectWeight D (slotsObjectEquiv D k f)=∑i,D.weight (f i) := by
  change 0+(∑i:Fin k,D.weight (f i))=_
  omega

def productObjectEquiv {A B : Type} (D : Decoration) (L : DecorationLayout A) (M : DecorationLayout B) :
    L.Object D × M.Object D ≃ (L.product M).Object D where
  toFun p := ⟨(p.1.1,p.2.1),Sum.elim p.1.2 p.2.2⟩
  invFun p := (⟨p.1.1,fun i => p.2 (.inl i)⟩,⟨p.1.2,fun i => p.2 (.inr i)⟩)
  left_inv _ := rfl
  right_inv p := by
    rcases p with ⟨⟨a,b⟩,f⟩
    dsimp only
    apply congrArg (Sigma.mk _)
    funext i
    cases i <;> rfl

lemma productObjectEquiv_weight {A B : Type} (D : Decoration) (L : DecorationLayout A)
    (M : DecorationLayout B) (p : L.Object D × M.Object D) :
    (L.product M).objectWeight D (productObjectEquiv D L M p)=
      L.objectWeight D p.1+M.objectWeight D p.2 := by
  change (L.weight p.1.1+M.weight p.2.1) +
    (∑i:L.Index p.1.1 ⊕ M.Index p.2.1,D.weight (Sum.elim p.1.2 p.2.2 i)) =
    (L.weight p.1.1+∑i,D.weight (p.1.2 i))+(M.weight p.2.1+∑i,D.weight (p.2.2 i))
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl,Sum.elim_inr]
  omega

def sumObjectEquiv {A B : Type} (D : Decoration) (L : DecorationLayout A) (M : DecorationLayout B) :
    L.Object D ⊕ M.Object D ≃ (L.sum M).Object D where
  toFun p := match p with
    | .inl p => ⟨.inl p.1,p.2⟩
    | .inr p => ⟨.inr p.1,p.2⟩
  invFun p := match p with
    | ⟨.inl a,f⟩ => .inl ⟨a,f⟩
    | ⟨.inr b,f⟩ => .inr ⟨b,f⟩
  left_inv p := by cases p <;> rfl
  right_inv p := by rcases p with ⟨a|b,f⟩ <;> rfl

lemma sumObjectEquiv_weight {A B : Type} (D : Decoration) (L : DecorationLayout A)
    (M : DecorationLayout B) (p : L.Object D ⊕ M.Object D) :
    (L.sum M).objectWeight D (sumObjectEquiv D L M p)=
      Sum.elim (L.objectWeight D) (M.objectWeight D) p := by cases p <;> rfl

lemma fin_pair_heq_values {n m k : ℕ} (hnm : n=m) (i : Fin n×Fin k) (j : Fin m×Fin k)
    (h : HEq i j) : i.1.val=j.1.val ∧ i.2=j.2 := by
  subst m
  cases h
  exact ⟨rfl,rfl⟩

/-- A word of independently decorated letters is exactly an undecorated
word and one decoration per (physical letter, local slot). -/
def wordObjectEquiv {A : Type} (D : Decoration) (w : A → ℕ) (k : ℕ) :
    List (A×(Fin k→D.Letter)) ≃ (DecorationLayout.words w k).Object D where
  toFun l := ⟨l.map Prod.fst,fun i => (l[i.1.val]'(by simpa using i.1.isLt)).2 i.2⟩
  invFun p := List.ofFn (fun i : Fin p.1.length => (p.1[i.val],fun j => p.2 (i,j)))
  left_inv l := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp only [List.getElem_ofFn,List.getElem_map]
  right_inv p := by
    rcases p with ⟨l,f⟩
    have hl : (List.ofFn (fun i : Fin l.length => (l[i.val],fun j => f (i,j)))).map Prod.fst=l := by
      simp only [List.map_ofFn]
      exact List.ofFn_getElem
    apply Sigma.ext hl
    apply Function.hfunext (by simp [DecorationLayout.words])
    intro i j hij
    have hv := fin_pair_heq_values (by simp) i j hij
    apply heq_of_eq
    simp only [List.getElem_ofFn]
    congr 1
    exact Prod.ext (Fin.ext hv.1) hv.2

lemma wordObjectEquiv_weight {A : Type} (D : Decoration) (w : A → ℕ) (k : ℕ)
    (l : List (A×(Fin k→D.Letter))) :
    (DecorationLayout.words w k).objectWeight D (wordObjectEquiv D w k l)=
      (l.map (fun p => w p.1 + ∑i,D.weight (p.2 i))).sum := by
  change ((l.map Prod.fst).map w).sum +
    (∑i:Fin (l.map Prod.fst).length × Fin k,D.weight ((l[i.1.val]' (by simpa using i.1.isLt)).2 i.2))=_
  simp only [List.map_map,Function.comp_def,Fintype.sum_prod_type,List.length_map]
  rw [List.sum_map_add]
  congr 1
  rw [←List.sum_ofFn]
  congr 1
  apply List.ext_getElem <;> simp

end SubmittedGenus.FiniteArithmetic.Reservoir
