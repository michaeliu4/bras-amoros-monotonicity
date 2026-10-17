import Results.Genus.Injection.ReservoirSources.DecoratedLayouts

noncomputable section
namespace SubmittedGenus.FiniteArithmetic.Reservoir
open scoped BigOperators

/-- Transport exact graded decoding through a weight-preserving bijection. -/
def Presentation.transport {F : ℕ→Type} {A B : Type} (p : Presentation F A)
    (e : A≃B) (w : B→ℕ) (hw : ∀a,w (e a)=p.weight a) : Presentation F B where
  weight := w
  equiv g := (p.equiv g).trans (e.subtypeEquiv (fun a => by rw [hw]))

def Presentation.sum {F G : ℕ→Type} {A B : Type}
    (p : Presentation F A) (q : Presentation G B) : Presentation (Graded.Sum F G) (A⊕B) where
  weight := Sum.elim p.weight q.weight
  equiv g := {
    toFun := fun a => match a with
      | .inl a => ⟨.inl (p.equiv g a).val,(p.equiv g a).property⟩
      | .inr a => ⟨.inr (q.equiv g a).val,(q.equiv g a).property⟩
    invFun := fun a => match a with
      | ⟨.inl a,h⟩ => .inl ((p.equiv g).symm ⟨a,h⟩)
      | ⟨.inr a,h⟩ => .inr ((q.equiv g).symm ⟨a,h⟩)
    left_inv := by intro a; cases a <;> simp
    right_inv := by rintro ⟨a|b,h⟩ <;> simp }

def atomPresentation {A : Type} (w : A→ℕ) : Presentation (Graded.Atoms w) A :=
  ⟨w,fun _ => Equiv.refl _⟩

def wordPresentation (A : LocallyFinite.Alphabet) :
    Presentation (LocallyFinite.Words A) (List A.Letter) :=
  ⟨fun l => (l.map A.weight).sum,fun _ => Equiv.refl _⟩

/-- An exact graded presentation equipped with its independent slot layout. -/
structure DecoratedPresentation (D : Decoration) (F : ℕ→Type) (A : Type) where
  layout : DecorationLayout A
  presentation : Presentation F (layout.Object D)
  weight_eq : presentation.weight=layout.objectWeight D

def DecoratedPresentation.plain {F : ℕ→Type} {A : Type} (D : Decoration)
    (p : Presentation F A) : DecoratedPresentation D F A :=
  ⟨DecorationLayout.plain p.weight,
    p.transport (plainObjectEquiv D p.weight)
      ((DecorationLayout.plain p.weight).objectWeight D) (plainObjectEquiv_weight D p.weight),rfl⟩

def DecoratedPresentation.slots (D : Decoration) (k : ℕ) :
    DecoratedPresentation D (D.Atoms k) Unit :=
  ⟨DecorationLayout.slots k,
    (atomPresentation (fun f : Fin k→D.Letter => ∑i,D.weight (f i))).transport
      (slotsObjectEquiv D k) ((DecorationLayout.slots k).objectWeight D)
      (slotsObjectEquiv_weight D k),rfl⟩

def DecoratedPresentation.product {F G : ℕ→Type} {A B : Type} {D : Decoration}
    (p : DecoratedPresentation D F A) (q : DecoratedPresentation D G B) :
    DecoratedPresentation D (Graded.Product F G) (A×B) :=
  ⟨p.layout.product q.layout,
    (p.presentation.product q.presentation).transport (productObjectEquiv D p.layout q.layout)
      ((p.layout.product q.layout).objectWeight D) (by
        intro a
        rw [productObjectEquiv_weight]
        change _=p.presentation.weight a.1+q.presentation.weight a.2
        rw [p.weight_eq,q.weight_eq]),rfl⟩

def DecoratedPresentation.shift {F : ℕ→Type} {A : Type} {D : Decoration}
    (p : DecoratedPresentation D F A) (k : ℕ) :
    DecoratedPresentation D (Graded.Shift k F) A :=
  ⟨p.layout.shift k,
    (p.presentation.shift k).transport (Equiv.refl _)
      ((p.layout.shift k).objectWeight D) (by
        intro a
        change (p.layout.weight a.1+k)+(∑i,D.weight (a.2 i))=p.presentation.weight a+k
        rw [p.weight_eq]
        unfold DecorationLayout.objectWeight
        omega),rfl⟩

def DecoratedPresentation.sum {F G : ℕ→Type} {A B : Type} {D : Decoration}
    (p : DecoratedPresentation D F A) (q : DecoratedPresentation D G B) :
    DecoratedPresentation D (Graded.Sum F G) (A⊕B) :=
  ⟨p.layout.sum q.layout,
    (p.presentation.sum q.presentation).transport (sumObjectEquiv D p.layout q.layout)
      ((p.layout.sum q.layout).objectWeight D) (by
        intro a
        rw [sumObjectEquiv_weight]
        change _=Sum.elim p.presentation.weight q.presentation.weight a
        rw [p.weight_eq,q.weight_eq]),rfl⟩

def DecoratedPresentation.words {A : Type} [Fintype A] (D : Decoration)
    (w : A→ℕ) (hw : ∀a,0<w a) (k : ℕ) :
    DecoratedPresentation D (LocallyFinite.Words (decoratedAlphabet w hw D k)) (List A) :=
  ⟨DecorationLayout.words w k,
    (wordPresentation (decoratedAlphabet w hw D k)).transport (wordObjectEquiv D w k)
      ((DecorationLayout.words w k).objectWeight D) (wordObjectEquiv_weight D w k),rfl⟩

/-- Finite-slot relabelling is a genuine bijection of decorations and
preserves their total weight, independently of how the slots were grouped. -/
def DecorationLayout.reindexEquiv {A B : Type} (D : Decoration) (L : DecorationLayout A)
    (e : A≃B) (d : B→ℕ) (hc : ∀a,Fintype.card (L.Index a)=d (e a)) :
    L.Object D ≃ (Σ b:B,Fin (d b)→D.Letter) :=
  (Equiv.sigmaCongrRight (fun a =>
    Equiv.arrowCongr ((Fintype.equivFin (L.Index a)).trans (finCongr (hc a))) (Equiv.refl _))).trans
      (Equiv.sigmaCongrLeft (β := fun b => Fin (d b)→D.Letter) e)

lemma DecorationLayout.reindex_weight {A B : Type} (D : Decoration) (L : DecorationLayout A)
    (e : A≃B) (d w : B→ℕ) (hc : ∀a,Fintype.card (L.Index a)=d (e a))
    (hw : ∀a,w (e a)=L.weight a) (a : L.Object D) :
    w (L.reindexEquiv D e d hc a).1 +
      (∑i,D.weight ((L.reindexEquiv D e d hc a).2 i))=L.objectWeight D a := by
  rcases a with ⟨a,f⟩
  change w (e a)+(∑i,D.weight (f (((Fintype.equivFin (L.Index a)).trans (finCongr (hc a))).symm i)))=
    L.weight a+∑i,D.weight (f i)
  rw [hw]
  congr 1
  exact Equiv.sum_comp ((Fintype.equivFin (L.Index a)).trans (finCongr (hc a))).symm
    (fun i => D.weight (f i))

/-- Collapse a proved layout to one physical decoration per distance unit. -/
def DecoratedPresentation.reindex {F : ℕ→Type} {A B : Type} {D : Decoration}
    (p : DecoratedPresentation D F A) (e : A≃B) (d w : B→ℕ)
    (hc : ∀a,Fintype.card (p.layout.Index a)=d (e a))
    (hw : ∀a,w (e a)=p.layout.weight a) :
    Presentation F (Σ b:B,Fin (d b)→D.Letter) :=
  p.presentation.transport (p.layout.reindexEquiv D e d hc)
    (fun x => w x.1+∑i,D.weight (x.2 i)) (by
      intro a
      rw [p.layout.reindex_weight D e d w hc hw,p.weight_eq])

#print axioms DecoratedPresentation.reindex
end SubmittedGenus.FiniteArithmetic.Reservoir
