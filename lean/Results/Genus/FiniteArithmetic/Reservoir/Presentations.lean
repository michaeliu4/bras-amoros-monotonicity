import Results.Genus.FiniteArithmetic.Reservoir.PrefixSemantics

namespace SubmittedGenus.FiniteArithmetic.Reservoir

/-- Exact graded encodings, retaining independently specified literal objects. -/
structure Presentation (F : ℕ → Type) (A : Type) where
  weight : A → ℕ
  equiv : ∀ g, F g ≃ {a : A // weight a = g}

noncomputable def presentationOfDecode {F : ℕ → Type} {A : Type}
    (weight : A → ℕ) (decode : ∀ {g}, F g → A)
    (hw : ∀ {g} (a : F g), weight (decode a) = g)
    (hi : ∀ g, Function.Injective (@decode g))
    (hs : ∀ a : A, ∃ b : F (weight a), decode b = a) : Presentation F A where
  weight := weight
  equiv g := Equiv.ofBijective (fun a => ⟨decode a, hw a⟩) ⟨by
    intro a b h
    exact hi g (congrArg Subtype.val h), by
    rintro ⟨a, ha⟩
    subst g
    obtain ⟨b, hb⟩ := hs a
    exact ⟨b, Subtype.ext hb⟩⟩

noncomputable def safePresentation : Presentation SafeSource SafeCode :=
  presentationOfDecode SafeCode.weight safeSourceCode safeSourceCode_weight
    safeSourceCode_injective exists_safeSource

noncomputable def earlyPresentation : Presentation EarlySource EarlyCode :=
  presentationOfDecode EarlyCode.weight earlySourceCode earlySourceCode_weight
    earlySourceCode_injective exists_earlySource

noncomputable def Presentation.product {F G : ℕ → Type} {A B : Type}
    (p : Presentation F A) (q : Presentation G B) :
    Presentation (Graded.Product F G) (A × B) where
  weight x := p.weight x.1 + q.weight x.2
  equiv g := Equiv.ofBijective
    (fun x => ⟨((p.equiv x.1.val x.2.1).val, (q.equiv (g-x.1.val) x.2.2).val), by
      have hi := x.1.isLt
      have ha := (p.equiv x.1.val x.2.1).property
      have hb := (q.equiv (g-x.1.val) x.2.2).property
      dsimp
      omega⟩) ⟨by
    rintro ⟨i,a,b⟩ ⟨j,c,d⟩ h
    have h1 := congrArg (fun x => x.val.1) h
    have h2 := congrArg (fun x => x.val.2) h
    have hi := (p.equiv i.val a).property
    have hj := (p.equiv j.val c).property
    have hij : i = j := Fin.ext (by rw [← hi, ← hj]; exact congrArg p.weight h1)
    subst j
    have hac := (p.equiv i.val).injective (Subtype.ext h1)
    have hbd := (q.equiv (g-i.val)).injective (Subtype.ext h2)
    dsimp at hac hbd
    subst c; subst d; rfl, by
    rintro ⟨⟨a,b⟩,h⟩
    let i : Fin (g+1) := ⟨p.weight a, by dsimp at h; omega⟩
    let aa : {a : A // p.weight a = i.val} := ⟨a,rfl⟩
    let bb : {b : B // q.weight b = g-i.val} := ⟨b, by dsimp [i]; dsimp at h; omega⟩
    refine ⟨⟨i,(p.equiv i.val).symm aa,(q.equiv (g-i.val)).symm bb⟩, ?_⟩
    apply Subtype.ext
    simp only [Equiv.apply_symm_apply]
    rfl⟩

noncomputable def Presentation.shift {F : ℕ → Type} {A : Type}
    (p : Presentation F A) (d : ℕ) : Presentation (Graded.Shift d F) A where
  weight a := p.weight a + d
  equiv g := by
    by_cases hg : d ≤ g
    · let e : Graded.Shift d F g ≃ F (g-d) := Equiv.cast (if_pos hg)
      exact e.trans ((p.equiv (g-d)).trans {
        toFun := fun a => ⟨a.val, by have := a.property; omega⟩
        invFun := fun a => ⟨a.val, by have := a.property; omega⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl })
    · exact {
        toFun := fun a => (cast (if_neg hg) a : PEmpty).elim
        invFun := fun a => False.elim (by have := a.property; omega)
        left_inv := fun a => (cast (if_neg hg) a : PEmpty).elim
        right_inv := fun a => False.elim (by have := a.property; omega) }

#print axioms Presentation.product
#print axioms Presentation.shift
end SubmittedGenus.FiniteArithmetic.Reservoir
