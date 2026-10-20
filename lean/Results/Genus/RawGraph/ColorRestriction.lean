import Results.Genus.RawGraph.Conditioning

namespace SubmittedGenus.RawGraph.ColorRestriction
open scoped BigOperators

/-- The carry transfer's three states are the physical values1,2,3. -/
def positiveColor (i : Fin 3) : Fin 5 := ⟨i.val + 1, by have := i.isLt; omega⟩

def PositiveColor (i : Fin 5) : Prop := 1 ≤ i.val ∧ i.val ≤ 3
instance (i : Fin 5) : Decidable (PositiveColor i) := by unfold PositiveColor; infer_instance

@[simp] theorem positiveColor_val (i : Fin 3) : (positiveColor i).val = i.val + 1 := rfl

def assignmentEquiv (V : Type*) : (V → Fin 3) ≃ {x : V → Fin 5 // ∀ v, PositiveColor (x v)} where
  toFun y := ⟨fun v => positiveColor (y v), fun v => by
    have := (y v).isLt; unfold PositiveColor positiveColor; dsimp; omega⟩
  invFun x v := ⟨(x.val v).val - 1, by have := x.property v; unfold PositiveColor at this; omega⟩
  left_inv y := by
    funext v
    apply Fin.ext
    simp [positiveColor]
  right_inv x := by
    apply Subtype.ext
    funext v
    apply Fin.ext
    have := x.property v
    unfold PositiveColor at this
    dsimp [positiveColor]
    omega

/-- Delete out-of-alphabet assignments only after proving their contributions
are zero; this is an exact finite sum reindexing, not an alphabet assumption. -/
theorem sum_restrict_positive {V R : Type*} [Fintype V] [DecidableEq V]
    [AddCommMonoid R] (f : (V → Fin 5) → R)
    (hf : ∀ x, ¬ (∀ v, PositiveColor (x v)) → f x = 0) :
    (∑ x, f x) = ∑ y : V → Fin 3, f (fun v => positiveColor (y v)) := by
  classical
  let P (x : V → Fin 5) := ∀ v, PositiveColor (x v)
  calc
    (∑ x, f x) = ∑ x, if P x then f x else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : P x
      · simp [hx]
      · simp [hx, hf x hx]
    _ = ∑ x : {x : V → Fin 5 // P x}, f x.val := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype (Finset.univ.filter P) (by simp) f
    _ = ∑ y : V → Fin 3, f (fun v => positiveColor (y v)) :=
      ((assignmentEquiv V).sum_comp (fun x => f x.val)).symm

/-- The source-exact conditioned tail polynomial reduces to the physical
three-state alphabet once its actual unary constraints enforce1≤value≤3. -/
theorem componentPolynomial_restrict {m r p : ℕ} {K C : Type*}
    [Fintype K] [Fintype C] [DecidableEq K] [DecidableEq C]
    (L : Conditioning.Layout m K C) (x : K → Fin 5) (c : C)
    (hcolor : ∀ j v, Conditioning.TailUnary L r p 4 x c j v → PositiveColor v) :
    Conditioning.componentPolynomial L r p 4 x c =
      ∑ y : Fin (L.edges c + 1) → Fin 3,
        Conditioning.tailTerm L r p 4 x c (fun j => positiveColor (y j)) := by
  unfold Conditioning.componentPolynomial
  apply sum_restrict_positive
  intro y hy
  have hnot : ¬ Conditioning.TailAllowed L r p 4 x c y := by
    intro h
    exact hy (fun j => hcolor j (y j) ((h.1) j))
  simp [Conditioning.tailTerm, hnot]

/-- The same restriction applies directly to the verified transfer evaluator. -/
theorem componentRun_restrict {m r p : ℕ} {K C : Type*}
    [Fintype K] [Fintype C] [DecidableEq K] [DecidableEq C]
    (L : Conditioning.Layout m K C) (x : K → Fin 5) (c : C)
    (hcolor : ∀ j v, Conditioning.TailUnary L r p 4 x c j v → PositiveColor v) :
    Conditioning.componentRun L r p 4 x c =
      ∑ y : Fin (L.edges c + 1) → Fin 3,
        Conditioning.tailTerm L r p 4 x c (fun j => positiveColor (y j)) := by
  rw [Conditioning.componentRun_eq_polynomial]
  exact componentPolynomial_restrict L x c hcolor

end SubmittedGenus.RawGraph.ColorRestriction
