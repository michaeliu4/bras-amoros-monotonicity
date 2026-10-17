import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic

/-!
# Finite-set allocation used by the submitted partial injection

These general lemmas implement the finite-set step of `cmb:partial`:
reserve the actual code images, inject the remaining demand into their
complement, and bound the single unused set by the maximum of two bounds.
They do not assert that numerical-semigroup source classes satisfy the
required capacity inequalities. Those semantic and analytic premises must
be supplied separately by the original-paper proofs.
-/

namespace SubmittedGenus.Allocation

open Function

attribute [local instance] Classical.propDecidable

variable {A B T : Type*} [Fintype A] [Fintype B] [Fintype T]

/-- An existing injection can be reserved while allocating a second finite
source type, provided the combined demand fits in the target type. -/
theorem exists_embedding_avoiding_reserved (reserved : A ↪ T)
    (hcapacity : Fintype.card A + Fintype.card B ≤ Fintype.card T) :
    ∃ fresh : B ↪ T, ∀ b a, fresh b ≠ reserved a := by
  classical
  let R : Set T := Set.range reserved
  have hcard : Fintype.card {t : T // t ∉ R} =
      Fintype.card T - Fintype.card A := by
    simp only [R, Fintype.card_subtype_compl, Fintype.card_range]
  have hfit : Fintype.card B ≤ Fintype.card {t : T // t ∉ R} := by
    rw [hcard]
    omega
  obtain ⟨e⟩ := Embedding.nonempty_of_card_le hfit
  let fresh : B ↪ T := e.trans (Embedding.subtype _)
  refine ⟨fresh, ?_⟩
  intro b a heq
  exact (e b).property ⟨a, heq.symm⟩

/-- Join two disjoint embeddings, keeping the reserved map exactly. -/
def joinEmbeddings (reserved : A ↪ T) (fresh : B ↪ T)
    (hdisjoint : ∀ b a, fresh b ≠ reserved a) : A ⊕ B ↪ T where
  toFun := Sum.elim reserved fresh
  inj' := by
    intro x y h
    cases x with
    | inl a =>
      cases y with
      | inl a' => exact congrArg Sum.inl (reserved.injective h)
      | inr b => exact (hdisjoint b a h.symm).elim
    | inr b =>
      cases y with
      | inl a => exact (hdisjoint b a h).elim
      | inr b' => exact congrArg Sum.inr (fresh.injective h)

@[simp] theorem joinEmbeddings_inl (reserved : A ↪ T) (fresh : B ↪ T)
    (hdisjoint : ∀ b a, fresh b ≠ reserved a) (a : A) :
    joinEmbeddings reserved fresh hdisjoint (Sum.inl a) = reserved a := rfl

@[simp] theorem joinEmbeddings_inr (reserved : A ↪ T) (fresh : B ↪ T)
    (hdisjoint : ∀ b a, fresh b ≠ reserved a) (b : B) :
    joinEmbeddings reserved fresh hdisjoint (Sum.inr b) = fresh b := rfl

/-- Existential finite allocation extending the actual reserved injection.
No ranking or arbitrary replacement of the reserved image is needed. -/
theorem exists_reserved_extension (reserved : A ↪ T)
    (hcapacity : Fintype.card A + Fintype.card B ≤ Fintype.card T) :
    ∃ total : A ⊕ B ↪ T, ∀ a, total (Sum.inl a) = reserved a := by
  obtain ⟨fresh, hfresh⟩ := exists_embedding_avoiding_reserved reserved hcapacity
  exact ⟨joinEmbeddings reserved fresh hfresh, fun _ => rfl⟩

/-- The exact unused cardinality of any finite injection. -/
theorem card_unused (e : A ↪ T) :
    Fintype.card {t : T // t ∉ Set.range e} = Fintype.card T - Fintype.card A := by
  classical
  simp only [Fintype.card_subtype_compl, Fintype.card_range]

/-- Both submitted binary-capacity estimates apply to the same unused set.
For natural `F`, `(12*F+24)/25` is `ceil(12*F/25)`. -/
theorem binary_unused_lower_bound (F W demand unused : ℕ)
    (hcount : unused + demand = F)
    (hmajorant : demand ≤ W) (hproportion : 25 * demand ≤ 13 * F) :
    max ((12 * F + 24) / 25) (F - W) ≤ unused := by
  apply max_le <;> omega

/-- The separate stronger bound for the original paper's `g ≥ 141` range. -/
theorem binary_unused_sharp_bound (F demand unused : ℕ)
    (hcount : unused + demand = F) (hproportion : 1000 * demand ≤ 13 * F) :
    987 * F ≤ 1000 * unused := by omega

/-- Exact accounting for a partial injection away from an exceptional set. -/
theorem partial_injection_balance {S U : Type*} [Fintype S] [Fintype U]
    (exceptional : S → Prop) [DecidablePred exceptional]
    (partialMap : {s : S // ¬ exceptional s} ↪ U) :
    Fintype.card U + Fintype.card {s : S // exceptional s} =
      Fintype.card S + Fintype.card {u : U // u ∉ Set.range partialMap} := by
  classical
  have he := Fintype.card_subtype_le exceptional
  have hp := Fintype.card_le_of_embedding partialMap
  have hc := Fintype.card_subtype_compl exceptional
  rw [card_unused]
  omega

/-- The submitted argument's final purely finite comparison: unused targets
cover exceptional sources. This theorem does not supply that coverage. -/
theorem cardinal_monotone_of_unused_covers_exceptional
    {S U : Type*} [Fintype S] [Fintype U]
    (exceptional : S → Prop) [DecidablePred exceptional]
    (partialMap : {s : S // ¬ exceptional s} ↪ U)
    (hcover : Fintype.card {s : S // exceptional s} ≤
      Fintype.card {u : U // u ∉ Set.range partialMap}) :
    Fintype.card S ≤ Fintype.card U := by
  have h := partial_injection_balance exceptional partialMap
  omega

end SubmittedGenus.Allocation
