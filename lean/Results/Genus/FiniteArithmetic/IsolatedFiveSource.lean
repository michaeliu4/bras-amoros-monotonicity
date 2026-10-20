import Results.Genus.FiniteArithmetic.ReflectionConstraints
import Results.Genus.FiniteArithmetic.CapacitySeries

namespace SubmittedGenus.FiniteArithmetic.IsolatedFive

open scoped BigOperators
open PowerSeries
open Reflection

abbrev leftSystem := boundedSystem 5 3
abbrev rightSystem := boundedSystem 4 3

noncomputable instance leftBlocksFintype (n : ℕ) : Fintype (Blocks leftSystem n) := blocksFintype leftSystem n
noncomputable instance rightBlocksFintype (n : ℕ) : Fintype (Blocks rightSystem n) := blocksFintype rightSystem n

noncomputable def leftSeries : PowerSeries ℤ := Reflection.blockSeries leftSystem
noncomputable def rightSeries : PowerSeries ℤ := Reflection.blockSeries rightSystem

theorem leftPair_polynomial : pairPolynomial 5 3 = 2 • (X : PowerSeries ℤ)^5 + X^6 := by
  simp [pairPolynomial, Fintype.sum_prod_type, Fin.sum_univ_succ]
  ring

theorem leftCenter_polynomial : centerPolynomial 5 3 = (X : PowerSeries ℤ)^3 := by
  simp [centerPolynomial, Fin.sum_univ_succ]

theorem rightPair_polynomial : pairPolynomial 4 3 = 3 • (X : PowerSeries ℤ)^4 + 2 • X^5 + X^6 := by
  simp [pairPolynomial, Fintype.sum_prod_type, Fin.sum_univ_succ]
  ring

theorem rightCenter_polynomial : centerPolynomial 4 3 = (X : PowerSeries ℤ)^2 + X^3 := by
  simp [centerPolynomial, Fin.sum_univ_succ]

theorem leftSeries_identity : (1 - 2 • (X : PowerSeries ℤ)^5 - X^6) * leftSeries = 1 + X^3 := by
  have h := bounded_block_identity 5 3
  rw [leftPair_polynomial, leftCenter_polynomial] at h
  simpa [leftSeries, sub_sub] using h

theorem rightSeries_identity : (1 - 3 • (X : PowerSeries ℤ)^4 - 2 • X^5 - X^6) * rightSeries =
    1 + X^2 + X^3 := by
  have h := bounded_block_identity 4 3
  rw [rightPair_polynomial, rightCenter_polynomial] at h
  simpa [rightSeries, sub_sub, add_assoc] using h

/-- Every {2,3} word satisfies the exact right reflection constraints. -/
theorem language_of_twothree {w : List ℕ} (hw : ∀ a ∈ w, a = 2 ∨ a = 3) :
    Language rightSystem.pairAllowed rightSystem.centerAllowed w := by
  induction w using List.bidirectionalRec with
  | nil => exact Language.nil
  | singleton a =>
    have ha := hw a (by simp)
    apply Language.singleton a
    change 1 ≤ a ∧ a ≤ 3 ∧ 4 ≤ 2 * a
    omega
  | cons_append a w b ih =>
    have ha := hw a (by simp)
    have hb := hw b (by simp)
    apply Language.pair a b w
    · change 1 ≤ a ∧ a ≤ 3 ∧ 1 ≤ b ∧ b ≤ 3 ∧ 4 ≤ a + b
      omega
    · apply ih
      intro x hx
      exact hw x (by simp [hx])

def physical23 (w : List (Fin 2)) : List ℕ := w.map (fun a => a.val + 2)

theorem physical23_letters (w : List (Fin 2)) :
    ∀ a ∈ physical23 w, a = 2 ∨ a = 3 := by
  intro a ha
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
  have := i.isLt
  omega

theorem physical23_injective : Function.Injective physical23 := by
  apply List.map_injective_iff.mpr
  intro a b h
  apply Fin.ext
  dsimp at h
  omega

def word23IntoRightBlock (n : ℕ) (w : ExactWords alphabet23 n) : Blocks rightSystem n :=
  ⟨physical23 w.val, language_of_twothree (physical23_letters w.val), w.property⟩

theorem word23IntoRightBlock_injective (n : ℕ) : Function.Injective (word23IntoRightBlock n) := by
  intro a b h
  exact Subtype.ext (physical23_injective (congrArg Subtype.val h))

def shrink23 : (w : List ℕ) → (∀ a ∈ w, a = 2 ∨ a = 3) → List (Fin 2)
  | [], _ => []
  | a :: w, h => ⟨a - 2, by have := h a (by simp); omega⟩ ::
      shrink23 w (fun b hb => h b (by simp [hb]))

theorem physical_shrink23 (w : List ℕ) (h : ∀ a ∈ w, a = 2 ∨ a = 3) :
    physical23 (shrink23 w h) = w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    change (a - 2 + 2) :: physical23 (shrink23 w _) = a :: w
    congr 1
    · have := h a (by simp)
      omega
    · exact ih _

theorem word23IntoRightBlock_range (n : ℕ) (w : Blocks rightSystem n) :
    w ∈ Set.range (word23IntoRightBlock n) ↔ ∀ a ∈ w.val, a = 2 ∨ a = 3 := by
  constructor
  · rintro ⟨v, rfl⟩
    exact physical23_letters v.val
  · intro h
    have hs : ((shrink23 w.val h).map alphabet23.weight).sum = n := by
      have he := congrArg List.sum (physical_shrink23 w.val h)
      exact he.trans w.property.2
    refine ⟨⟨shrink23 w.val h, hs⟩, ?_⟩
    exact Subtype.ext (physical_shrink23 w.val h)

theorem word23IntoRightBlock_range_iff_noOne (n : ℕ) (w : Blocks rightSystem n) :
    w ∈ Set.range (word23IntoRightBlock n) ↔ 1 ∉ w.val := by
  rw [word23IntoRightBlock_range]
  constructor
  · intro h hone
    have := h 1 hone
    omega
  · intro h a ha
    have hb := bounded_language_letters w.property.1 a ha
    have hne : a ≠ 1 := by intro he; subst a; exact h ha
    change 1 ≤ a ∧ a ≤ 3 at hb
    omega

/-- The right block must contain a 1 because the no-1 sources were removed. -/
abbrev RightMarkedWords (n : ℕ) :=
  {w : Blocks rightSystem n // ¬ w ∈ Set.range (word23IntoRightBlock n)}

noncomputable instance rightMarkedWordsFintype (n : ℕ) : Fintype (RightMarkedWords n) := Fintype.ofFinite _

theorem rightMarked_iff_hasOne (n : ℕ) (w : Blocks rightSystem n) :
    (¬ w ∈ Set.range (word23IntoRightBlock n)) ↔ 1 ∈ w.val := by
  rw [word23IntoRightBlock_range_iff_noOne]
  simp

noncomputable def rightMarkedSeries : PowerSeries ℤ := Graded.series RightMarkedWords

theorem rightMarkedSeries_identity : rightMarkedSeries = rightSeries - capacityC0 := by
  classical
  apply PowerSeries.ext
  intro n
  have hi := Fintype.card_le_of_injective (word23IntoRightBlock n) (word23IntoRightBlock_injective n)
  have hc : Fintype.card (Set.range (word23IntoRightBlock n)) =
      Fintype.card (ExactWords alphabet23 n) :=
    (Fintype.card_congr (Equiv.ofInjective _ (word23IntoRightBlock_injective n))).symm
  have hh : Fintype.card (RightMarkedWords n) = Fintype.card (Blocks rightSystem n) -
      Fintype.card (ExactWords alphabet23 n) := by
    rw [Fintype.card_subtype_compl, hc]
  simp only [rightMarkedSeries, Graded.coeff_series, map_sub, rightSeries,
    Reflection.coeff_blockSeries, capacityC0, coeff_wordSeries, wordCount]
  rw [hh, Int.ofNat_sub hi]

abbrev LeftNonemptyWords (n : ℕ) := {w : Blocks leftSystem n // w.val ≠ []}
noncomputable instance leftNonemptyWordsFintype (n : ℕ) : Fintype (LeftNonemptyWords n) := Fintype.ofFinite _
noncomputable def leftNonemptySeries : PowerSeries ℤ := Graded.series LeftNonemptyWords

instance leftZeroUnique : Unique (Blocks leftSystem 0) where
  default := ⟨[], Language.nil, rfl⟩
  uniq w := by
    apply Subtype.ext
    by_contra hne
    have hp := w.property.1.sum_pos_of_nonempty
      (fun a b hab => hab.1) (fun a ha => ha.1) hne
    rw [w.property.2] at hp
    omega

instance leftNonemptyZeroEmpty : IsEmpty (LeftNonemptyWords 0) where
  false w := w.property (congrArg Subtype.val (leftZeroUnique.uniq w.val))

noncomputable def leftNonemptyEquiv (n : ℕ) (hn : n ≠ 0) :
    LeftNonemptyWords n ≃ Blocks leftSystem n :=
  Equiv.ofBijective (fun w => w.val) (by
    constructor
    · intro a b h
      exact Subtype.ext h
    · intro w
      refine ⟨⟨w, ?_⟩, rfl⟩
      intro he
      have hs := w.property.2
      rw [he] at hs
      exact hn hs.symm)

theorem leftNonemptySeries_identity : leftNonemptySeries = leftSeries - 1 := by
  apply PowerSeries.ext
  intro n
  simp only [leftNonemptySeries, Graded.coeff_series, map_sub, leftSeries,
    Reflection.coeff_blockSeries, coeff_one]
  by_cases hn : n = 0
  · subst n
    simp
  · rw [if_neg hn, sub_zero]
    exact congrArg (fun x : ℕ => (x : ℤ)) (Fintype.card_congr (leftNonemptyEquiv n hn))

/-- Exactly the original isolated-five block source: nonempty left, pivot 5,
and a right block containing a 1. -/
abbrev JSource := Graded.Shift 5 (Graded.Product LeftNonemptyWords RightMarkedWords)
noncomputable def capacityJ : PowerSeries ℤ := Graded.series JSource

@[simp] theorem capacityJ_source_coeff (n : ℕ) :
    coeff n capacityJ = (Fintype.card (JSource n) : ℤ) := by simp [capacityJ]

theorem capacityJ_factorization : capacityJ =
    (X : PowerSeries ℤ)^5 * (leftSeries - 1) * (rightSeries - capacityC0) := by
  unfold capacityJ JSource
  rw [Graded.shift_series, Graded.product_series]
  change X^5 * (leftNonemptySeries * rightMarkedSeries) = _
  rw [leftNonemptySeries_identity, rightMarkedSeries_identity]
  ring

/-- The original displayed J rational function follows from its counted source. -/
theorem capacityJ_source_identity :
    ((1 - 2 • (X : PowerSeries ℤ)^5 - X^6) * (1 - X^2 - X^3) *
      (1 - 3 • X^4 - 2 • X^5 - X^6)) * capacityJ =
      2 • X^12 + 4 • X^14 + 2 • X^15 := by
  rw [capacityJ_factorization]
  calc
    _ = X^5 *
        (((1 - 2 • (X : PowerSeries ℤ)^5 - X^6) * leftSeries) -
          (1 - 2 • X^5 - X^6)) *
        ((1 - X^2 - X^3) * ((1 - 3 • X^4 - 2 • X^5 - X^6) * rightSeries) -
          (1 - 3 • X^4 - 2 • X^5 - X^6) * ((1 - X^2 - X^3) * capacityC0)) := by
      simp only [nsmul_eq_mul]
      ring
    _ = 2 • X^12 + 4 • X^14 + 2 • X^15 := by
      rw [leftSeries_identity, rightSeries_identity, capacityC0_source_identity]
      simp only [nsmul_eq_mul]
      ring

#print axioms rightMarkedSeries_identity
#print axioms capacityJ_source_coeff
#print axioms capacityJ_source_identity

end SubmittedGenus.FiniteArithmetic.IsolatedFive
