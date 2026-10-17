import Results.Genus.FiniteArithmetic.CapacitySeries
import Mathlib.Data.List.Induction

/-!
# Actual words over locally finite positive-weight alphabets

This extends the first finite-alphabet slice to the genuinely unbounded ordered
pair alphabet required by the original q ≥ 9 capacity tail. Finiteness is proved
at each weight; it is not inferred from a bounded test range.
-/

namespace SubmittedGenus.FiniteArithmetic.LocallyFinite

open scoped BigOperators
open PowerSeries

structure Alphabet where
  Letter : Type
  weight : Letter → ℕ
  positive : ∀ a, 0 < weight a
  finiteBelow : ∀ n, Finite {a : Letter // weight a ≤ n}

instance belowFinite (A : Alphabet) (n : ℕ) : Finite {a : A.Letter // A.weight a ≤ n} :=
  A.finiteBelow n

abbrev Words (A : Alphabet) (n : ℕ) :=
  {w : List A.Letter // (w.map A.weight).sum = n}

abbrev Letters (A : Alphabet) (n : ℕ) := {a : A.Letter // A.weight a = n}

theorem length_le_weight (A : Alphabet) (w : List A.Letter) :
    w.length ≤ (w.map A.weight).sum := by
  induction w with
  | nil => simp
  | cons a w ih =>
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    have := A.positive a
    omega

theorem letter_weight_le (A : Alphabet) (w : List A.Letter) (a : A.Letter)
    (ha : a ∈ w) : A.weight a ≤ (w.map A.weight).sum := by
  induction w with
  | nil => simp at ha
  | cons b w ih =>
    simp only [List.mem_cons] at ha
    simp only [List.map_cons, List.sum_cons]
    rcases ha with rfl | ha
    · omega
    · have := ih ha
      omega

def boundWord (A : Alphabet) (n : ℕ) (w : Words A n) :
    {l : List {a : A.Letter // A.weight a ≤ n} // l.length ≤ n} :=
  ⟨w.val.attachWith (fun a => A.weight a ≤ n) (fun a ha =>
      (letter_weight_le A w.val a ha).trans (le_of_eq w.property)), by
    simpa only [List.length_attachWith, w.property] using length_le_weight A w.val⟩

theorem boundWord_injective (A : Alphabet) (n : ℕ) : Function.Injective (boundWord A n) := by
  intro a b h
  apply Subtype.ext
  have he := congrArg (fun w => w.val.map Subtype.val) h
  simpa only [boundWord, List.attachWith_map_subtype_val] using he

noncomputable instance wordsFintype (A : Alphabet) (n : ℕ) : Fintype (Words A n) := by
  letI : Fintype {l : List {a : A.Letter // A.weight a ≤ n} // l.length ≤ n} :=
    (List.finite_length_le _ n).fintype
  exact Fintype.ofInjective (boundWord A n) (boundWord_injective A n)

noncomputable instance lettersFintype (A : Alphabet) (n : ℕ) : Fintype (Letters A n) := by
  letI : Fintype {a : A.Letter // A.weight a ≤ n} := Fintype.ofFinite _
  exact Fintype.ofInjective (fun a : Letters A n => ⟨a.val, le_of_eq a.property⟩ :
    Letters A n → {a : A.Letter // A.weight a ≤ n}) (by
      intro a b h
      exact Subtype.ext (congrArg (fun x : {a : A.Letter // A.weight a ≤ n} => x.val) h))

instance zeroLettersEmpty (A : Alphabet) : IsEmpty (Letters A 0) where
  false a := by have := A.positive a.val; have := a.property; omega

instance zeroWordsUnique (A : Alphabet) : Unique (Words A 0) where
  default := ⟨[], by simp⟩
  uniq w := by
    apply Subtype.ext
    have h := length_le_weight A w.val
    rw [w.property] at h
    exact List.length_eq_zero_iff.mp (by omega)

/-- The first letter is grouped by its positive weight. This is an equivalence
of actual lists, not a recurrence used to define their cardinality. -/
def firstLetterEquiv (A : Alphabet) (n : ℕ) (hn : 0 < n) :
    Words A n ≃ Σ i : Fin n, Letters A (i.val + 1) × Words A (n - 1 - i.val) where
  toFun w := by
    rcases w with ⟨w, hw⟩
    cases w with
    | nil => simp at hw; omega
    | cons a t =>
      simp only [List.map_cons, List.sum_cons] at hw
      have hp := A.positive a
      refine ⟨⟨A.weight a - 1, by omega⟩, ⟨a, ?_⟩, ⟨t, ?_⟩⟩
      · change A.weight a = (A.weight a - 1) + 1
        omega
      · change (t.map A.weight).sum = n - 1 - (A.weight a - 1)
        omega
  invFun w := ⟨w.2.1.val :: w.2.2.val, by
    simp only [List.map_cons, List.sum_cons, w.2.1.property, w.2.2.property]
    have := w.1.isLt
    omega⟩
  left_inv w := by
    rcases w with ⟨w, hw⟩
    cases w with
    | nil => simp at hw; omega
    | cons a t => rfl
  right_inv w := by
    rcases w with ⟨⟨i, hi⟩, ⟨a, ha⟩, ⟨t, ht⟩⟩
    change A.weight a = i + 1 at ha
    have hi' : i = A.weight a - 1 := by omega
    subst i
    rfl

noncomputable def wordCount (A : Alphabet) (n : ℕ) : ℕ := Fintype.card (Words A n)
noncomputable def letterCount (A : Alphabet) (n : ℕ) : ℕ := Fintype.card (Letters A n)

@[simp] theorem wordCount_zero (A : Alphabet) : wordCount A 0 = 1 := Fintype.card_unique
@[simp] theorem letterCount_zero (A : Alphabet) : letterCount A 0 = 0 := Fintype.card_eq_zero

theorem wordCount_first_letter (A : Alphabet) (n : ℕ) (hn : 0 < n) :
    wordCount A n = ∑ i : Fin n, letterCount A (i.val + 1) * wordCount A (n - 1 - i.val) := by
  unfold wordCount letterCount
  rw [Fintype.card_congr (firstLetterEquiv A n hn), Fintype.card_sigma]
  simp only [Fintype.card_prod]

noncomputable def wordSeries (A : Alphabet) : PowerSeries ℤ :=
  PowerSeries.mk (fun n => (wordCount A n : ℤ))
noncomputable def letterSeries (A : Alphabet) : PowerSeries ℤ :=
  PowerSeries.mk (fun n => (letterCount A n : ℤ))

@[simp] theorem coeff_wordSeries (A : Alphabet) (n : ℕ) :
    coeff n (wordSeries A) = (wordCount A n : ℤ) := by simp [wordSeries]
@[simp] theorem coeff_letterSeries (A : Alphabet) (n : ℕ) :
    coeff n (letterSeries A) = (letterCount A n : ℤ) := by simp [letterSeries]

/-- Exact formal-geometric identity for a locally finite alphabet. -/
theorem wordSeries_identity (A : Alphabet) :
    (1 - letterSeries A) * wordSeries A = 1 := by
  apply PowerSeries.ext
  intro n
  rw [sub_mul, one_mul, map_sub, coeff_mul_eq_convolution, convolution_head_tail]
  simp only [coeff_letterSeries, coeff_wordSeries, letterCount_zero, Nat.cast_zero,
    zero_mul, zero_add, coeff_one]
  by_cases hn : n = 0
  · subst n
    simp
  · rw [if_neg hn]
    have h := congrArg (fun x : ℕ => (x : ℤ))
      (wordCount_first_letter A n (Nat.pos_of_ne_zero hn))
    push_cast at h
    have hh := h.trans (Fin.sum_univ_eq_sum_range
      (fun i => (letterCount A (i + 1) : ℤ) * (wordCount A (n - 1 - i) : ℤ)) n)
    omega

end SubmittedGenus.FiniteArithmetic.LocallyFinite
