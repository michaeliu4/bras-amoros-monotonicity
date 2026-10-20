import Results.Genus.FiniteArithmetic.HighDepthSource
import Results.Genus.FiniteArithmetic.KunzReflection

namespace SubmittedGenus.FiniteArithmetic

open Reflection

/-- Restore the literal physical word represented by a fixed-pivot source. -/
def fixedSourceWord {q g : ℕ} (s : FixedPivotSource q g) : List ℕ :=
  if h : q ≤ g then
    let t : Graded.Product (Blocks (boundedSystem q q))
      (Blocks (boundedSystem (q - 1) (q - 1))) (g - q) := cast (if_pos h) s
    t.2.1.val ++ q :: t.2.2.val
  else []

/-- Any two admissible blocks with their exact total weight inhabit the source. -/
theorem exists_fixedSource {q g : ℕ} (l r : List ℕ)
    (hl : Language (boundedSystem q q).pairAllowed (boundedSystem q q).centerAllowed l)
    (hr : Language (boundedSystem (q - 1) (q - 1)).pairAllowed
      (boundedSystem (q - 1) (q - 1)).centerAllowed r)
    (hw : l.sum + q + r.sum = g) :
    ∃ s : FixedPivotSource q g, fixedSourceWord s = l ++ q :: r := by
  have hq : q ≤ g := by omega
  let t : Graded.Product (Blocks (boundedSystem q q))
      (Blocks (boundedSystem (q - 1) (q - 1))) (g - q) :=
    ⟨⟨l.sum, by omega⟩, ⟨l, hl, rfl⟩, ⟨r, hr, by change r.sum = g - q - l.sum; omega⟩⟩
  let s : FixedPivotSource q g := cast (if_pos hq).symm t
  refine ⟨s, ?_⟩
  have he : cast (if_pos hq) s = t := by
    exact (cast_cast _ _ t).trans (cast_eq _ t)
  change (if h : q ≤ g then
    (cast (if_pos h) s).2.1.val ++ q :: (cast (if_pos h) s).2.2.val else []) = _
  rw [dif_pos hq]
  exact congrArg (fun v => v.2.1.val ++ q :: v.2.2.val) he


/-- Restore the literal word represented by the all-q≥9 source. -/
def tailSourceWord {g : ℕ} (s : OriginalTail.TailSource g) : List ℕ :=
  s.2.2.2.1.val ++ s.2.1.val :: s.2.2.2.2.val

theorem exists_tailSource {q g : ℕ} (hq : 9 ≤ q) (l r : List ℕ)
    (hl : Language OriginalTail.relaxedEightSystem.pairAllowed
      OriginalTail.relaxedEightSystem.centerAllowed l)
    (hr : Language OriginalTail.relaxedEightSystem.pairAllowed
      OriginalTail.relaxedEightSystem.centerAllowed r)
    (hw : l.sum + q + r.sum = g) :
    ∃ s : OriginalTail.TailSource g, tailSourceWord s = l ++ q :: r := by
  let t : Graded.Product (Blocks OriginalTail.relaxedEightSystem)
      (Blocks OriginalTail.relaxedEightSystem) (g - q) :=
    ⟨⟨l.sum, by omega⟩, ⟨l, hl, rfl⟩, ⟨r, hr, by change r.sum = g - q - l.sum; omega⟩⟩
  exact ⟨⟨⟨q, by omega⟩, ⟨q, hq, rfl⟩, t⟩, rfl⟩

/-- All original M summands have a common literal-word decoder. -/
def mSourceWord {g : ℕ} : MSource g → List ℕ
  | .inl s => fixedSourceWord s
  | .inr (.inl s) => fixedSourceWord s
  | .inr (.inr (.inl s)) => fixedSourceWord s
  | .inr (.inr (.inr s)) => tailSourceWord s

/-- Every genuine depth-at-least-six Kunz word occurs in the original M source.
The three finite pivots and the complete unbounded tail are covered. -/
theorem deep_word_has_mSource (d : KunzData) (hd : 6 ≤ d.depth) :
    ∃ s : MSource d.weight, mSourceWord s = d.toList := by
  let x := d.2.val
  let q := x.depth
  let p := x.rightmostMaximum
  let l := leftBlock x p
  let r := rightBlock x p
  have hq : 6 ≤ q := hd
  have hm := KunzWord.one_lt_multiplicity_of_depth_pos x (by omega)
  have hp := KunzWord.rightmostMaximum_spec x hm
  have hb := rightmost_blocks x d.2.property (by omega)
  have hs : d.toList = l ++ q :: r := by
    simpa only [KunzData.toList, l, r, p, q, hp.2.2] using
      list_split_pivot x hp.1 hp.2.1
  have hw : l.sum + q + r.sum = d.weight := by
    have := d.sum_toList
    rw [hs, List.sum_append, List.sum_cons] at this
    omega
  have hfixed : ∃ s : FixedPivotSource q d.weight, fixedSourceWord s = l ++ q :: r :=
    exists_fixedSource l r hb.1 hb.2 hw
  rcases (show q = 6 ∨ q = 7 ∨ q = 8 ∨ 9 ≤ q by omega) with h | h | h | h
  · rw [h] at hfixed hs
    obtain ⟨s, hsw⟩ := hfixed
    exact ⟨.inl s, hsw.trans hs.symm⟩
  · rw [h] at hfixed hs
    obtain ⟨s, hsw⟩ := hfixed
    exact ⟨.inr (.inl s), hsw.trans hs.symm⟩
  · rw [h] at hfixed hs
    obtain ⟨s, hsw⟩ := hfixed
    exact ⟨.inr (.inr (.inl s)), hsw.trans hs.symm⟩
  · obtain ⟨s, hsw⟩ := exists_tailSource h l r
      (bounded_to_relaxed_eight (by omega) hb.1)
      (bounded_to_relaxed_eight (by omega) hb.2) hw
    exact ⟨.inr (.inr (.inr s)), hsw.trans hs.symm⟩

abbrev DeepSources (g : ℕ) := {d : KunzData.WeightFibre g // 6 ≤ d.val.depth}

noncomputable def deepToM {g : ℕ} (d : DeepSources g) : MSource g := by
  have h := deep_word_has_mSource d.val.val d.property
  rw [d.val.property] at h
  exact h.choose

theorem deepToM_word {g : ℕ} (d : DeepSources g) :
    mSourceWord (deepToM d) = d.val.val.toList := by
  unfold deepToM
  exact (by
    have h := deep_word_has_mSource d.val.val d.property
    rw [d.val.property] at h
    exact h.choose_spec)

theorem deepToM_injective (g : ℕ) : Function.Injective (@deepToM g) := by
  intro a b h
  apply Subtype.ext
  apply Subtype.ext
  apply KunzData.toList_injective
  rw [← deepToM_word a, ← deepToM_word b, h]

theorem deep_card_le_m (g : ℕ) : Fintype.card (DeepSources g) ≤ Fintype.card (MSource g) :=
  Fintype.card_le_of_injective _ (deepToM_injective g)

#print axioms deep_word_has_mSource
#print axioms deep_card_le_m

end SubmittedGenus.FiniteArithmetic
