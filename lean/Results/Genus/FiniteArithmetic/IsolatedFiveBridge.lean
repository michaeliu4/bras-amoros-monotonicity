import Results.Genus.FiniteArithmetic.IsolatedFiveSource
import Results.Genus.FiniteArithmetic.KunzReflection

/-!
# The original isolated-five population is bounded by the actual J source

The map starts with the exact ordered `I` source class from the submitted
manuscript. Kunz inequalities imply both reflection languages. The left
block is nonempty and cannot contain `1`; exclusion of the earlier `D`
class therefore puts a `1` in the right block. Concatenation around the
literal pivot `5` reconstructs the complete original Kunz word.
-/

namespace SubmittedGenus.FiniteArithmetic.IsolatedFive

open Reflection OriginalSources PowerSeries

/-- A threshold-five, cap-three block has no letter `1`, including at a
central self-pair. -/
theorem left_language_noOne {w : List ℕ}
    (hw : Language leftSystem.pairAllowed leftSystem.centerAllowed w) : 1 ∉ w := by
  have hletters : ∀ a ∈ w, 2 ≤ a := hw.forall_letters (by
    intro a b hab
    change 1 ≤ a ∧ a ≤ 3 ∧ 1 ≤ b ∧ b ≤ 3 ∧ 5 ≤ a + b at hab
    omega) (by
    intro a ha
    change 1 ≤ a ∧ a ≤ 3 ∧ 5 ≤ 2 * a at ha
    omega)
  intro hone
  have := hletters 1 hone
  omega

/-- Forget only the source constraints, retaining every physical letter. -/
def decodeJPair (n : ℕ) (s : Graded.Product LeftNonemptyWords RightMarkedWords n) : List ℕ :=
  s.2.1.val.val ++ 5 :: s.2.2.val.val

def decodeJ (g : ℕ) (a : JSource g) : List ℕ :=
  if hg : 5 ≤ g then
    let s : Graded.Product LeftNonemptyWords RightMarkedWords (g - 5) :=
      cast (by simp only [JSource, Graded.Shift, if_pos hg]) a
    decodeJPair (g - 5) s
  else PEmpty.elim (cast (by simp only [JSource, Graded.Shift, if_neg hg]) a : PEmpty)

/-- Store a pair of actual admissible lists at its exact total weight. -/
def packJ {g : ℕ} (l r : List ℕ)
    (hl : Language leftSystem.pairAllowed leftSystem.centerAllowed l)
    (hr : Language rightSystem.pairAllowed rightSystem.centerAllowed r)
    (hne : l ≠ []) (hone : 1 ∈ r) (hw : l.sum + 5 + r.sum = g) : JSource g := by
  have hg : 5 ≤ g := by omega
  let code : Graded.Product LeftNonemptyWords RightMarkedWords (g - 5) :=
    ⟨⟨l.sum, by omega⟩, ⟨⟨l, hl, rfl⟩, hne⟩,
      ⟨⟨r, hr, by change r.sum = g - 5 - l.sum; omega⟩,
        (rightMarked_iff_hasOne _ _).mpr hone⟩⟩
  exact cast (by simp only [JSource, Graded.Shift, if_pos hg]) code

@[simp] theorem decodeJ_packJ {g : ℕ} (l r : List ℕ)
    (hl : Language leftSystem.pairAllowed leftSystem.centerAllowed l)
    (hr : Language rightSystem.pairAllowed rightSystem.centerAllowed r)
    (hne : l ≠ []) (hone : 1 ∈ r) (hw : l.sum + 5 + r.sum = g) :
    decodeJ g (packJ l r hl hr hne hone hw) = l ++ 5 :: r := by
  have hg : 5 ≤ g := by omega
  simp only [decodeJ, packJ, dif_pos hg, cast_cast, cast_eq]
  rfl

/-- The literal isolated pivot yields precisely the two original bounded
reflection blocks, and exclusion of `D` supplies the right-hand `1`. -/
theorem source_I_reflection_split (d : KunzData) (hI : sector d = .I) :
    ∃ l r : List ℕ,
      Language leftSystem.pairAllowed leftSystem.centerAllowed l ∧
      Language rightSystem.pairAllowed rightSystem.centerAllowed r ∧
      l ≠ [] ∧ 1 ∈ r ∧ d.toList = l ++ 5 :: r := by
  rcases (sector_I_iff d).mp hI with ⟨_, _, _, _, hD, p, hp0, hp5, hother⟩
  have hpm : p.val + 1 < d.1.val := by have := p.isLt; omega
  have hpcoord : KunzWord.coord d.2.val (p.val + 1) = 5 := by
    rw [KunzWord.coord_index, hp5]
  have hcap : ∀ i, 0 < i → i < d.1.val → i ≠ p.val + 1 →
      KunzWord.coord d.2.val i ≤ 3 := by
    intro i hi him hne
    let j : Fin (d.1.val - 1) := ⟨i - 1, by omega⟩
    have hj : j.val + 1 = i := by dsimp [j]; omega
    rw [← hj, KunzWord.coord_index]
    apply hother j
    intro he
    have := congrArg Fin.val he
    dsimp [j] at this
    omega
  let l := leftBlock d.2.val (p.val + 1)
  let r := rightBlock d.2.val (p.val + 1)
  have hl : Language leftSystem.pairAllowed leftSystem.centerAllowed l := by
    have h := leftBlock_language (cap := 3) d.2.val d.2.property
      (by omega : 0 < p.val + 1) hpm (fun i hi hip => hcap i hi (by omega) (by omega))
    simpa only [hpcoord] using h
  have hr : Language rightSystem.pairAllowed rightSystem.centerAllowed r := by
    have h := rightBlock_language (cap := 3) d.2.val d.2.property
      (by omega : 0 < p.val + 1) hpm (fun i hpi him => hcap i (by omega) him (by omega))
    simpa only [hpcoord] using h
  have hne : l ≠ [] := by
    intro he
    have hh := congrArg List.length he
    simp only [l, leftBlock, List.length_ofFn, List.length_nil] at hh
    omega
  have hsplit : d.toList = l ++ 5 :: r := by
    simpa only [KunzData.toList, hpcoord] using
      list_split_pivot d.2.val (by omega : 0 < p.val + 1) hpm
  have hdepth : d.depth = 5 := isolatedAnyFive_depth d ⟨p, hp5, hother⟩
  have hnotno : ¬ noOne d := fun hno => hD (Or.inr ⟨Or.inr hdepth, hno⟩)
  have hone : 1 ∈ d.toList := by
    rw [KunzData.mem_toList]
    simpa only [noOne, not_forall, not_not] using hnotno
  have hright : 1 ∈ r := by
    rw [hsplit] at hone
    have hleft := left_language_noOne hl
    simpa only [List.mem_append, List.mem_cons, hleft, false_or,
      show ¬ (1 : ℕ) = 5 by decide] using hone
  exact ⟨l, r, hl, hr, hne, hright, hsplit⟩

/-- Every actual genus-g isolated-five source has an exact J code whose
unconstrained decoding recovers that original source word. -/
theorem source_I_has_JCode (g : ℕ) (s : SourceClass g .I) :
    ∃ a : JSource g, decodeJ g a = s.val.val.toList := by
  obtain ⟨l, r, hl, hr, hne, hone, hs⟩ := source_I_reflection_split s.val.val s.property
  have hw : l.sum + 5 + r.sum = g := by
    have ht := congrArg List.sum hs
    rw [KunzData.sum_toList, List.sum_append, List.sum_cons] at ht
    have hg := s.val.property
    omega
  refine ⟨packJ l r hl hr hne hone hw, ?_⟩
  rw [decodeJ_packJ, hs]

noncomputable def sourceIToJ (g : ℕ) (s : SourceClass g .I) : JSource g :=
  Classical.choose (source_I_has_JCode g s)

@[simp] theorem decodeJ_sourceIToJ (g : ℕ) (s : SourceClass g .I) :
    decodeJ g (sourceIToJ g s) = s.val.val.toList :=
  Classical.choose_spec (source_I_has_JCode g s)

/-- No pivot-position factor is introduced: the ordered blocks already
reconstruct every coordinate, hence the original semigroup. -/
theorem sourceIToJ_injective (g : ℕ) : Function.Injective (sourceIToJ g) := by
  intro a b he
  have hl := congrArg (decodeJ g) he
  rw [decodeJ_sourceIToJ, decodeJ_sourceIToJ] at hl
  apply Subtype.ext
  apply Subtype.ext
  exact KunzData.toList_injective hl

/-- All-genus cardinal bound for the exact original I class. -/
theorem source_I_card_le (g : ℕ) :
    Fintype.card (SourceClass g .I) ≤ Fintype.card (JSource g) :=
  Fintype.card_le_of_injective _ (sourceIToJ_injective g)

/-- The isolated-five contribution in the manuscript majorant, with no
additional hypotheses about source sizes or coefficients. -/
theorem source_I_coeff_le (g : ℕ) :
    (Fintype.card (SourceClass g .I) : ℤ) ≤ coeff g capacityJ := by
  rw [capacityJ_source_coeff]
  exact_mod_cast source_I_card_le g

#print axioms source_I_reflection_split
#print axioms sourceIToJ_injective
#print axioms source_I_card_le
#print axioms source_I_coeff_le

end SubmittedGenus.FiniteArithmetic.IsolatedFive
