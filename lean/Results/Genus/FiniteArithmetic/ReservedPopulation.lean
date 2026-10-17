import Results.Genus.FiniteArithmetic.NoOneBridge
import Results.Genus.FiniteArithmetic.MarkedFour
import Results.Genus.Injection.LetterCounts
import Mathlib.Data.List.Count

namespace SubmittedGenus.FiniteArithmetic

open OriginalSources PowerSeries

/-- A literal {2,3,4} prefix containing two fours, followed by 1, is exactly
an element of the submitted K language at its physical total weight. -/
theorem finalOne_mem_kSource (l : List ℕ)
    (hl : ∀ a ∈ l, a = 2 ∨ a = 3 ∨ a = 4) (hc : 2 ≤ l.count 4) :
    l ++ [1] ∈ Set.range (encodeFinalOne (n := (l ++ [1]).sum - 1)) := by
  obtain ⟨w, hw⟩ := exists_interval_encoding 2 3 l (by
    intro a ha
    have := hl a ha
    omega)
  have hi : Function.Injective (fun a : Fin 3 => a.val + 2) := by
    intro a b h
    apply Fin.ext
    dsimp at h
    omega
  have hcount : (w.map (fun a => a.val + 2)).count 4 = w.count 2 :=
    List.count_map_of_injective w (fun a => a.val + 2) hi 2
  rw [hw] at hcount
  let v : NWords ((l ++ [1]).sum - 1) := ⟨w, by
    change (w.map (fun a => a.val + 2)).sum = _
    simp [hw], by omega⟩
  refine ⟨v, ?_⟩
  change w.map (fun a => a.val + 2) ++ [1] = l ++ [1]
  rw [hw]

/-- The actual B test supplies every K-language requirement, rather than
assuming a reserved-image population. -/
noncomputable def sourceBToK {g : ℕ} (d : SourceClass g .B) : KWords g := by
  have he := OriginalMaps.B_toList_eq d.property
  have hsum : (d.val.val.prefixList ++ [1]).sum = g := by
    rw [← he, KunzData.sum_toList, d.val.property]
  refine ⟨d.val.val.toList, ?_, ?_⟩
  · simp only [List.sum_append, List.sum_cons, List.sum_nil, add_zero] at hsum
    omega
  · rw [he]
    have h := finalOne_mem_kSource d.val.val.prefixList
      (OriginalMaps.B_prefix d.property) (OriginalMaps.B_prefix_two_fours d.property)
    rwa [hsum] at h

theorem sourceBToK_injective (g : ℕ) : Function.Injective (@sourceBToK g) := by
  intro a b h
  apply Subtype.ext
  apply Subtype.ext
  apply KunzData.toList_injective
  exact congrArg Subtype.val h

/-- Genuine B population bound for the original reservation subtraction. -/
theorem source_B_card_le (g : ℕ) :
    Fintype.card (SourceClass g .B) ≤ Fintype.card (KWords g) :=
  Fintype.card_le_of_injective _ (sourceBToK_injective g)

theorem source_B_coeff_le (g : ℕ) :
    (Fintype.card (SourceClass g .B) : ℤ) ≤ coeff g capacityK := by
  rw [capacityK_source_coeff]
  exact_mod_cast source_B_card_le g

#print axioms source_B_card_le
#print axioms source_B_coeff_le

end SubmittedGenus.FiniteArithmetic
