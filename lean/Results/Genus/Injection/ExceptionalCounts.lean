import Results.Genus.Injection.ParentReduction

noncomputable section
namespace SubmittedGenus.OriginalPopulations
open OriginalSources
attribute [local instance] Classical.propDecidable

lemma exceptional_first {d : KunzData} (he : sector d = .E) (hd : d.depth = 4) :
    IsFirstResidual d := by
  rcases (exceptional_iff_three_sectors d).mp he with ⟨hl, ho, hs⟩
  refine ⟨hl, ho, hd, ?_⟩
  rcases hs with h | h | h
  · exact h.2
  · have := h.1; omega
  · have := h.1; omega

lemma exceptional_unique {d : KunzData} (he : sector d = .E)
    (hd : d.depth ≠ 4) (hu : uniqueFive d) : IsUniqueFiveResidual d := by
  rcases (exceptional_iff_three_sectors d).mp he with ⟨hl, ho, hs⟩
  refine ⟨hl, ho, ?_⟩
  rcases hs with h | h | h
  · exact (hd h.1).elim
  · exact h
  · rcases hu with ⟨p, hp, huni⟩
    rcases h.2 with ⟨q, r, hqr, hq, hr⟩
    exact (hqr ((huni q hq).trans (huni r hr).symm)).elim

lemma exceptional_multiple_five {d : KunzData} (he : sector d = .E)
    (hd : d.depth ≠ 4) (hu : ¬ uniqueFive d) : CapFiveMass.HasMultipleFive d := by
  rcases (exceptional_iff_three_sectors d).mp he with ⟨hl, ho, hs⟩
  rcases hs with h | h | h
  · exact (hd h.1).elim
  · exact (hu h.2.1).elim
  · exact ⟨(KunzWord.depth_le_iff _).mp (le_of_eq h.1), h.2⟩

/-- The actual three genus fibers in the parent-reduction coefficient bound. -/
abbrev ThreeCountTargets (g : ℕ) :=
  GenuineFourAt g ⊕ (GenuineFourAt (g - 1) ⊕ CapFiveMass.GenuineFiveAt g)

def exceptionalIntoCounts (g : ℕ) (d : SourceClass g .E) : ThreeCountTargets g :=
  if hd : d.val.val.depth = 4 then
    Sum.inl ⟨d.val, (firstIntoFour ⟨d.val.val, exceptional_first d.property hd⟩).property⟩
  else if hu : uniqueFive d.val.val then
    let e : UniqueFiveResidual := ⟨d.val.val, exceptional_unique d.property hd hu⟩
    Sum.inr (Sum.inl ⟨⟨uniqueFiveParent e, by
      have hw := uniqueFiveParent_weight e
      have hg := d.val.property
      change e.val.weight = g at hg
      omega⟩, uniqueFiveParent_multipleFour e⟩)
  else Sum.inr (Sum.inr ⟨d.val, exceptional_multiple_five d.property hd hu⟩)

lemma exceptionalIntoCounts_injective (g : ℕ) : Function.Injective (exceptionalIntoCounts g) := by
  intro d e he
  by_cases hd : d.val.val.depth = 4
  · by_cases he4 : e.val.val.depth = 4
    · simp only [exceptionalIntoCounts, dif_pos hd, dif_pos he4, Sum.inl.injEq] at he
      exact Subtype.ext (congrArg (fun z : GenuineFourAt g => z.val) he)
    · by_cases heu : uniqueFive e.val.val <;>
        simp [exceptionalIntoCounts, hd, he4, heu] at he
  · by_cases hdu : uniqueFive d.val.val
    · by_cases he4 : e.val.val.depth = 4
      · simp only [exceptionalIntoCounts, dif_neg hd, dif_pos hdu, dif_pos he4,
          Sum.inr_ne_inl] at he
      · by_cases heu : uniqueFive e.val.val
        · simp only [exceptionalIntoCounts, dif_neg hd, dif_pos hdu, dif_neg he4,
            dif_pos heu, Sum.inr.injEq, Sum.inl.injEq] at he
          have hi := uniqueFiveParent_injective
            (congrArg (fun z : GenuineFourAt (g - 1) => z.val.val) he)
          exact Subtype.ext (Subtype.ext (congrArg (fun z : UniqueFiveResidual => z.val) hi))
        · simp only [exceptionalIntoCounts, dif_neg hd, dif_pos hdu, dif_neg he4,
            dif_neg heu, Sum.inr.injEq, Sum.inl_ne_inr] at he
    · by_cases he4 : e.val.val.depth = 4
      · simp only [exceptionalIntoCounts, dif_neg hd, dif_neg hdu, dif_pos he4,
          Sum.inr_ne_inl] at he
      · by_cases heu : uniqueFive e.val.val
        · simp only [exceptionalIntoCounts, dif_neg hd, dif_neg hdu, dif_neg he4,
            dif_pos heu, Sum.inr.injEq, Sum.inr_ne_inl] at he
        · simp only [exceptionalIntoCounts, dif_neg hd, dif_neg hdu, dif_neg he4,
            dif_neg heu, Sum.inr.injEq] at he
          exact Subtype.ext (congrArg (fun z : CapFiveMass.GenuineFiveAt g => z.val) he)

/-- Lemma `cmb:parent-reduction`, at the level of the genuine finite counts. -/
theorem exceptional_count_le (g : ℕ) :
    Fintype.card (SourceClass g .E) ≤ countFour g + countFour (g - 1) + CapFiveMass.count g := by
  have h := Fintype.card_le_of_injective (exceptionalIntoCounts g) (exceptionalIntoCounts_injective g)
  simpa only [ThreeCountTargets, Fintype.card_sum, countFour, CapFiveMass.count, Nat.add_assoc] using h

end SubmittedGenus.OriginalPopulations
