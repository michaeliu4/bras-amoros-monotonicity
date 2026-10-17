import Results.Genus.Injection.FinalOneExact
import Results.Genus.Injection.ExceptionalCounts

noncomputable section
namespace SubmittedGenus.OriginalPopulations
open OriginalSources FiniteArithmetic
attribute [local instance] Classical.propDecidable

def RawNoOnePred {g : ℕ} (w : RawFourAt g) : Prop := ∀ a ∈ w.val, a ≠ 1
def RawFinalOnePred {g : ℕ} (w : RawFourAt g) : Prop := KunzWord.SoleFinalOne (KunzWord.ofList w.val)
abbrev RawEligibleAt (g : ℕ) := {w : RawFourAt g // ¬ (RawNoOnePred w ∨ RawFinalOnePred w)}
abbrev RawHasOneAt (g : ℕ) := {w : RawFourAt g // ¬ RawNoOnePred w}

lemma raw_exclusions_disjoint (g : ℕ) (w : RawFourAt g)
    (hn : RawNoOnePred w) (hf : RawFinalOnePred w) : False := by
  have h := hf.1
  unfold KunzWord.coord at h
  split_ifs at h with hi
  exact hn _ (List.getElem_mem _) h

lemma rawEligible_card (g : ℕ) : Fintype.card (RawEligibleAt g) =
    rawFourCount g - Fintype.card (NWords g) - Fintype.card (NWords (g - 3)) -
      Fintype.card (NWords (g - 4)) := by
  have hd : Disjoint (@RawNoOnePred g) (@RawFinalOnePred g) :=
    fun f hn hf w hw => raw_exclusions_disjoint g w (hn w hw) (hf w hw)
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_or_disjoint _ _ hd]
  have hn : Fintype.card {w : RawFourAt g // RawNoOnePred w} = Fintype.card (RawNoOneAt g) :=
    Fintype.card_congr (Equiv.refl _)
  have hf : Fintype.card {w : RawFourAt g // RawFinalOnePred w} = Fintype.card (RawFinalOneAt g) :=
    Fintype.card_congr (Equiv.refl _)
  rw [hn, hf, rawNoOne_card, rawFinalOne_card]
  unfold rawFourCount
  omega

lemma rawHasOne_card (g : ℕ) : Fintype.card (RawHasOneAt g) =
    rawFourCount g - Fintype.card (NWords g) := by
  rw [Fintype.card_subtype_compl]
  have hn : Fintype.card {w : RawFourAt g // RawNoOnePred w} = Fintype.card (RawNoOneAt g) :=
    Fintype.card_congr (Equiv.refl _)
  rw [hn, rawNoOne_card]
  rfl

lemma fourIntoRaw_noOne_iff (g : ℕ) (d : GenuineFourAt g) :
    RawNoOnePred (fourIntoRaw g d) ↔ noOne d.val.val := by
  constructor
  · intro h i
    exact h _ ((KunzData.mem_toList _ _).mpr ⟨i, rfl⟩)
  · intro h a ha
    obtain ⟨i, rfl⟩ := (KunzData.mem_toList _ _).mp ha
    exact h i

lemma fourIntoRaw_finalOne_iff (g : ℕ) (d : GenuineFourAt g) :
    RawFinalOnePred (fourIntoRaw g d) ↔ soleOneFinal d.val.val := by
  constructor
  · intro h
    let w : RawFinalOneAt g := ⟨fourIntoRaw g d, h⟩
    have he : (rawFinalOneIntoGenuine g w).val.val.val = d.val.val := by
      apply KunzData.toList_injective
      exact rawIntoFour_toList _ _ _
    exact he ▸ (rawFinalOneIntoGenuine g w).property
  · intro h
    exact (genuineFinalOneIntoRaw g ⟨d, h⟩).property

/-- First residual leaves miss both exact raw exclusions. -/
def firstAtIntoEligible (g : ℕ) (d : SourceClass g .E) (hd : d.val.val.depth = 4) : RawEligibleAt g := by
  let s : FirstResidual := ⟨d.val.val, exceptional_first d.property hd⟩
  let q : GenuineFourAt g := ⟨d.val, (firstIntoFour s).property⟩
  refine ⟨fourIntoRaw g q, ?_⟩
  rintro (hn | hf)
  · have hno := (fourIntoRaw_noOne_iff g q).mp hn
    obtain ⟨i, hi⟩ := s.property.2.1
    exact hno i hi
  · exact s.property.2.2.2.2 ((fourIntoRaw_finalOne_iff g q).mp hf)

/-- Unique-five parents miss the no-one exclusion only. No sole-final-one
subtraction is imposed on this shifted, nonleaf parent population. -/
def uniqueAtIntoHasOne (g : ℕ) (d : SourceClass g .E) (hd : d.val.val.depth ≠ 4)
    (hu : uniqueFive d.val.val) : RawHasOneAt (g - 1) := by
  let s : UniqueFiveResidual := ⟨d.val.val, exceptional_unique d.property hd hu⟩
  let q : GenuineFourAt (g - 1) := ⟨⟨uniqueFiveParent s, by
    have hw := uniqueFiveParent_weight s
    have hg := d.val.property
    change s.val.weight = g at hg
    omega⟩, uniqueFiveParent_multipleFour s⟩
  refine ⟨fourIntoRaw (g - 1) q, ?_⟩
  intro hn
  have hno := (fourIntoRaw_noOne_iff (g - 1) q).mp hn
  obtain ⟨i, hi⟩ := uniqueFiveParent_hasOne s
  exact hno i hi

abbrev RawEnvelopeTargets (g : ℕ) := RawEligibleAt g ⊕ (RawHasOneAt (g - 1) ⊕ CapFiveMass.GenuineFiveAt g)

def exceptionalIntoRawEnvelope (g : ℕ) (d : SourceClass g .E) : RawEnvelopeTargets g :=
  if hd : d.val.val.depth = 4 then .inl (firstAtIntoEligible g d hd)
  else if hu : uniqueFive d.val.val then .inr (.inl (uniqueAtIntoHasOne g d hd hu))
  else .inr (.inr ⟨d.val, exceptional_multiple_five d.property hd hu⟩)

lemma exceptionalIntoRawEnvelope_injective (g : ℕ) : Function.Injective (exceptionalIntoRawEnvelope g) := by
  intro d e he
  by_cases hd : d.val.val.depth = 4
  · by_cases he4 : e.val.val.depth = 4
    · simp only [exceptionalIntoRawEnvelope, dif_pos hd, dif_pos he4, Sum.inl.injEq] at he
      have hh := congrArg (fun z : RawEligibleAt g => z.val.val) he
      exact Subtype.ext (Subtype.ext (KunzData.toList_injective hh))
    · by_cases heu : uniqueFive e.val.val <;>
        simp [exceptionalIntoRawEnvelope, hd, he4, heu] at he
  · by_cases hdu : uniqueFive d.val.val
    · by_cases he4 : e.val.val.depth = 4
      · simp only [exceptionalIntoRawEnvelope, dif_neg hd, dif_pos hdu, dif_pos he4,
          Sum.inr_ne_inl] at he
      · by_cases heu : uniqueFive e.val.val
        · simp only [exceptionalIntoRawEnvelope, dif_neg hd, dif_pos hdu, dif_neg he4,
            dif_pos heu, Sum.inr.injEq, Sum.inl.injEq] at he
          have hh := congrArg (fun z : RawHasOneAt (g - 1) => z.val.val) he
          have hi := uniqueFiveParent_injective (KunzData.toList_injective hh)
          exact Subtype.ext (Subtype.ext (congrArg (fun z : UniqueFiveResidual => z.val) hi))
        · simp only [exceptionalIntoRawEnvelope, dif_neg hd, dif_pos hdu, dif_neg he4,
            dif_neg heu, Sum.inr.injEq, Sum.inl_ne_inr] at he
    · by_cases he4 : e.val.val.depth = 4
      · simp only [exceptionalIntoRawEnvelope, dif_neg hd, dif_neg hdu, dif_pos he4,
          Sum.inr_ne_inl] at he
      · by_cases heu : uniqueFive e.val.val
        · simp only [exceptionalIntoRawEnvelope, dif_neg hd, dif_neg hdu, dif_neg he4,
            dif_pos heu, Sum.inr.injEq, Sum.inr_ne_inl] at he
        · simp only [exceptionalIntoRawEnvelope, dif_neg hd, dif_neg hdu, dif_neg he4,
            dif_neg heu, Sum.inr.injEq] at he
          exact Subtype.ext (congrArg (fun z : CapFiveMass.GenuineFiveAt g => z.val) he)

/-- The exact source envelope before any finite upper bounds are supplied. -/
theorem exceptional_le_raw_envelope (g : ℕ) :
    Fintype.card (SourceClass g .E) ≤
      rawFourCount g - Fintype.card (NWords g) - Fintype.card (NWords (g - 3)) -
        Fintype.card (NWords (g - 4)) +
      (rawFourCount (g - 1) - Fintype.card (NWords (g - 1))) + CapFiveMass.count g := by
  have h := Fintype.card_le_of_injective (exceptionalIntoRawEnvelope g) (exceptionalIntoRawEnvelope_injective g)
  simpa only [RawEnvelopeTargets, Fintype.card_sum, rawEligible_card, rawHasOne_card,
    CapFiveMass.count, Nat.add_assoc] using h

/-- Proposition `cmb:raw-envelope`. The hypotheses are bounds on the actual
complete raw population and genuine B count; the exact exclusions are proved. -/
theorem raw_envelope_upper (g Ug Uprev Vg : ℕ)
    (hU : rawFourCount g ≤ Ug) (hUp : rawFourCount (g - 1) ≤ Uprev)
    (hV : CapFiveMass.count g ≤ Vg) :
    Fintype.card (SourceClass g .E) ≤
      Ug - Fintype.card (NWords g) - Fintype.card (NWords (g - 3)) -
        Fintype.card (NWords (g - 4)) +
      (Uprev - Fintype.card (NWords (g - 1))) + Vg := by
  have h := exceptional_le_raw_envelope g
  omega

end SubmittedGenus.OriginalPopulations
