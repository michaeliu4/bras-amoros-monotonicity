import Results.Genus.Injection.FinalOneShape
import Results.Genus.Injection.FinalOneConstruction

noncomputable section
namespace SubmittedGenus.OriginalPopulations
open OriginalSources FiniteArithmetic
attribute [local instance] Classical.propDecidable

abbrev FourFinalOneAt (g : ℕ) := {d : GenuineFourAt g // soleOneFinal d.val.val}

lemma nWords_weight_pos {g : ℕ} (w : NWords g) : 0 < g := by
  by_contra h
  have hg : g = 0 := by omega
  subst g
  exact isEmptyElim w

def finalOneIntoGenuine (g a : ℕ) (ha : a = 2 ∨ a = 3)
    (w : NWords (g - (a + 1))) : FourFinalOneAt g :=
  ⟨⟨⟨finalOneData w a ha, by
    rw [finalOneData_weight]
    have := nWords_weight_pos w
    omega⟩, finalOneData_multipleFour w a ha⟩, finalOneData_finalOne w a ha⟩

lemma finalOneIntoGenuine_injective (g a : ℕ) (ha : a = 2 ∨ a = 3) :
    Function.Injective (finalOneIntoGenuine g a ha) := by
  intro w v h
  have hd := congrArg (fun d : FourFinalOneAt g => d.val.val.val.toList) h
  change (finalOneData w a ha).toList = (finalOneData v a ha).toList at hd
  rw [finalOneData_toList, finalOneData_toList] at hd
  exact nWord_injective _ (List.append_cancel_right hd)

lemma finalOneIntoGenuine_ne (g : ℕ) (w : NWords (g - 3)) (v : NWords (g - 4)) :
    finalOneIntoGenuine g 2 (Or.inl rfl) w ≠ finalOneIntoGenuine g 3 (Or.inr rfl) v := by
  intro h
  have hd := congrArg (fun d : FourFinalOneAt g => d.val.val.val.toList) h
  change (finalOneData w 2 (Or.inl rfl)).toList = (finalOneData v 3 (Or.inr rfl)).toList at hd
  rw [finalOneData_toList, finalOneData_toList] at hd
  have he := congrArg (fun l : List ℕ => l.dropLast.getLast?) hd
  simp at he

abbrev FinalOneSources (g : ℕ) := NWords (g - 3) ⊕ NWords (g - 4)

def finalOneSourcesIntoGenuine (g : ℕ) : FinalOneSources g → FourFinalOneAt g :=
  Sum.elim (finalOneIntoGenuine g 2 (Or.inl rfl)) (finalOneIntoGenuine g 3 (Or.inr rfl))

lemma finalOneSourcesIntoGenuine_injective (g : ℕ) : Function.Injective (finalOneSourcesIntoGenuine g) := by
  intro d e h
  rcases d with d | d <;> rcases e with e | e
  · exact congrArg Sum.inl (finalOneIntoGenuine_injective g 2 (Or.inl rfl) h)
  · exact (finalOneIntoGenuine_ne g d e h).elim
  · exact (finalOneIntoGenuine_ne g e d h.symm).elim
  · exact congrArg Sum.inr (finalOneIntoGenuine_injective g 3 (Or.inr rfl) h)

lemma finalOneSourcesIntoGenuine_surjective (g : ℕ) : Function.Surjective (finalOneSourcesIntoGenuine g) := by
  intro d
  obtain ⟨a, ha, hw, hb, hc⟩ := genuineFour_final_one_shape ⟨d.val.val.val, d.val.property⟩ d.property
  have hs : d.val.val.val.prefixTwoList.sum + a + 1 = g := by
    have h := (KunzData.sum_toList d.val.val.val).trans d.val.val.property
    rw [hw, List.sum_append] at h
    simpa [Nat.add_assoc] using h
  obtain ⟨w, he⟩ := exists_nWord d.val.val.val.prefixTwoList hb hc
    (show d.val.val.val.prefixTwoList.sum = g - (a + 1) by omega)
  rcases ha with rfl | rfl
  · refine ⟨Sum.inl w, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply KunzData.toList_injective
    change (finalOneData w 2 (Or.inl rfl)).toList = d.val.val.val.toList
    rw [finalOneData_toList, he, hw]
  · refine ⟨Sum.inr w, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply KunzData.toList_injective
    change (finalOneData w 3 (Or.inr rfl)).toList = d.val.val.val.toList
    rw [finalOneData_toList, he, hw]

def finalOneEquivGenuine (g : ℕ) : FinalOneSources g ≃ FourFinalOneAt g :=
  Equiv.ofBijective (finalOneSourcesIntoGenuine g)
    ⟨finalOneSourcesIntoGenuine_injective g, finalOneSourcesIntoGenuine_surjective g⟩

theorem genuineFinalOne_card (g : ℕ) : Fintype.card (FourFinalOneAt g) =
    Fintype.card (NWords (g - 3)) + Fintype.card (NWords (g - 4)) := by
  rw [← Fintype.card_congr (finalOneEquivGenuine g)]
  exact Fintype.card_sum

lemma rawFinalOne_valid (g : ℕ) (w : RawFinalOneAt g) :
    KunzWord.Valid (KunzWord.ofList w.val.val) := by
  obtain ⟨r, p, h⟩ := w.val.property.1
  exact RawGraph.raw_four_sole_final_valid h w.property

def rawFinalOneIntoGenuine (g : ℕ) (w : RawFinalOneAt g) : FourFinalOneAt g :=
  ⟨rawIntoFour g w.val (rawFinalOne_valid g w), w.property⟩

def genuineFinalOneIntoRaw (g : ℕ) (d : FourFinalOneAt g) : RawFinalOneAt g :=
  ⟨fourIntoRaw g d.val, by
    obtain ⟨a, ha, hw, hb, hc⟩ := genuineFour_final_one_shape ⟨d.val.val.val, d.val.property⟩ d.property
    change KunzWord.SoleFinalOne (KunzWord.ofList d.val.val.val.toList)
    rw [hw]
    exact KunzWord.soleFinalOne_two_suffix _ _ (by omega) (fun b hb' => (hb b hb').1)⟩

def rawFinalOneEquivGenuine (g : ℕ) : RawFinalOneAt g ≃ FourFinalOneAt g where
  toFun := rawFinalOneIntoGenuine g
  invFun := genuineFinalOneIntoRaw g
  left_inv w := by
    apply Subtype.ext
    apply Subtype.ext
    exact rawIntoFour_toList _ _ _
  right_inv d := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply KunzData.toList_injective
    exact rawIntoFour_toList _ _ _

/-- The exact raw sole-final-one exclusion has coefficients N_(g-3)+N_(g-4). -/
theorem rawFinalOne_card (g : ℕ) : Fintype.card (RawFinalOneAt g) =
    Fintype.card (NWords (g - 3)) + Fintype.card (NWords (g - 4)) :=
  (Fintype.card_congr (rawFinalOneEquivGenuine g)).trans (genuineFinalOne_card g)

end SubmittedGenus.OriginalPopulations
