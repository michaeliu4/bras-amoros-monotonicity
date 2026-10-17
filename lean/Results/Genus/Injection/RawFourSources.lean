import Results.Genus.Injection.NoOneExact

noncomputable section
namespace SubmittedGenus.OriginalPopulations
open OriginalSources FiniteArithmetic
attribute [local instance] Classical.propDecidable

/-- The raw relaxation is a predicate on literal words. Pivot labels are
existential because the proved two-rightmost-pivot uniqueness fixes them. -/
def RawFourList (w : List ℕ) : Prop :=
  ∃ r p, RawGraph.RawAdmissible r p 4 (KunzWord.ofList w)

abbrev RawFourAt (g : ℕ) := {w : List ℕ // RawFourList w ∧ w.sum = g}

lemma rawFourList_bounds {w : List ℕ} (h : RawFourList w) :
    ∀ a ∈ w, 1 ≤ a ∧ a ≤ 4 := by
  obtain ⟨r, p, h⟩ := h
  intro a ha
  rw [← KunzWord.ofFn_ofList w] at ha
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
  exact RawGraph.raw_coordinate_bounds h i

abbrev alphabet1234 : WeightedAlphabet where
  size := 4
  weight a := a.val + 1
  positive _ := by omega

instance (g : ℕ) : Fintype (RawFourAt g) := by
  letI := exactWordsFintype alphabet1234 g
  have hf := Set.finite_range (fun w : ExactWords alphabet1234 g => w.val.map alphabet1234.weight)
  exact (hf.subset (by
    intro w hw
    obtain ⟨v, hv⟩ := exists_interval_encoding 1 4 w
      (by intro a ha; have := rawFourList_bounds hw.1 a ha; omega)
    refine ⟨⟨v, ?_⟩, hv⟩
    change (v.map (fun a => a.val + 1)).sum = g
    rw [hv]
    exact hw.2)).fintype

def rawFourCount (g : ℕ) : ℕ := Fintype.card (RawFourAt g)

lemma genuineFour_raw_list (d : GenuineFour) : RawFourList d.val.toList := by
  obtain ⟨r, p, h⟩ := RawGraph.exists_raw_of_kunz_two_maxima (Or.inl rfl)
    d.val.2.property d.property.1 d.property.2
  have hm : d.val.toList.length + 1 = d.val.1.val := by
    rw [KunzData.length_toList]
    have := d.val.1.property
    omega
  let idx : Fin (d.val.toList.length + 1 - 1) → Fin (d.val.1.val - 1) :=
    fun i => ⟨i.val, by have := i.isLt; omega⟩
  have hv (i : Fin (d.val.toList.length + 1 - 1)) :
      KunzWord.ofList d.val.toList i = d.val.2.val (idx i) := by
    change (List.ofFn d.val.2.val)[i.val] = d.val.2.val (idx i)
    rw [List.getElem_ofFn]
  refine ⟨r, p, ?_, ?_, ?_, ?_⟩
  · simpa only [hm] using h.1
  · intro i
    change (if RawGraph.IsPivot r p i then KunzWord.ofList d.val.toList i = 4
      else 1 ≤ KunzWord.ofList d.val.toList i ∧ KunzWord.ofList d.val.toList i ≤
        if RawGraph.physical i < r then 4 else 4 - 1)
    rw [hv]
    exact h.2.1 (idx i)
  · intro i j hij
    rw [hv, hv]
    exact h.2.2.1 (idx i) (idx j) hij
  · intro i j hij
    rw [hv, hv]
    apply h.2.2.2 (idx i) (idx j)
    change i.val + 1 + (j.val + 1) = d.val.1.val + r ∨
      i.val + 1 + (j.val + 1) = d.val.1.val + p
    change i.val + 1 + (j.val + 1) = d.val.toList.length + 1 + r ∨
      i.val + 1 + (j.val + 1) = d.val.toList.length + 1 + p at hij
    omega

def fourIntoRaw (g : ℕ) (d : GenuineFourAt g) : RawFourAt g :=
  ⟨d.val.val.toList, genuineFour_raw_list ⟨d.val.val, d.property⟩,
    (KunzData.sum_toList _).trans d.val.property⟩

lemma fourIntoRaw_injective (g : ℕ) : Function.Injective (fourIntoRaw g) := by
  intro d e h
  exact Subtype.ext (Subtype.ext (KunzData.toList_injective (congrArg Subtype.val h)))

/-- Interpret a raw word as genuine only after its full validity is proved. -/
def rawIntoFour (g : ℕ) (w : RawFourAt g) (hv : KunzWord.Valid (KunzWord.ofList w.val)) :
    GenuineFourAt g := by
  let d : KunzData := ⟨⟨w.val.length + 1, by omega⟩, ⟨KunzWord.ofList w.val, hv⟩⟩
  have hd : d.toList = w.val := KunzWord.ofFn_ofList _
  refine ⟨⟨d, ?_⟩, ?_⟩
  · rw [← KunzData.sum_toList, hd]
    exact w.property.2
  · obtain ⟨r, p, h⟩ := w.property.1
    exact ⟨fun i => (RawGraph.raw_coordinate_bounds h i).2, RawGraph.raw_has_two_maxima h⟩

@[simp] lemma rawIntoFour_toList (g : ℕ) (w : RawFourAt g)
    (hv : KunzWord.Valid (KunzWord.ofList w.val)) : (rawIntoFour g w hv).val.val.toList = w.val :=
  KunzWord.ofFn_ofList _

abbrev RawNoOneAt (g : ℕ) := {w : RawFourAt g // ∀ a ∈ w.val, a ≠ 1}
abbrev RawFinalOneAt (g : ℕ) := {w : RawFourAt g // KunzWord.SoleFinalOne (KunzWord.ofList w.val)}

lemma rawNoOne_valid (g : ℕ) (w : RawNoOneAt g) :
    KunzWord.Valid (KunzWord.ofList w.val.val) := by
  apply KunzWord.valid_of_two_to_four
  intro i
  have hb := rawFourList_bounds w.val.property.1 _
    (List.getElem_mem (l := w.val.val) (n := i.val) (by simpa using i.isLt))
  have hn := w.property _
    (List.getElem_mem (l := w.val.val) (n := i.val) (by simpa using i.isLt))
  change 2 ≤ w.val.val[i.val] ∧ w.val.val[i.val] ≤ 4
  omega

def rawNoOneIntoGenuine (g : ℕ) (w : RawNoOneAt g) : FourNoOneAt g :=
  ⟨rawIntoFour g w.val (rawNoOne_valid g w), by
    intro i
    exact w.property _ (List.getElem_mem _)⟩

def genuineNoOneIntoRaw (g : ℕ) (d : FourNoOneAt g) : RawNoOneAt g :=
  ⟨fourIntoRaw g d.val, by
    intro a ha
    obtain ⟨i, rfl⟩ := (KunzData.mem_toList d.val.val.val a).mp ha
    exact d.property i⟩

/-- Raw and genuine no-one exclusions coincide as actual finite populations. -/
def rawNoOneEquivGenuine (g : ℕ) : RawNoOneAt g ≃ FourNoOneAt g where
  toFun := rawNoOneIntoGenuine g
  invFun := genuineNoOneIntoRaw g
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

/-- The complete raw no-one exclusion has exactly coefficient N_g. -/
theorem rawNoOne_card (g : ℕ) : Fintype.card (RawNoOneAt g) = Fintype.card (NWords g) :=
  (Fintype.card_congr (rawNoOneEquivGenuine g)).trans (fourNoOne_card g)

end SubmittedGenus.OriginalPopulations
