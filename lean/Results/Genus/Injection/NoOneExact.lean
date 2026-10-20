import Results.Genus.Injection.RawExclusions
import Results.Genus.Injection.ParentReduction
import Results.Genus.FiniteArithmetic.NoOneBridge
import Results.Genus.FiniteArithmetic.MarkedFour

noncomputable section
namespace SubmittedGenus.OriginalPopulations
open OriginalSources FiniteArithmetic
attribute [local instance] Classical.propDecidable

/-- The actual no-one exclusion from genuine A at genus g. -/
abbrev FourNoOneAt (g : ℕ) := {d : GenuineFourAt g // noOne d.val.val}

/-- Physical decoding of the original N language. -/
def nWord {g : ℕ} (w : NWords g) : List ℕ := w.val.map alphabet234.weight

lemma nWord_bounds {g : ℕ} (w : NWords g) : ∀ a ∈ nWord w, 2 ≤ a ∧ a ≤ 4 := by
  intro a ha
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
  change 2 ≤ i.val + 2 ∧ i.val + 2 ≤ 4
  have hi : i.val < 3 := i.isLt
  omega

lemma nWord_sum {g : ℕ} (w : NWords g) : (nWord w).sum = g := w.property.1

lemma nWord_count_four {g : ℕ} (w : NWords g) : 2 ≤ (nWord w).count 4 := by
  have hi : Function.Injective alphabet234.weight := by
    intro a b h
    apply Fin.ext
    change a.val + 2 = b.val + 2 at h
    omega
  have h := List.count_map_of_injective w.val alphabet234.weight hi (2 : Fin 3)
  change (nWord w).count 4 = w.val.count 2 at h
  rw [h]
  exact w.property.2

lemma nWord_injective (g : ℕ) : Function.Injective (@nWord g) := by
  intro a b h
  apply Subtype.ext
  apply List.map_injective_iff.mpr _ h
  intro a b h
  apply Fin.ext
  change a.val + 2 = b.val + 2 at h
  omega

lemma exists_nWord {g : ℕ} (w : List ℕ)
    (hb : ∀ a ∈ w, 2 ≤ a ∧ a ≤ 4) (hc : 2 ≤ w.count 4) (hw : w.sum = g) :
    ∃ s : NWords g, nWord s = w := by
  obtain ⟨v, hv⟩ := exists_interval_encoding 2 3 w (by intro a ha; have := hb a ha; omega)
  have he : v.map alphabet234.weight = w := hv
  refine ⟨⟨v, ?_, ?_⟩, he⟩
  · rw [he]; exact hw
  · have hinj : Function.Injective alphabet234.weight := by
      intro a b h
      apply Fin.ext
      change a.val + 2 = b.val + 2 at h
      omega
    have h := List.count_map_of_injective v alphabet234.weight hinj (2 : Fin 3)
    change (v.map alphabet234.weight).count 4 = v.count 2 at h
    rw [he] at h
    omega

def nData {g : ℕ} (w : NWords g) : KunzData :=
  ⟨⟨(nWord w).length + 1, by omega⟩,
    ⟨KunzWord.ofList (nWord w), KunzWord.valid_of_two_to_four
      (fun i => nWord_bounds w _ (List.getElem_mem _))⟩⟩

@[simp] lemma nData_toList {g : ℕ} (w : NWords g) : (nData w).toList = nWord w :=
  KunzWord.ofFn_ofList _

lemma nData_multipleFour {g : ℕ} (w : NWords g) : HasMultipleFour (nData w) := by
  refine ⟨fun i => (nWord_bounds w _ (List.getElem_mem _)).2, ?_⟩
  apply (KunzData.twoLetters_iff_count _ _).mpr
  rw [nData_toList]
  exact nWord_count_four w

lemma nData_noOne {g : ℕ} (w : NWords g) : noOne (nData w) := by
  intro i
  change Fin ((nWord w).length + 1 - 1) at i
  have h := (nWord_bounds w _ (List.getElem_mem (l := nWord w) (n := i.val)
    (by simpa using i.isLt))).1
  change (nWord w)[i.val] ≠ 1
  omega

lemma nData_weight {g : ℕ} (w : NWords g) : (nData w).weight = g := by
  rw [← KunzData.sum_toList, nData_toList, nWord_sum]

def nIntoFourNoOne (g : ℕ) (w : NWords g) : FourNoOneAt g :=
  ⟨⟨⟨nData w, nData_weight w⟩, nData_multipleFour w⟩, nData_noOne w⟩

lemma nIntoFourNoOne_injective (g : ℕ) : Function.Injective (nIntoFourNoOne g) := by
  intro a b h
  apply nWord_injective g
  have hd := congrArg (fun z : FourNoOneAt g => z.val.val.val.toList) h
  simpa only [nIntoFourNoOne, nData_toList] using hd

lemma nIntoFourNoOne_surjective (g : ℕ) : Function.Surjective (nIntoFourNoOne g) := by
  intro d
  have hb : ∀ a ∈ d.val.val.val.toList, 2 ≤ a ∧ a ≤ 4 := by
    intro a ha
    obtain ⟨i, rfl⟩ := (KunzData.mem_toList _ _).mp ha
    have hp := d.val.val.val.2.property.positive i
    have hn := d.property i
    have hu := d.val.property.1 i
    omega
  obtain ⟨w, hw⟩ := exists_nWord d.val.val.val.toList hb
    ((KunzData.twoLetters_iff_count _ _).mp d.val.property.2)
    ((KunzData.sum_toList _).trans d.val.val.property)
  refine ⟨w, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply KunzData.toList_injective
  exact (nData_toList w).trans hw

/-- A bijection to the literal N source; all its words are genuine. -/
def noOneEquivN (g : ℕ) : NWords g ≃ FourNoOneAt g :=
  Equiv.ofBijective (nIntoFourNoOne g) ⟨nIntoFourNoOne_injective g, nIntoFourNoOne_surjective g⟩

theorem fourNoOne_card (g : ℕ) : Fintype.card (FourNoOneAt g) = Fintype.card (NWords g) :=
  (Fintype.card_congr (noOneEquivN g)).symm

end SubmittedGenus.OriginalPopulations
