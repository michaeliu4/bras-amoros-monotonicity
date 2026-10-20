import Results.Genus.FiniteArithmetic.HighDepthBridge

namespace SubmittedGenus.FiniteArithmetic

/-- A bounded natural-number word can be reindexed without changing a letter. -/
theorem exists_interval_encoding (lo size : ℕ) (l : List ℕ)
    (hl : ∀ a ∈ l, lo ≤ a ∧ a < lo + size) :
    ∃ w : List (Fin size), w.map (fun a => a.val + lo) = l := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons a l ih =>
    have ha := hl a (by simp)
    obtain ⟨w, hw⟩ := ih (fun b hb => hl b (by simp [hb]))
    refine ⟨⟨a - lo, by omega⟩ :: w, ?_⟩
    simp only [List.map_cons, hw]
    congr 1
    omega

/-- Decode the literal no-one source word. -/
def hSourceWord {g : ℕ} (w : HWords g) : List ℕ := w.val.val.map alphabet2345.weight

theorem word_has_hSource {g : ℕ} (l : List ℕ)
    (hl : ∀ a ∈ l, 2 ≤ a ∧ a ≤ 5)
    (hlarge : ∃ a ∈ l, a = 4 ∨ a = 5) (hw : l.sum = g) :
    ∃ s : HWords g, hSourceWord s = l := by
  obtain ⟨w, he⟩ := exists_interval_encoding 2 4 l (by intro a ha; have := hl a ha; omega)
  have he' : w.map alphabet2345.weight = l := he
  let t : ExactWords alphabet2345 g := ⟨w, by rw [he']; exact hw⟩
  have ht : ¬ t ∈ Set.range (smallWordIntoBig g) := by
    apply (not_smallWordIntoBig_iff g t).mpr
    obtain ⟨a, ha, ha45⟩ := hlarge
    rw [← he'] at ha
    obtain ⟨b, hb, hba⟩ := List.mem_map.mp ha
    exact ⟨b, hb, by simpa only [hba] using ha45⟩
  exact ⟨⟨t, ht⟩, he'⟩

/-- The submitted shallow no-one test maps into the original H source. -/
theorem noOne_word_has_hSource (d : KunzData)
    (hd : d.depth = 4 ∨ d.depth = 5) (hno : OriginalSources.noOne d) :
    ∃ s : HWords d.weight, hSourceWord s = d.toList := by
  apply word_has_hSource
  · intro a ha
    obtain ⟨i, rfl⟩ := (KunzData.mem_toList d a).mp ha
    have hp := d.2.property.positive i
    have hn := hno i
    have hb := KunzWord.le_depth d.2.val i
    change d.2.val i ≤ d.depth at hb
    omega
  · have hm := KunzWord.one_lt_multiplicity_of_depth_pos d.2.val
      (by change 0 < d.depth; omega)
    obtain ⟨i, hi⟩ := KunzWord.exists_eq_depth d.2.val hm
    exact ⟨d.depth, (KunzData.mem_toList d d.depth).mpr ⟨i, hi⟩, hd⟩
  · exact d.sum_toList

abbrev NoOneSources (g : ℕ) := {d : KunzData.WeightFibre g //
  (d.val.depth = 4 ∨ d.val.depth = 5) ∧ OriginalSources.noOne d.val}

noncomputable instance noOneSourcesFintype (g : ℕ) : Fintype (NoOneSources g) :=
  Fintype.ofFinite _

noncomputable def noOneToH {g : ℕ} (d : NoOneSources g) : HWords g := by
  have h := noOne_word_has_hSource d.val.val d.property.1 d.property.2
  rw [d.val.property] at h
  exact h.choose

theorem noOneToH_word {g : ℕ} (d : NoOneSources g) :
    hSourceWord (noOneToH d) = d.val.val.toList := by
  unfold noOneToH
  exact (by
    have h := noOne_word_has_hSource d.val.val d.property.1 d.property.2
    rw [d.val.property] at h
    exact h.choose_spec)

theorem noOneToH_injective (g : ℕ) : Function.Injective (@noOneToH g) := by
  intro a b h
  apply Subtype.ext
  apply Subtype.ext
  apply KunzData.toList_injective
  rw [← noOneToH_word a, ← noOneToH_word b, h]

theorem noOne_card_le_h (g : ℕ) :
    Fintype.card (NoOneSources g) ≤ Fintype.card (HWords g) :=
  Fintype.card_le_of_injective _ (noOneToH_injective g)

#print axioms noOne_word_has_hSource
#print axioms noOne_card_le_h

end SubmittedGenus.FiniteArithmetic
