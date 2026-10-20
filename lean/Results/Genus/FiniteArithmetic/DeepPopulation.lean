import Results.Genus.FiniteArithmetic.NoOneBridge

namespace SubmittedGenus.FiniteArithmetic

open OriginalSources PowerSeries

/-- Encode the exact ordered D sector in the disjoint original M/H sources. -/
noncomputable def sourceDToMH {g : ℕ} (d : SourceClass g .D) : MSource g ⊕ HWords g := by
  classical
  by_cases hd : 6 ≤ d.val.val.depth
  · exact .inl (deepToM ⟨d.val, hd⟩)
  · have h := ((sector_D_iff d.val.val).mp d.property).2.2.2.2
    exact .inr (noOneToH ⟨d.val, h.resolve_left hd⟩)

def decodeMH {g : ℕ} : MSource g ⊕ HWords g → List ℕ
  | .inl s => mSourceWord s
  | .inr s => hSourceWord s

theorem sourceDToMH_word {g : ℕ} (d : SourceClass g .D) :
    decodeMH (sourceDToMH d) = d.val.val.toList := by
  classical
  unfold sourceDToMH
  split_ifs
  · exact deepToM_word _
  · exact noOneToH_word _

theorem sourceDToMH_injective (g : ℕ) : Function.Injective (@sourceDToMH g) := by
  intro a b h
  apply Subtype.ext
  apply Subtype.ext
  apply KunzData.toList_injective
  rw [← sourceDToMH_word a, ← sourceDToMH_word b, h]

/-- Genuine original D population bound, including its earlier source exclusions. -/
theorem source_D_card_le (g : ℕ) :
    Fintype.card (SourceClass g .D) ≤ Fintype.card (MSource g) + Fintype.card (HWords g) := by
  simpa only [Fintype.card_sum] using Fintype.card_le_of_injective _ (sourceDToMH_injective g)

theorem source_D_coeff_le (g : ℕ) :
    (Fintype.card (SourceClass g .D) : ℤ) ≤ coeff g (capacityM + capacityH) := by
  rw [map_add, capacityM_source_coeff, capacityH_source_coeff]
  exact_mod_cast source_D_card_le g

#print axioms source_D_card_le
#print axioms source_D_coeff_le

end SubmittedGenus.FiniteArithmetic
