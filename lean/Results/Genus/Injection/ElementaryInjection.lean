import Results.Genus.Injection.InitialFiveMap
import Results.Genus.Injection.BinaryTargets

namespace SubmittedGenus.OriginalMaps

open OriginalSources Function

@[simp] theorem TTarget_lastLetter (s : TSource) : (TTarget s).lastLetter = 3 := by
  exact KunzWord.coord_initialFiveTransform_last s.val.2.val

theorem TTarget_low (s : TSource) : (TTarget s).depth ≤ 3 := by
  apply (KunzWord.depth_le_iff _).mpr
  exact KunzWord.initialFiveTransform_bounded ((sector_T_iff _).mp s.property).2.2.2.2

theorem TMap_low (g : ℕ) (s : SourceClass g .T) : (TMap g s).val.kunzDepth ≤ 3 := by
  change (TTarget ⟨s.val.val, s.property⟩).toSemigroup.kunzDepth ≤ 3
  rw [NumericalSemigroup.kunzDepth_toSemigroup]
  exact TTarget_low _

theorem PMap_ne_TMap (g : ℕ) (x : SourceClass g .P) (y : SourceClass g .T) :
    PMap g x ≠ TMap g y := by
  intro h
  have hp := PMap_high g x
  have ht := TMap_low g y
  rw [h] at hp
  omega

theorem LMap_ne_TMap (g : ℕ) (x : SourceClass g .L) (y : SourceClass g .T) :
    LMap g x ≠ TMap g y := by
  intro h
  have hdata := KunzData.toSemigroup_injective (congrArg Subtype.val h)
  have hlast := congrArg KunzData.lastLetter hdata
  change (lowAppend 1 (by omega) (by omega)
    ⟨x.val.val, (sector_L_iff x.val.val).mp x.property⟩).lastLetter =
      (TTarget ⟨y.val.val, y.property⟩).lastLetter at hlast
  rw [lowAppend_lastLetter, TTarget_lastLetter] at hlast
  omega

theorem CMap_ne_TMap (g : ℕ) (x : SourceClass g .C) (y : SourceClass g .T) :
    CMap g x ≠ TMap g y := by
  intro h
  have hdata := KunzData.toSemigroup_injective (congrArg Subtype.val h)
  have hlast := congrArg KunzData.lastLetter hdata
  change (lowAppend 2 (by omega) (by omega)
    (CParent ⟨x.val.val, x.property⟩)).lastLetter =
      (TTarget ⟨y.val.val, y.property⟩).lastLetter at hlast
  rw [lowAppend_lastLetter, TTarget_lastLetter] at hlast
  omega

theorem TMap_ne_BMap (g : ℕ) (x : SourceClass g .T) (y : SourceClass g .B) :
    TMap g x ≠ BMap g y := by
  intro h
  have hdata := KunzData.toSemigroup_injective (congrArg Subtype.val h)
  have hlast := congrArg KunzData.lastLetter hdata
  change (TTarget ⟨x.val.val, x.property⟩).lastLetter = (BTarget y.val.val).lastLetter at hlast
  rw [TTarget_lastLetter, BTarget_lastLetter] at hlast
  omega

def LEmbedding (g : ℕ) : SourceClass g .L ↪ NumericalSemigroup.GenusFibre (g + 1) :=
  ⟨LMap g, LMap_injective g⟩

noncomputable def PEmbedding (g : ℕ) : SourceClass g .P ↪ NumericalSemigroup.GenusFibre (g + 1) :=
  ⟨PMap g, PMap_injective g⟩

noncomputable def CEmbedding (g : ℕ) : SourceClass g .C ↪ NumericalSemigroup.GenusFibre (g + 1) :=
  ⟨CMap g, CMap_injective g⟩

def TEmbedding (g : ℕ) : SourceClass g .T ↪ NumericalSemigroup.GenusFibre (g + 1) :=
  ⟨TMap g, TMap_injective g⟩

def BEmbedding (g : ℕ) : SourceClass g .B ↪ NumericalSemigroup.GenusFibre (g + 1) :=
  ⟨BMap g, BMap_injective g⟩

noncomputable def TBEmbedding (g : ℕ) :
    SourceClass g .T ⊕ SourceClass g .B ↪ NumericalSemigroup.GenusFibre (g + 1) :=
  Allocation.joinEmbeddings (TEmbedding g) (BEmbedding g)
    (fun b t h => TMap_ne_BMap g t b h.symm)

noncomputable def CTBEmbedding (g : ℕ) :
    SourceClass g .C ⊕ (SourceClass g .T ⊕ SourceClass g .B) ↪
      NumericalSemigroup.GenusFibre (g + 1) :=
  Allocation.joinEmbeddings (CEmbedding g) (TBEmbedding g) (by
    rintro (t | b) c h
    · exact CMap_ne_TMap g c t h.symm
    · exact CMap_ne_BMap g c b h.symm)

noncomputable def PCTBEmbedding (g : ℕ) :
    SourceClass g .P ⊕ (SourceClass g .C ⊕ (SourceClass g .T ⊕ SourceClass g .B)) ↪
      NumericalSemigroup.GenusFibre (g + 1) :=
  Allocation.joinEmbeddings (PEmbedding g) (CTBEmbedding g) (by
    rintro (c | t | b) p h
    · exact PMap_ne_CMap g p c h.symm
    · exact PMap_ne_TMap g p t h.symm
    · exact PMap_ne_BMap g p b h.symm)

/-- The five literal elementary maps, assembled using their ten proved
pairwise-disjointness cases. No binary capacity premise is used here. -/
noncomputable def elementaryEmbedding (g : ℕ) :
    SourceClass g .L ⊕ (SourceClass g .P ⊕
      (SourceClass g .C ⊕ (SourceClass g .T ⊕ SourceClass g .B))) ↪
      NumericalSemigroup.GenusFibre (g + 1) :=
  Allocation.joinEmbeddings (LEmbedding g) (PCTBEmbedding g) (by
    rintro (p | c | t | b) l h
    · exact PMap_ne_LMap g p l h
    · exact LMap_ne_CMap g l c h.symm
    · exact LMap_ne_TMap g l t h.symm
    · exact LMap_ne_BMap g l b h.symm)

end SubmittedGenus.OriginalMaps
