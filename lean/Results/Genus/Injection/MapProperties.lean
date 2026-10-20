import Results.Genus.Injection.ParentAppendMap
import Results.Genus.Injection.OrdinaryMap
import Results.Genus.Injection.CodeMap

namespace SubmittedGenus.KunzWord

theorem depth_append {m a : ℕ} (x : KunzWord m) (hm : 0 < m) :
    depth (append x a) = max (depth x) a := by
  apply Nat.le_antisymm
  · apply (depth_le_iff _).mpr
    exact append_bounded (fun i => (le_depth x i).trans (le_max_left _ _)) (le_max_right _ _)
  · apply max_le
    · apply (depth_le_iff x).mpr
      intro i
      have hi0 : 0 < i.val + 1 := by omega
      have him : i.val + 1 < m := by omega
      have hcoord := coord_append_old (a := a) x hi0 him
      rw [coord_index] at hcoord
      rw [← hcoord]
      exact coord_le_depth _ _
    · have hcoord := coord_append_last (a := a) x hm
      simpa only [hcoord] using coord_le_depth (append x a) m

end SubmittedGenus.KunzWord

namespace SubmittedGenus.KunzData

/-- The final physical Kunz coordinate, zero for the empty word. -/
def lastLetter (d : KunzData) : ℕ := KunzWord.coord d.2.val (d.1.val - 1)

theorem depth_le_of_subset (d : KunzData) (T : NumericalSemigroup)
    (hsubset : ∀ n : ℕ, n ∈ T → n ∈ d.toSemigroup)
    (hm : T.IsMultiplicity d.1.val) : d.depth ≤ T.kunzDepth := by
  let y := KunzWord.ofSemigroup T hm
  let e : KunzData := ⟨d.1, ⟨y, KunzWord.valid_ofSemigroup T hm⟩⟩
  have he : e.toSemigroup = T := KunzWord.toSemigroup_ofSemigroup T hm
  rw [← he, NumericalSemigroup.kunzDepth_toSemigroup]
  apply (KunzWord.depth_le_iff d.2.val).mpr
  intro i
  have him : i.val + 1 < d.1.val := by omega
  have hmem : i.val + 1 + d.1.val * y i ∈ T := by
    rw [← he, KunzData.toSemigroup, KunzWord.mem_toSemigroup,
      KunzWord.tailMem_residue _ d.1.property him, KunzWord.coord_index]
  have hsource := hsubset _ hmem
  change KunzWord.TailMem d.2.val (i.val + 1 + d.1.val * y i) at hsource
  rw [KunzWord.tailMem_residue _ d.1.property him, KunzWord.coord_index] at hsource
  exact hsource.trans (KunzWord.le_depth y i)

theorem highDepth_frobenius_gt_multiplicity {d : KunzData} (hhigh : 4 ≤ d.depth) :
    (d.1.val : ℤ) < d.toSemigroup.frobenius := by
  have hm := KunzWord.one_lt_multiplicity_of_depth_pos d.2.val
    (by change 0 < d.depth; omega)
  have hs := KunzWord.rightmostMaximum_spec d.2.val hm
  change 0 < KunzWord.rightmostMaximum d.2.val ∧ _ at hs
  change (d.1.val : ℤ) < (KunzWord.toSemigroup _ _ _).frobenius
  rw [KunzWord.frobenius_eq_depth_rightmost d.2.val hm d.2.property]
  have hdepth : 4 ≤ KunzWord.depth d.2.val := hhigh
  have hmul := Nat.mul_le_mul_right d.1.val (by omega : 1 ≤ KunzWord.depth d.2.val - 1)
  simp only [Nat.one_mul] at hmul
  exact_mod_cast (show d.1.val <
    (KunzWord.depth d.2.val - 1) * d.1.val + KunzWord.rightmostMaximum d.2.val by omega)

end SubmittedGenus.KunzData

namespace SubmittedGenus.OriginalMaps

open OriginalSources

@[simp] theorem lowAppend_lastLetter (a : ℕ) (ha0 : 0 < a) (ha2 : a ≤ 2)
    (d : LowSource) : (lowAppend a ha0 ha2 d).lastLetter = a := by
  exact KunzWord.coord_append_last d.val.2.val d.val.1.property

theorem PMap_high (g : ℕ) (s : SourceClass g .P) : 4 ≤ (PMap g s).val.kunzDepth := by
  let d := s.val.val
  have hs := (sector_P_iff d).mp s.property
  have hhigh : 4 ≤ d.depth := by have := hs.1; unfold low at this; omega
  let a := d.toSemigroup.largestEffective hs.2
  have ha := d.toSemigroup.largestEffective_spec hs.2
  have hF := KunzData.highDepth_frobenius_gt_multiplicity hhigh
  have hgreater := (NumericalSemigroup.isEffectiveGenerator_iff.mp ha).2
  have ham : d.1.val ≠ a := by omega
  have hm := KunzWord.isMultiplicity_toSemigroup d.2.val d.1.property d.2.property
  have hchildmult : (d.toSemigroup.largestChild hs.2).IsMultiplicity d.1.val := by
    refine ⟨hm.1, ⟨hm.2.1, ham⟩, ?_⟩
    intro n hn hnmem
    exact hm.2.2 n hn hnmem.1
  have hmono := d.depth_le_of_subset (d.toSemigroup.largestChild hs.2)
    (fun _ hn => hn.1) hchildmult
  change 4 ≤ (d.toSemigroup.largestChild hs.2).kunzDepth
  omega

theorem LMap_low (g : ℕ) (s : SourceClass g .L) : (LMap g s).val.kunzDepth ≤ 3 := by
  change ((lowAppend 1 (by omega) (by omega)
    ⟨s.val.val, (sector_L_iff s.val.val).mp s.property⟩).toSemigroup).kunzDepth ≤ 3
  rw [NumericalSemigroup.kunzDepth_toSemigroup]
  exact lowAppend_low _ _ _ _

theorem CMap_low (g : ℕ) (s : SourceClass g .C) : (CMap g s).val.kunzDepth ≤ 3 := by
  change ((lowAppend 2 (by omega) (by omega)
    (CParent ⟨s.val.val, s.property⟩)).toSemigroup).kunzDepth ≤ 3
  rw [NumericalSemigroup.kunzDepth_toSemigroup]
  exact lowAppend_low _ _ _ _

theorem CParent_depth (s : CSource) : (CParent s).val.depth = 3 := by
  have hs := (sector_C_iff s.val).mp s.property
  have hhigh : 4 ≤ s.val.depth := by have := hs.1; unfold low at this; omega
  obtain ⟨p, hpdepth, hright⟩ := KunzWord.exists_rightmost_maximum s.val.2.val
    (by change 0 < s.val.depth; omega)
  have hp : 4 ≤ s.val.2.val p := by change s.val.2.val p = s.val.depth at hpdepth; omega
  have hmax : ∀ i, s.val.2.val i ≤ s.val.2.val p := by
    intro i
    rw [hpdepth]
    exact KunzWord.le_depth s.val.2.val i
  have hcrit := (lowParent_iff_at_rightmost s.val p hp hmax hright).mp hs.2.2
  let P : KunzData := ⟨s.val.1,
    ⟨KunzWord.lowerAt s.val.2.val p, s.val.2.property.lowerMaximum (by omega) hmax⟩⟩
  have hparent : P.toSemigroup.IsOrdinaryChild s.val.toSemigroup :=
    KunzWord.lowerAt_isOrdinaryParent s.val.2.val s.val.1.property s.val.2.property p
      (by omega) hmax hright
  have heq : (CParent s).val = P := KunzData.toSemigroup_injective
    (NumericalSemigroup.ordinaryParent_unique (CParent_isOrdinaryParent s) hparent)
  rw [heq]
  change KunzWord.depth (KunzWord.lowerAt s.val.2.val p) = 3
  apply Nat.le_antisymm
  · exact (KunzWord.lowerAt_depth_le_three_iff s.val.2.val p hp).mpr hcrit
  · have h := KunzWord.le_depth (KunzWord.lowerAt s.val.2.val p) p
    simp only [KunzWord.lowerAt_self, hcrit.1] at h
    exact h

theorem CMap_depth (g : ℕ) (s : SourceClass g .C) : (CMap g s).val.kunzDepth = 3 := by
  change ((lowAppend 2 (by omega) (by omega)
    (CParent ⟨s.val.val, s.property⟩)).toSemigroup).kunzDepth = 3
  rw [NumericalSemigroup.kunzDepth_toSemigroup]
  change KunzWord.depth (KunzWord.append _ 2) = 3
  rw [KunzWord.depth_append _ (CParent ⟨s.val.val, s.property⟩).val.1.property]
  have h := CParent_depth ⟨s.val.val, s.property⟩
  change KunzWord.depth (CParent ⟨s.val.val, s.property⟩).val.2.val = 3 at h
  rw [h]
  decide

theorem BTarget_depth (d : KunzData) : (BTarget d).depth ≤ 2 := by
  apply (KunzWord.depth_le_iff _).mpr
  intro i
  have h := BinaryCode.target_binary d.prefixList _ (List.getElem_mem
    (l := BinaryCode.target d.prefixList) (n := i.val) (by simpa only [BTarget, KunzWord.binaryData, Nat.add_sub_cancel] using i.isLt))
  change (BinaryCode.target d.prefixList)[i.val]'(by simpa only [BTarget, KunzWord.binaryData, Nat.add_sub_cancel] using i.isLt) ≤ 2
  omega

theorem BTarget_lastLetter (d : KunzData) : (BTarget d).lastLetter = 2 := by
  simp [KunzData.lastLetter, BTarget, KunzWord.binaryData, KunzWord.coord,
    KunzWord.ofList, BinaryCode.target]

theorem BMap_depth (g : ℕ) (s : SourceClass g .B) : (BMap g s).val.kunzDepth ≤ 2 := by
  change (BTarget s.val.val).toSemigroup.kunzDepth ≤ 2
  rw [NumericalSemigroup.kunzDepth_toSemigroup]
  exact BTarget_depth _

theorem PMap_ne_LMap (g : ℕ) (x : SourceClass g .P) (y : SourceClass g .L) :
    PMap g x ≠ LMap g y := by
  intro h
  have hp := PMap_high g x
  have hl := LMap_low g y
  rw [h] at hp
  omega

theorem PMap_ne_CMap (g : ℕ) (x : SourceClass g .P) (y : SourceClass g .C) :
    PMap g x ≠ CMap g y := by
  intro h
  have hp := PMap_high g x
  have hc := CMap_low g y
  rw [h] at hp
  omega

theorem PMap_ne_BMap (g : ℕ) (x : SourceClass g .P) (y : SourceClass g .B) :
    PMap g x ≠ BMap g y := by
  intro h
  have hp := PMap_high g x
  have hb := BMap_depth g y
  rw [h] at hp
  omega

theorem CMap_ne_BMap (g : ℕ) (x : SourceClass g .C) (y : SourceClass g .B) :
    CMap g x ≠ BMap g y := by
  intro h
  have hc := CMap_depth g x
  have hb := BMap_depth g y
  rw [h] at hc
  omega

theorem LMap_ne_BMap (g : ℕ) (x : SourceClass g .L) (y : SourceClass g .B) :
    LMap g x ≠ BMap g y := by
  intro h
  have hdata := KunzData.toSemigroup_injective (congrArg Subtype.val h)
  have hlast := congrArg KunzData.lastLetter hdata
  change (lowAppend 1 (by omega) (by omega)
    ⟨x.val.val, (sector_L_iff x.val.val).mp x.property⟩).lastLetter =
      (BTarget y.val.val).lastLetter at hlast
  rw [lowAppend_lastLetter, BTarget_lastLetter] at hlast
  omega

end SubmittedGenus.OriginalMaps
