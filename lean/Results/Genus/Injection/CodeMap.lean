import Results.Genus.Injection.Residual
import Results.Genus.Injection.WordLists

namespace SubmittedGenus.OriginalMaps

open OriginalSources

/-- The original `B` source really ends in `1`. -/
theorem B_toList_eq {d : KunzData} (hB : sector d = .B) :
    d.toList = d.prefixList ++ [1] := by
  have hs := (sector_B_iff d).mp hB
  have hd := hs.2.2.2.2.2.2.1
  have hf := hs.2.2.2.2.2.2.2.1
  have hm := KunzWord.one_lt_multiplicity_of_depth_pos d.2.val
    (by change 0 < d.depth; omega)
  rw [KunzData.toList_eq_prefix_append_last d hm, hf]

/-- Earlier exclusions and the sole-final-one condition leave a literal
prefix over `{2,3,4}`, exactly the domain of the submitted block code. -/
theorem B_prefix {d : KunzData} (hB : sector d = .B) : BinaryCode.Prefix d.prefixList := by
  have hs := (sector_B_iff d).mp hB
  have hd := hs.2.2.2.2.2.2.1
  have hsole := hs.2.2.2.2.2.2.2.2
  intro a ha
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
  let j : Fin (d.1.val - 1) := ⟨i.val, by omega⟩
  have hjlast : j.val + 1 ≠ d.1.val - 1 := by dsimp [j]; omega
  have hne1 := hsole j hjlast
  have hpos := d.2.property.positive j
  have hbound := KunzWord.le_depth d.2.val j
  change d.2.val j ≤ d.depth at hbound
  change d.2.val j = 2 ∨ d.2.val j = 3 ∨ d.2.val j = 4
  omega

/-- The exact binary code target interpreted as a genuine numerical semigroup. -/
def BTarget (d : KunzData) : KunzData :=
  KunzWord.binaryData (BinaryCode.target d.prefixList) (BinaryCode.target_binary _)

theorem BTarget_genus {d : KunzData} (hB : sector d = .B) :
    (BTarget d).toSemigroup.genus = d.weight + 1 := by
  rw [BTarget, KunzWord.genus_binaryData]
  rw [BinaryCode.target_weight (B_prefix hB), ← B_toList_eq hB, KunzData.sum_toList]

theorem BTarget_injective {d e : KunzData} (hd : sector d = .B) (he : sector e = .B)
    (h : (BTarget d).toSemigroup = (BTarget e).toSemigroup) : d = e := by
  have hdata := KunzData.toSemigroup_injective h
  have hcode := congrArg KunzData.toList hdata
  simp only [BTarget, KunzWord.toList_binaryData] at hcode
  have hprefix := BinaryCode.target_injective_on_prefix (B_prefix hd) (B_prefix he) hcode
  apply KunzData.toList_injective
  rw [B_toList_eq hd, B_toList_eq he, hprefix]

/-- The fifth elementary map from the original proof, with its actual genus
codomain and already-reserved image. -/
def BMap (g : ℕ) (s : SourceClass g .B) : NumericalSemigroup.GenusFibre (g + 1) :=
  ⟨(BTarget s.val.val).toSemigroup, by
    rw [BTarget_genus s.property, s.val.property]⟩

theorem BMap_injective (g : ℕ) : Function.Injective (BMap g) := by
  intro x y h
  have hdata := BTarget_injective x.property y.property (congrArg Subtype.val h)
  exact Subtype.ext (Subtype.ext hdata)

end SubmittedGenus.OriginalMaps
