import Results.Genus.Injection.ActualMaps
import Results.Genus.Injection.Residual

namespace SubmittedGenus.OriginalMaps

open OriginalSources

abbrev CSource := {d : KunzData // sector d = .C}

noncomputable def CParent (s : CSource) : LowSource := by
  let h := ((sector_C_iff s.val).mp s.property).2.2
  let P := Classical.choose h
  refine ⟨KunzData.equivNumericalSemigroup.symm P, ?_⟩
  exact (Classical.choose_spec h).2

theorem CParent_isOrdinaryParent (s : CSource) :
    (CParent s).val.toSemigroup.IsOrdinaryChild s.val.toSemigroup := by
  let h := ((sector_C_iff s.val).mp s.property).2.2
  change (KunzData.equivNumericalSemigroup
    (KunzData.equivNumericalSemigroup.symm (Classical.choose h))).IsOrdinaryChild _
  rw [Equiv.apply_symm_apply]
  exact (Classical.choose_spec h).1

theorem CSource_leaf (s : CSource) : s.val.toSemigroup.IsLeaf := by
  classical
  have h := ((sector_C_iff s.val).mp s.property).2.1
  simpa only [nonleaf, not_not] using h

theorem CParent_injective : Function.Injective CParent := by
  intro x y h
  have hx := CParent_isOrdinaryParent x
  have hy := CParent_isOrdinaryParent y
  rw [← h] at hy
  have hs := NumericalSemigroup.leafChild_unique hx hy (CSource_leaf x) (CSource_leaf y)
  exact Subtype.ext (KunzData.toSemigroup_injective hs)

/-- The exact third map: restore the unique parent, then append `2`. -/
noncomputable def CMap (g : ℕ) (s : SourceClass g .C) :
    NumericalSemigroup.GenusFibre (g + 1) :=
  ⟨(lowAppend 2 (by omega) (by omega) (CParent ⟨s.val.val, s.property⟩)).toSemigroup, by
    rw [lowAppend_genus]
    have hp := NumericalSemigroup.genus_of_ordinaryChild
      (CParent_isOrdinaryParent ⟨s.val.val, s.property⟩)
    simp only [KunzData.genus_toSemigroup] at hp
    have hg := s.val.property
    omega⟩

theorem CMap_injective (g : ℕ) : Function.Injective (CMap g) := by
  intro x y h
  have hparents := lowAppend_semigroup_injective 2 (by omega) (by omega)
    (congrArg Subtype.val h)
  have hsources := CParent_injective hparents
  have hdata : x.val.val = y.val.val := congrArg (fun z : CSource => z.val) hsources
  exact Subtype.ext (Subtype.ext hdata)

/-- The first and third image sectors are already disjoint as actual
semigroups, because their final Kunz letters differ. -/
theorem LMap_ne_CMap (g : ℕ) (x : SourceClass g .L) (y : SourceClass g .C) :
    LMap g x ≠ CMap g y := by
  intro h
  have hlast := lowAppend_letter_eq_of_semigroup_eq
    ⟨x.val.val, (sector_L_iff x.val.val).mp x.property⟩
    (CParent ⟨y.val.val, y.property⟩) (congrArg Subtype.val h)
  omega

end SubmittedGenus.OriginalMaps
