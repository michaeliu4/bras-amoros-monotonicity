import Results.Genus.Injection.SourceClasses

namespace SubmittedGenus.NumericalSemigroup

/-- Minimal generators lie below twice any positive conductor bound. -/
theorem minimalGenerator_lt_twice_conductorBound {S : NumericalSemigroup} {a : ℕ}
    (ha : S.IsMinimalGenerator a) : a < 2 * S.conductorBound := by
  have hcpos : 0 < S.conductorBound := by simp [conductorBound]
  by_contra h
  have hc : S.conductorBound ∈ S := S.mem_of_conductorBound_le le_rfl
  have hdiff : a - S.conductorBound ∈ S := S.mem_of_conductorBound_le (by omega)
  rcases ha.2.2 S.conductorBound (a - S.conductorBound) hc hdiff (by omega) with h0 | h0
  · omega
  · omega

noncomputable def effectiveGenerators (S : NumericalSemigroup) : Finset ℕ := by
  classical
  exact (Finset.range (2 * S.conductorBound)).filter S.IsEffectiveGenerator

@[simp] theorem mem_effectiveGenerators (S : NumericalSemigroup) (a : ℕ) :
    a ∈ S.effectiveGenerators ↔ S.IsEffectiveGenerator a := by
  classical
  simp only [effectiveGenerators, Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => h.2, fun h => ⟨minimalGenerator_lt_twice_conductorBound h.1, h⟩⟩

theorem effectiveGenerators_nonempty {S : NumericalSemigroup} (h : ¬ S.IsLeaf) :
    S.effectiveGenerators.Nonempty := by
  classical
  simp only [IsLeaf, not_forall, not_not] at h
  obtain ⟨a, ha⟩ := h
  exact ⟨a, (S.mem_effectiveGenerators a).mpr ha⟩

noncomputable def largestEffective (S : NumericalSemigroup) (h : ¬ S.IsLeaf) : ℕ :=
  S.effectiveGenerators.max' (effectiveGenerators_nonempty h)

theorem largestEffective_spec (S : NumericalSemigroup) (h : ¬ S.IsLeaf) :
    S.IsEffectiveGenerator (S.largestEffective h) :=
  (S.mem_effectiveGenerators _).mp (Finset.max'_mem _ _)

theorem le_largestEffective (S : NumericalSemigroup) (h : ¬ S.IsLeaf)
    {a : ℕ} (ha : S.IsEffectiveGenerator a) : a ≤ S.largestEffective h :=
  Finset.le_max' _ _ ((S.mem_effectiveGenerators a).mpr ha)

/-- Precisely the ordinary-child map chosen in the submitted proof. -/
noncomputable def largestChild (S : NumericalSemigroup) (h : ¬ S.IsLeaf) :
    NumericalSemigroup := S.removeGenerator (S.largestEffective h) (S.largestEffective_spec h).1

theorem isOrdinaryChild_largestChild (S : NumericalSemigroup) (h : ¬ S.IsLeaf) :
    S.IsOrdinaryChild (S.largestChild h) :=
  ⟨S.largestEffective h, S.largestEffective_spec h, fun _ => Iff.rfl⟩

@[simp] theorem genus_largestChild (S : NumericalSemigroup) (h : ¬ S.IsLeaf) :
    (S.largestChild h).genus = S.genus + 1 :=
  genus_of_ordinaryChild (S.isOrdinaryChild_largestChild h)

end SubmittedGenus.NumericalSemigroup

namespace SubmittedGenus.OriginalMaps

open OriginalSources

noncomputable def PMap (g : ℕ) (s : SourceClass g .P) :
    NumericalSemigroup.GenusFibre (g + 1) :=
  ⟨s.val.val.toSemigroup.largestChild ((sector_P_iff s.val.val).mp s.property).2, by
    rw [NumericalSemigroup.genus_largestChild, KunzData.genus_toSemigroup, s.val.property]⟩

theorem PMap_injective (g : ℕ) : Function.Injective (PMap g) := by
  intro x y h
  have hx := x.val.val.toSemigroup.isOrdinaryChild_largestChild
    ((sector_P_iff x.val.val).mp x.property).2
  have hy := y.val.val.toSemigroup.isOrdinaryChild_largestChild
    ((sector_P_iff y.val.val).mp y.property).2
  have htargets := congrArg Subtype.val h
  change x.val.val.toSemigroup.largestChild _ = y.val.val.toSemigroup.largestChild _ at htargets
  rw [← htargets] at hy
  have hparents := NumericalSemigroup.ordinaryParent_unique hx hy
  exact Subtype.ext (Subtype.ext (KunzData.toSemigroup_injective hparents))

end SubmittedGenus.OriginalMaps
