import Results.Genus.CapFiveMass.Source

/-! Exact meaning of the genuine B_g population and its semigroup bridge. -/
noncomputable section
namespace SubmittedGenus.CapFiveMass

lemma hasMultipleFive_iff_depth (d : KunzData) :
    HasMultipleFive d ↔ d.depth = 5 ∧ ∃ i j, i ≠ j ∧ d.2.val i = 5 ∧ d.2.val j = 5 := by
  constructor
  · intro hd
    exact ⟨genuine_depth_five ⟨d, hd⟩, hd.2⟩
  · rintro ⟨hd, ht⟩
    refine ⟨?_, ht⟩
    intro i
    have h := KunzWord.le_depth d.2.val i
    change d.2.val i ≤ d.depth at h
    simpa [hd] using h

/-- The same genus-g population viewed as actual numerical semigroups via
its proved all-multiplicity positive-Kunz equivalence. -/
abbrev GenuineFiveSemigroupsAt (g : ℕ) :=
  {S : NumericalSemigroup.GenusFibre g //
    HasMultipleFive (KunzData.equivNumericalSemigroup.symm S.val)}

noncomputable instance (g : ℕ) : Fintype (GenuineFiveSemigroupsAt g) := by
  classical
  infer_instance

def genuineFiveAtEquivSemigroups (g : ℕ) : GenuineFiveAt g ≃ GenuineFiveSemigroupsAt g :=
  (KunzData.equivGenusFibre g).subtypeEquiv (fun d => by
    change HasMultipleFive d.val ↔ HasMultipleFive (KunzData.equivNumericalSemigroup.symm d.val.toSemigroup)
    change HasMultipleFive d.val ↔ HasMultipleFive
      (KunzData.equivNumericalSemigroup.symm (KunzData.equivNumericalSemigroup d.val))
    rw [Equiv.symm_apply_apply])

lemma count_eq_semigroup_card (g : ℕ) : count g = Fintype.card (GenuineFiveSemigroupsAt g) :=
  Fintype.card_congr (genuineFiveAtEquivSemigroups g)

end SubmittedGenus.CapFiveMass
