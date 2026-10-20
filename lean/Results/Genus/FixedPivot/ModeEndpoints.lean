import Results.Genus.FixedPivot.SourceGenerating
import Results.Genus.FixedPivot.PurePhases

/-! Identification of the two endpoint mode coefficients with actual all-pure contractions. -/
namespace SubmittedGenus.FixedPivot
open scoped BigOperators
noncomputable section

lemma mixedModeDegree_zero_iff {C : Type*} [Fintype C] (arity : C→ℕ)
    (hpos : ∀ c,0<arity c) (choice : C→Bool) :
    mixedModeDegree arity choice=0 ↔ choice=(fun _ => false) := by
  constructor
  · intro h
    funext c
    have hh : (if choice c then arity c else 0)≤mixedModeDegree arity choice :=
      by
        unfold mixedModeDegree
        exact Finset.single_le_sum (f := fun a => if choice a then arity a else 0)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
    rw [h] at hh
    cases hc : choice c
    · rfl
    · simp only [hc,ite_true] at hh
      have:=hpos c
      omega
  · intro h
    rw [h]
    simp [mixedModeDegree]

lemma pureModeDegree_zero_iff {C : Type*} [Fintype C] (arity : C→ℕ)
    (hpos : ∀ c,0<arity c) (choice : C→Bool) :
    pureModeDegree arity choice=0 ↔ choice=(fun _ => true) := by
  constructor
  · intro h
    funext c
    have hh : (if choice c then 0 else arity c)≤pureModeDegree arity choice :=
      by
        unfold pureModeDegree
        exact Finset.single_le_sum (f := fun a => if choice a then 0 else arity a)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
    rw [h] at hh
    cases hc : choice c
    · simp only [hc,Bool.false_eq_true,ite_false] at hh
      have:=hpos c
      omega
    · rfl
  · intro h
    rw [h]
    simp [pureModeDegree]

lemma sourceModeIndex_zero_iff {N d : ℕ} (hN : d<N)
    (choice : CarryRepresentative N d hN→Bool) :
    sourceModeIndex hN choice=0 ↔ choice=(fun _ => false) := by
  rw [Fin.ext_iff]
  change mixedModeDegree (carryPortArity N d hN) choice=0 ↔ _
  exact mixedModeDegree_zero_iff _ (carryPortArity_pos N d hN) choice

lemma sourceModeIndex_last_iff {N d : ℕ} (hN : d<N)
    (choice : CarryRepresentative N d hN→Bool) :
    sourceModeIndex hN choice=Fin.last d ↔ choice=(fun _ => true) := by
  rw [Fin.ext_iff]
  change mixedModeDegree (carryPortArity N d hN) choice=d ↔ _
  have hh:=modeDegrees_sum (carryPortArity N d hN) choice
  rw [carry_port_arity_sum] at hh
  rw [← pureModeDegree_zero_iff _ (carryPortArity_pos N d hN) choice]
  omega

section Ring
variable {R : Type*} [CommRing R]

lemma sourceModeCoefficient_zero {r N d : ℕ} (hN : d<N) (z lam mu li mi di : R) :
    (∑ pair∈Finset.univ.filter (fun pair : SourceModeAssignment r N d hN =>
      sourceModeIndex hN pair.2=0),sourceModeCoefficient (r := r) hN z lam mu li mi di pair)=
      canonicalPureContribution z lam mu li di r N d hN := by
  simp only [Finset.sum_filter,sourceModeIndex_zero_iff]
  rw [Fintype.sum_prod_type]
  simp only [sourceModeCoefficient,canonicalModeAmplitude,canonicalPureContribution]
  apply Finset.sum_congr rfl
  intro x _
  simp

lemma sourceModeCoefficient_last {r N d : ℕ} (hN : d<N) (z lam mu li mi di : R) :
    (∑ pair∈Finset.univ.filter (fun pair : SourceModeAssignment r N d hN =>
      sourceModeIndex hN pair.2=Fin.last d),sourceModeCoefficient (r := r) hN z lam mu li mi di pair)=
      canonicalPureContribution z mu lam mi (-di) r N d hN := by
  simp only [Finset.sum_filter,sourceModeIndex_last_iff]
  rw [Fintype.sum_prod_type]
  simp only [sourceModeCoefficient,canonicalModeAmplitude,canonicalPureContribution]
  apply Finset.sum_congr rfl
  intro x _
  simp

end Ring
end
end SubmittedGenus.FixedPivot
