import Results.Genus.FixedPivot.FiniteModes

/-! The original degree-(d+1) structural recurrence for finite core contractions. -/
namespace SubmittedGenus.FixedPivot
open scoped BigOperators
section Ring
variable {R I C : Type*} [CommRing R] [Fintype I] [Fintype C] [DecidableEq C]

def fullModeRoots (lam mu : R) (d : ℕ) : List R :=
  (List.range (d+1)).map (fun j => lam^(d-j)*mu^j)

lemma modeRate_mem_fullModeRoots (lam mu : R) (arity : C→ℕ) {d : ℕ}
    (hd : (∑ c,arity c)=d) (choice : C→Bool) :
    lam^(pureModeDegree arity choice)*mu^(mixedModeDegree arity choice)∈fullModeRoots lam mu d := by
  obtain ⟨hj,hrate⟩:=modeRate_source_index lam mu arity hd choice
  rw [hrate]
  exact List.mem_map.mpr ⟨mixedModeDegree arity choice,List.mem_range.mpr (by omega),rfl⟩

/-- Finite core contraction commutes with the exact finite mode expansion. -/
theorem finiteCoreMode_expansion (lam mu : R) (arity : C→ℕ) (core : I→R)
    (A B : I→C→R) (k : ℕ) :
    (∑ i : I,core i*∏ c,(A i c*(lam^(arity c))^k+B i c*(mu^(arity c))^k))=
      ∑ pair : I×(C→Bool),
        (core pair.1*(∏ c,if pair.2 c then B pair.1 c else A pair.1 c))*
        (lam^(pureModeDegree arity pair.2)*mu^(mixedModeDegree arity pair.2))^k := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [finiteMode_expansion,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro choice _
  ring

/-- Applying the actual product of shift factors kills the contracted source
mode expression, including repeated roots and the base phase k=0. -/
theorem finiteCoreMode_recurrence (lam mu : R) (arity : C→ℕ) {d : ℕ}
    (hd : (∑ c,arity c)=d) (core : I→R) (A B : I→C→R) (n : ℕ) :
    applyAnnihilator (fullModeRoots lam mu d)
      (fun k => ∑ i : I,core i*∏ c,(A i c*(lam^(arity c))^k+B i c*(mu^(arity c))^k)) n=0 := by
  have he : (fun k => ∑ i : I,core i*∏ c,(A i c*(lam^(arity c))^k+B i c*(mu^(arity c))^k))=
      fun k => ∑ pair : I×(C→Bool),
        (core pair.1*(∏ c,if pair.2 c then B pair.1 c else A pair.1 c))*
        (lam^(pureModeDegree arity pair.2)*mu^(mixedModeDegree arity pair.2))^k := by
    funext k
    exact finiteCoreMode_expansion lam mu arity core A B k
  rw [he]
  apply annihilator_finite_exponentials
  intro pair
  exact modeRate_mem_fullModeRoots lam mu arity hd pair.2

end Ring
end SubmittedGenus.FixedPivot
