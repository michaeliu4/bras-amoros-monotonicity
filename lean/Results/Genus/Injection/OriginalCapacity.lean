import Results.Genus.Injection.Fundamental
import Results.Genus.FiniteArithmetic.WNumerical

/-! Unconditional assembly of the original partial injection and binary
capacity estimates from the proved actual-source W theorem. -/
namespace SubmittedGenus.OriginalMaps
open OriginalSources FiniteArithmetic
noncomputable section

def originalDemand (g : ℕ) : ℕ := (PowerSeries.coeff g capacityW).toNat

theorem originalDemand_cast (g : ℕ) : (originalDemand g : ℤ) = PowerSeries.coeff g capacityW := by
  unfold originalDemand
  apply Int.toNat_of_nonneg
  rw [capacityW_source_coeff]
  positivity

theorem originalDemand_majorant (g : ℕ) :
    Fintype.card (SourceClass g .D)+Fintype.card (SourceClass g .I)+
      Fintype.card (SourceClass g .B) ≤ originalDemand g := by
  have h := original_population_le_W g
  rw [←originalDemand_cast] at h
  exact_mod_cast h

theorem originalDemand_weak (g : ℕ) : 25*originalDemand g ≤ 13*Nat.fib g := by
  have h := original_W_weak_all g
  rw [←originalDemand_cast] at h
  exact_mod_cast h

theorem originalDemand_sharp (g : ℕ) (hg : 141 ≤ g) :
    1000*originalDemand g ≤ 13*Nat.fib g := by
  have h := original_W_sharp_all g hg
  rw [←originalDemand_cast] at h
  exact_mod_cast h

/-- Actual semigroups outside the exact original exceptional class inject
into the next genus, with every source and capacity premise discharged. -/
theorem original_partial_injection (g : ℕ) (hg : 1 ≤ g) :
    Nonempty (ActualNonexceptional g ↪ NumericalSemigroup.GenusFibre (g+1)) :=
  exists_actual_partialEmbedding_of_capacity g hg (original_binary_source_capacity g)

/-- The original binary fundamental inequality for genuine genus counts. -/
theorem original_fundamental_binary (g : ℕ) (hg : 1 ≤ g) :
    NumericalSemigroup.count g +
      max ((12*Nat.fib g+24)/25) (Nat.fib g-originalDemand g) ≤
      NumericalSemigroup.count (g+1)+Fintype.card (SourceClass g .E) := by
  obtain ⟨fresh,hreserved⟩ := exists_joint_DI_allocation g hg (original_binary_source_capacity g)
  exact fundamental_original_binary_bound g (originalDemand g) hg fresh hreserved
    (originalDemand_majorant g) (originalDemand_weak g)

/-- The sharper original binary reservoir is an actual unused-target bound,
not a standalone Fibonacci inequality. -/
theorem original_sharp_binary_supply (g : ℕ) (hg : 141 ≤ g) :
    ∃ fresh : DISources g ↪ BinaryEndTwo g,
      ∃ hreserved : ∀ di b, fresh di ≠ BReserved g b,
        987*Nat.fib g ≤ 1000*Fintype.card (UnusedBinary g fresh hreserved) := by
  obtain ⟨fresh,hreserved⟩ := exists_joint_DI_allocation g (by omega)
    (original_binary_source_capacity g)
  exact ⟨fresh,hreserved,unusedBinary_sharp_capacity g (originalDemand g) (by omega)
    fresh hreserved (originalDemand_majorant g) (originalDemand_sharp g hg)⟩

#print axioms original_partial_injection
#print axioms original_fundamental_binary
#print axioms original_sharp_binary_supply
end
end SubmittedGenus.OriginalMaps
