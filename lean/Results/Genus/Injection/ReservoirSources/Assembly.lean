import Results.Genus.Injection.ReservoirSources.Targets
import Results.Genus.Injection.OriginalCapacity

noncomputable section
namespace SubmittedGenus.OriginalReservoir
open OriginalMaps OriginalSources FiniteArithmetic
attribute [local instance] Classical.propDecidable

/-- Unconditional original low-depth supply, with both actual prefix
families and the already-proved original W population bound. -/
lemma original_low_supply (g : ℕ) (hg : 1 ≤ g) :
    ∃ fresh : DISources g ↪ BinaryEndTwo g,
      ∃ hreserved : ∀ di b, fresh di ≠ BReserved g b,
        max ((12*Nat.fib g+24)/25) (Nat.fib g-originalDemand g) + nonbinaryLowerBound g ≤
          Fintype.card (UnusedLow g fresh hreserved) := by
  obtain ⟨fresh,hreserved⟩ := exists_joint_DI_allocation g hg (original_binary_source_capacity g)
  exact ⟨fresh,hreserved,original_capacity_bound g (originalDemand g) hg fresh hreserved
    (originalDemand_majorant g) (originalDemand_weak g)⟩

/-- The complete original combinatorial fundamental inequality on genuine
semigroups; the remaining reservoir producer identifies the finite literal
counts here with the submitted rational marked-prefix series. -/
lemma original_fundamental_reservoir (g : ℕ) (hg : 1 ≤ g) :
    NumericalSemigroup.count g +
      (max ((12*Nat.fib g+24)/25) (Nat.fib g-originalDemand g) + nonbinaryLowerBound g) ≤
      NumericalSemigroup.count (g+1)+Fintype.card (SourceClass g .E) := by
  obtain ⟨fresh,hreserved,hbound⟩ := original_low_supply g hg
  exact fundamental_low_bound g _ fresh hreserved hbound

/-- Integer form of the paper's exact low-depth identity, without natural
subtraction hiding any intermediate truncation. -/
lemma unusedLow_card_int (g : ℕ) (fresh : DISources g ↪ BinaryEndTwo g)
    (hreserved : ∀ di b, fresh di ≠ BReserved g b) :
    (Fintype.card (UnusedLow g fresh hreserved) : ℤ) =
      (lowCount (g+1) : ℤ) - lowCount g - Fintype.card (SourceClass g .C) -
      Fintype.card (SourceClass g .T) - Fintype.card (SourceClass g .D) -
      Fintype.card (SourceClass g .I) - Fintype.card (SourceClass g .B) := by
  have h := unusedLow_balance g fresh hreserved
  omega

/-- Exact finite-count inequality in the signed form printed in the paper. -/
lemma original_fundamental_signed (g : ℕ) (fresh : DISources g ↪ BinaryEndTwo g)
    (hreserved : ∀ di b, fresh di ≠ BReserved g b) :
    (NumericalSemigroup.count (g+1) : ℤ) - NumericalSemigroup.count g ≥
      (Fintype.card (UnusedLow g fresh hreserved) : ℤ) - Fintype.card (SourceClass g .E) := by
  have h := fundamental_low_bound g (Fintype.card (UnusedLow g fresh hreserved))
    fresh hreserved (by rfl)
  omega

#print axioms original_low_supply
#print axioms original_fundamental_reservoir
#print axioms unusedLow_card_int
#print axioms original_fundamental_signed
end SubmittedGenus.OriginalReservoir
