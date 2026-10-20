import Results.Genus.FiniteArithmetic.Reservoir.CapacityLookup
import Results.Genus.FiniteArithmetic.WExtension837.Acceptance

namespace SubmittedGenus.FiniteArithmetic.Reservoir
open OriginalReservoir OriginalMaps PowerSeries
noncomputable section

/-- Exact submitted L(g) across the entire original finite comparison range. -/
def capacityLookup837 (g : ℕ) : ℕ :=
  max ((12*Nat.fastFib g+24)/25) (Nat.fastFib g-(wLookup837 g).toNat)+nonbinaryLookup g

theorem capacityLookup837_correct (g : ℕ) (hg : g<837) :
    capacityLookup837 g=originalCapacity g := by
  unfold capacityLookup837 originalCapacity
  rw [Nat.fastFib_eq,nonbinaryLookup_correct g (by omega),wLookup837_source_correct g hg]
  rfl

#print axioms capacityLookup837_correct
end
end SubmittedGenus.FiniteArithmetic.Reservoir
