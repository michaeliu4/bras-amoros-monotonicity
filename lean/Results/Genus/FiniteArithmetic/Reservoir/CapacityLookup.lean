import Results.Genus.FiniteArithmetic.Reservoir.CapacityBounds

namespace SubmittedGenus.FiniteArithmetic.Reservoir
open OriginalReservoir OriginalMaps PowerSeries
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Accepted exact finite nonbinary capacity, with the two original clips
retained separately. This definition is executable without enumerating
semigroups or relying on any imported JSON equality. -/
def nonbinaryLookup (g : ℕ) : ℕ :=
  (max 0 (Certificate1500.tsLookup g-Certificate1500.usLookup g)+
    max 0 (Certificate1500.teLookup g-Certificate1500.ueLookup g)).toNat

theorem nonbinaryLookup_correct (g : ℕ) (hg : g<1500) :
    nonbinaryLookup g=nonbinaryLowerBound g := by
  have he := nonbinaryLowerBound_eq_coefficient_clip g
  simp only [coefficientNonbinaryLowerBound,map_sub] at he
  rw [←Certificate1500.ts_source_correct g hg,←Certificate1500.te_source_correct g hg,
    ←Certificate1500.us_source_correct g hg,←Certificate1500.ue_source_correct g hg] at he
  unfold nonbinaryLookup
  rw [←he]
  simp

/-- The original full capacity in the exact0–499 overlap with the accepted W
certificate. The semantic theorem below, rather than this data definition,
is the finite comparator interface. -/
def capacityLookup500 (g : ℕ) : ℕ :=
  max ((12*Nat.fastFib g+24)/25) (Nat.fastFib g-(wLookup500 g).toNat)+nonbinaryLookup g

theorem capacityLookup500_correct (g : ℕ) (hg : g<500) : capacityLookup500 g=originalCapacity g := by
  unfold capacityLookup500 originalCapacity
  rw [Nat.fastFib_eq,nonbinaryLookup_correct g (by omega),wLookup500_source_correct g hg]
  rfl

#print axioms nonbinaryLookup_correct
#print axioms capacityLookup500_correct
end
end SubmittedGenus.FiniteArithmetic.Reservoir
