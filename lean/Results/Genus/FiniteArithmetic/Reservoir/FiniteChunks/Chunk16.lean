import Results.Genus.FiniteArithmetic.Reservoir.Lookup1500
namespace SubmittedGenus.FiniteArithmetic.Reservoir.Certificate1500
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
theorem recurrence_16 : CheckedRange 512 32 := by decide
theorem lower_16 : LowerRange 512 32 := by decide
#print axioms recurrence_16
#print axioms lower_16
end SubmittedGenus.FiniteArithmetic.Reservoir.Certificate1500
