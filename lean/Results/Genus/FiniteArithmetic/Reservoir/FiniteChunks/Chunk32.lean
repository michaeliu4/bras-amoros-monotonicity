import Results.Genus.FiniteArithmetic.Reservoir.Lookup1500
namespace SubmittedGenus.FiniteArithmetic.Reservoir.Certificate1500
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
theorem recurrence_32 : CheckedRange 1024 32 := by decide
theorem lower_32 : LowerRange 1024 32 := by decide
#print axioms recurrence_32
#print axioms lower_32
end SubmittedGenus.FiniteArithmetic.Reservoir.Certificate1500
