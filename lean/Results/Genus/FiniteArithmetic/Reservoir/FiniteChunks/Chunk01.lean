import Results.Genus.FiniteArithmetic.Reservoir.Lookup1500
namespace SubmittedGenus.FiniteArithmetic.Reservoir.Certificate1500
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
theorem recurrence_01 : CheckedRange 32 32 := by decide
theorem lower_01 : LowerRange 32 32 := by decide
#print axioms recurrence_01
#print axioms lower_01
end SubmittedGenus.FiniteArithmetic.Reservoir.Certificate1500
