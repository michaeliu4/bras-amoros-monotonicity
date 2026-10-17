import Results.Genus.FiniteArithmetic.Reservoir.Lookup1500
namespace SubmittedGenus.FiniteArithmetic.Reservoir.Certificate1500
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
theorem recurrence_20 : CheckedRange 640 32 := by decide
theorem lower_20 : LowerRange 640 32 := by decide
#print axioms recurrence_20
#print axioms lower_20
end SubmittedGenus.FiniteArithmetic.Reservoir.Certificate1500
