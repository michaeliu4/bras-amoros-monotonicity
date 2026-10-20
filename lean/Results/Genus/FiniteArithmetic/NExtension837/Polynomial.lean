import Results.Genus.FiniteArithmetic.MarkedFour
import Results.Genus.FiniteArithmetic.LookupSparse
namespace SubmittedGenus.FiniteArithmetic.NExtension837
open PowerSeries

def numeratorTerms : Sparse.Terms := [(8,1)]
def denominatorTail : Sparse.Terms := [(2,-3),(3,-3),(4,2),(5,6),(6,4),(7,-1),(8,-4),(9,-3),(10,-1)]
theorem denominator_positive : ∀ t∈denominatorTail,0<t.1 := by decide

/-- The original N source identity supplies this exact sparse recurrence. -/
theorem source_identity :
    (1+Sparse.series denominatorTail)*capacityN=Sparse.series numeratorTerms := by
  have hd : 1+Sparse.series denominatorTail =
      (1-(X:PowerSeries ℤ)^2-X^3)^2*(1-X^2-X^3-X^4) := by
    norm_num [Sparse.series,denominatorTail] <;> ring
  rw [hd,capacityN_source_identity]
  simp [Sparse.series,numeratorTerms]

#print axioms source_identity
end SubmittedGenus.FiniteArithmetic.NExtension837
