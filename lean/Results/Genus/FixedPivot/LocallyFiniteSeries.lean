import Results.Genus.FixedPivot.InitialNumerator
import Results.Genus.RawGraph.SignedCounterexample
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Topology.Instances.Rat

/-! Coefficientwise finite multiplicity sums of the actual fixed-pivot genus series. -/
namespace SubmittedGenus.FixedPivot
open RawGraph
open scoped BigOperators PowerSeries.WithPiTopology
noncomputable section

def locallyFinitePolynomialSum (f : ℕ→Polynomial ℚ) : PowerSeries ℚ :=
  PowerSeries.mk (fun n => ∑ k∈Finset.range (n+1),(f k).coeff n)

/-- This summation theorem is purely coefficientwise: every coefficient has
finite support, so no numerical convergence estimate is assumed. -/
theorem hasSum_locallyFinitePolynomialSum (f : ℕ→Polynomial ℚ)
    (hcut : ∀ n k,n<k → (f k).coeff n=0) :
    HasSum (fun k => (f k : PowerSeries ℚ)) (locallyFinitePolynomialSum f) := by
  rw [PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff]
  intro n
  simp only [locallyFinitePolynomialSum,PowerSeries.coeff_mk,Polynomial.coeff_coe]
  apply hasSum_sum_of_ne_finset_zero
  intro k hk
  apply hcut n k
  have hh : ¬k<n+1 := by simpa only [Finset.mem_range] using hk
  omega

def fixedPivotSeriesQ (r p : ℕ) : PowerSeries ℚ :=
  PowerSeries.map (Int.castRingHom ℚ) (SignedCounterexample.fixedPivotSeries r p)

lemma fixedPivotSeriesQ_coeff (r p g : ℕ) :
    PowerSeries.coeff g (fixedPivotSeriesQ r p)=∑ m∈Finset.range (g+1),(rawPolynomialQ m r p).coeff g := by
  simp [fixedPivotSeriesQ,SignedCounterexample.fixedPivotSeries,SignedCounterexample.fixedPivotCoeff,
    rawPolynomialQ]

/-- The reused signed-series source is exactly the complete multiplicity sum. -/
theorem fixedPivotSeriesQ_hasSum (r p : ℕ) :
    HasSum (fun m => (rawPolynomialQ m r p : PowerSeries ℚ)) (fixedPivotSeriesQ r p) := by
  have he : locallyFinitePolynomialSum (fun m => rawPolynomialQ m r p)=fixedPivotSeriesQ r p := by
    apply PowerSeries.ext
    intro n
    rw [fixedPivotSeriesQ_coeff]
    simp only [locallyFinitePolynomialSum,PowerSeries.coeff_mk]
  rw [← he]
  apply hasSum_locallyFinitePolynomialSum
  intro g m hm
  simp only [rawPolynomialQ,Polynomial.coeff_map]
  rw [SignedCounterexample.coeff_zero_of_multiplicity (by omega),map_zero]

/-- Every arithmetic source progression is coefficientwise summable by the
original genus≥m+5 support bound. -/
theorem rawProgression_hasSum (m r p d : ℕ) (hd : 0<d) :
    HasSum (fun k => (rawPolynomialQ (m+k*d) r p : PowerSeries ℚ))
      (locallyFinitePolynomialSum (fun k => rawPolynomialQ (m+k*d) r p)) := by
  apply hasSum_locallyFinitePolynomialSum
  intro g k hg
  have hk : k≤k*d := Nat.le_mul_of_pos_right k hd
  simp only [rawPolynomialQ,Polynomial.coeff_map]
  rw [SignedCounterexample.coeff_zero_of_multiplicity (by omega),map_zero]

end
end SubmittedGenus.FixedPivot
