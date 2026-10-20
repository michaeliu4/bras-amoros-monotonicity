import Results.Genus.FiniteComparison.OmittedSource

noncomputable section
open scoped BigOperators
namespace SubmittedGenus.FiniteComparison.AllGenusOmittedSource
open RawGraph RawGraph.SignedCounterexample SourceBoxes OmittedSource

def horizon (g : ℕ) := max 301 (g+2)
def retainedPrefix (g : ℕ) := ∑ p ∈ Finset.range 301,∑ r ∈ Finset.Ico 1 p,fixedPivotCoeff r p g

lemma multiplicity_sum_dynamic (r p g : ℕ) :
    (∑ m ∈ Finset.range (horizon g),(rawPolynomial m r p 4).coeff g)=fixedPivotCoeff r p g := by
  unfold fixedPivotCoeff
  apply sum_range_same
  · intro m hm
    have hh:=le_max_right 301 (g+2)
    exact coeff_zero_of_multiplicity (by unfold horizon at hm; omega)
  · intro m hm
    exact coeff_zero_of_multiplicity (by omega)

lemma rawFour_eq_dynamic_box (g : ℕ) : OriginalPopulations.rawFourCount g=box 4 (horizon g) g := by
  rw [OriginalPopulations.RawFourAggregate.rawFourCount_eq_aggregate,fin_aggregate_eq_box]
  apply triple_sum_same
  · exact coefficient_cube_support (by intro m hm; omega)
  · apply coefficient_cube_support
    intro m hm
    have hh:=le_max_right 301 (g+2)
    unfold horizon at hm
    omega

lemma pivot_sum (g p : ℕ) (hp : p<horizon g) :
    (∑ r ∈ Finset.range (horizon g),fixedPivotCoeff r p g)=
      ∑ r ∈ Finset.Ico 1 p,fixedPivotCoeff r p g := by
  have he : (∑ r ∈ Finset.range (horizon g),fixedPivotCoeff r p g)=
      ∑ r ∈ Finset.range p,fixedPivotCoeff r p g := by
    apply sum_range_same
    · intro r hr; exact fixedPivotCoeff_invalid (Or.inr (by omega))
    · intro r hr; exact fixedPivotCoeff_invalid (Or.inr hr)
  rw [he]
  by_cases hz : p=0
  · subst p; simp
  · rw [←Finset.sum_range_add_sum_Ico (fun r => fixedPivotCoeff r p g) (show 1≤p by omega)]
    simp [fixedPivotCoeff_invalid (r:=0) (Or.inl rfl)]

/-- All-genus source equality, with a finite horizon justified by support. -/
theorem rawFour_eq_prefix_add_omitted (g : ℕ) :
    OriginalPopulations.rawFourCount g=retainedPrefix g+
      ∑ p ∈ Finset.Ico 301 (horizon g),∑ r ∈ Finset.Ico 1 p,fixedPivotCoeff r p g := by
  rw [rawFour_eq_dynamic_box]
  unfold box
  have he : (∑ m ∈ Finset.range (horizon g),∑ r ∈ Finset.range (horizon g),
      ∑ p ∈ Finset.range (horizon g),(rawPolynomial m r p 4).coeff g)=
      ∑ p ∈ Finset.range (horizon g),∑ r ∈ Finset.Ico 1 p,fixedPivotCoeff r p g := by
    calc
      _ = ∑ m ∈ Finset.range (horizon g),∑ p ∈ Finset.range (horizon g),∑ r ∈ Finset.range (horizon g),
          (rawPolynomial m r p 4).coeff g := by
        apply Finset.sum_congr rfl; intro m hm; rw [Finset.sum_comm]
      _ = ∑ p ∈ Finset.range (horizon g),∑ r ∈ Finset.range (horizon g),∑ m ∈ Finset.range (horizon g),
          (rawPolynomial m r p 4).coeff g := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro p hp; rw [Finset.sum_comm]
      _ = _ := by
        simp_rw [multiplicity_sum_dynamic]
        apply Finset.sum_congr rfl; intro p hp
        exact pivot_sum g p (Finset.mem_range.mp hp)
  rw [he]
  exact (Finset.sum_range_add_sum_Ico _ (le_max_left 301 (g+2))).symm

lemma omitted_zero_before604 (g : ℕ) (hg : g<604) :
    (∑ p ∈ Finset.Ico 301 (horizon g),∑ r ∈ Finset.Ico 1 p,fixedPivotCoeff r p g)=0 := by
  apply Finset.sum_eq_zero; intro p hp
  apply Finset.sum_eq_zero; intro r hr
  unfold fixedPivotCoeff
  apply Finset.sum_eq_zero; intro m hm
  exact omitted_pivot_coeff_zero (by have := Finset.mem_Ico.mp hp; omega) hg

/-- The full all-genus original integer envelope from the source-exact per-pair
bound and the original scalar omitted-pivot sum. No array is needed here. -/
theorem integer_envelope_of_multiplier (B : ℕ → ℕ → ℝ)
    (hcoef : ∀ g p r,300<p → 1≤r → r<p →
      (fixedPivotCoeff r p g:ℝ) ≤ B r p*(Nat.fib g:ℝ))
    (hsum : ∀ N,(∑ p ∈ Finset.Ico 301 N,∑ r ∈ Finset.Ico 1 p,B r p) ≤ (221715:ℝ)/1000000)
    (g : ℕ) : OriginalPopulations.rawFourCount g ≤ retainedPrefix g+
      if 604≤g then 221715*Nat.fastFib g/1000000 else 0 := by
  rw [rawFour_eq_prefix_add_omitted]
  by_cases hg : g<604
  · rw [omitted_zero_before604 g hg,if_neg (show ¬604≤g by omega)]
  · rw [if_pos (show 604≤g by omega)]
    let A : ℕ := ∑ p ∈ Finset.Ico 301 (horizon g),∑ r ∈ Finset.Ico 1 p,fixedPivotCoeff r p g
    have hreal : (A:ℝ) ≤ (221715:ℝ)/1000000*(Nat.fib g:ℝ) := by
      calc
        _ = ∑ p ∈ Finset.Ico 301 (horizon g),∑ r ∈ Finset.Ico 1 p,(fixedPivotCoeff r p g:ℝ) := by
          simp only [A,Nat.cast_sum]
        _ ≤ ∑ p ∈ Finset.Ico 301 (horizon g),∑ r ∈ Finset.Ico 1 p,B r p*(Nat.fib g:ℝ) := by
          apply Finset.sum_le_sum; intro p hp
          apply Finset.sum_le_sum; intro r hr
          have hpp:=Finset.mem_Ico.mp hp
          have hrr:=Finset.mem_Ico.mp hr
          exact hcoef g p r (by omega) hrr.1 hrr.2
        _ = (∑ p ∈ Finset.Ico 301 (horizon g),∑ r ∈ Finset.Ico 1 p,B r p)*(Nat.fib g:ℝ) := by
          simp only [Finset.sum_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_right (hsum _) (Nat.cast_nonneg _)
    have hmul : (A:ℝ)*1000000 ≤ 221715*(Nat.fib g:ℝ) := by linarith
    have hnat : A*1000000 ≤ 221715*Nat.fib g := by exact_mod_cast hmul
    have hfloor : A ≤ 221715*Nat.fib g/1000000 :=
      (Nat.le_div_iff_mul_le (by decide : 0<1000000)).mpr hnat
    rw [Nat.fastFib_eq]
    exact Nat.add_le_add_left hfloor _

#print axioms rawFour_eq_prefix_add_omitted
#print axioms integer_envelope_of_multiplier
end SubmittedGenus.FiniteComparison.AllGenusOmittedSource
