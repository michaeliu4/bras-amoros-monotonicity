import Results.Genus.FiniteComparison.SourceBoxes
import Results.Genus.RawGraph.SignedCounterexample

noncomputable section
open scoped BigOperators
namespace SubmittedGenus.FiniteComparison.OmittedSource
open RawGraph RawGraph.SignedCounterexample SourceBoxes

lemma fixedPivotCoeff_invalid {r p g : ℕ} (h : r=0 ∨ p≤r) : fixedPivotCoeff r p g=0 := by
  unfold fixedPivotCoeff
  apply Finset.sum_eq_zero; intro m hm
  have hi : ¬Parameters m r p 4 := by unfold Parameters; omega
  simp [rawPolynomial_invalid hi]

lemma multiplicity_sum (r p g : ℕ) (hg : g≤897) :
    (∑ m ∈ Finset.range 598,(rawPolynomial m r p 4).coeff g)=fixedPivotCoeff r p g := by
  unfold fixedPivotCoeff
  apply sum_range_same
  · intro m hm
    apply rawPolynomial_coeff_zero_of_support
    omega
  · intro m hm
    exact coeff_zero_of_multiplicity (by omega)

lemma retained_partial (g : ℕ) :
    (∑ m ∈ Finset.range 598,∑ r ∈ Finset.range 598,∑ p ∈ Finset.range 301,
      (rawPolynomial m r p 4).coeff g)=retainedFour g := by
  unfold retainedFour
  apply Finset.sum_congr rfl; intro m hm
  apply sum_range_same
  · intro r hr; apply Finset.sum_eq_zero; intro p hp
    have hp':=Finset.mem_range.mp hp
    have hi : ¬Parameters m r p 4 := by unfold Parameters; omega
    simp [rawPolynomial_invalid hi]
  · intro r hr; apply Finset.sum_eq_zero; intro p hp
    have hp':=Finset.mem_range.mp hp
    have hi : ¬Parameters m r p 4 := by unfold Parameters; omega
    simp [rawPolynomial_invalid hi]

lemma tail_reindex (g : ℕ) (hg : g≤897) :
    (∑ m ∈ Finset.range 598,∑ r ∈ Finset.range 598,∑ p ∈ Finset.Ico 301 598,
      (rawPolynomial m r p 4).coeff g)=
    ∑ p ∈ Finset.Ico 301 598,∑ r ∈ Finset.Ico 1 p,fixedPivotCoeff r p g := by
  calc
    _ = ∑ m ∈ Finset.range 598,∑ p ∈ Finset.Ico 301 598,∑ r ∈ Finset.range 598,
        (rawPolynomial m r p 4).coeff g := by
      apply Finset.sum_congr rfl; intro m hm; rw [Finset.sum_comm]
    _ = ∑ p ∈ Finset.Ico 301 598,∑ r ∈ Finset.range 598,∑ m ∈ Finset.range 598,
        (rawPolynomial m r p 4).coeff g := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro p hp; rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl; intro p hp
      simp_rw [multiplicity_sum _ _ _ hg]
      have hp':=Finset.mem_Ico.mp hp
      have he : (∑ r ∈ Finset.range 598,fixedPivotCoeff r p g)=
          ∑ r ∈ Finset.range p,fixedPivotCoeff r p g := by
        apply sum_range_same
        · intro r hr; exact fixedPivotCoeff_invalid (Or.inr (by omega))
        · intro r hr; exact fixedPivotCoeff_invalid (Or.inr hr)
      rw [he,←Finset.sum_range_add_sum_Ico (fun r => fixedPivotCoeff r p g) (show 1≤p by omega)]
      simp [fixedPivotCoeff_invalid (r:=0) (Or.inl rfl)]

/-- Source-exact partition into the retained original finite polynomial and
all omitted pivots that can contribute through genus897. -/
theorem rawFour_eq_retained_add_omitted (g : ℕ) (hg : g≤897) :
    OriginalPopulations.rawFourCount g = retainedFour g+
      ∑ p ∈ Finset.Ico 301 598,∑ r ∈ Finset.Ico 1 p,fixedPivotCoeff r p g := by
  rw [rawFourCount_eq_box g hg]
  unfold box
  have hsplit : ∀ m r,(∑ p ∈ Finset.range 598,(rawPolynomial m r p 4).coeff g)=
      (∑ p ∈ Finset.range 301,(rawPolynomial m r p 4).coeff g)+
      ∑ p ∈ Finset.Ico 301 598,(rawPolynomial m r p 4).coeff g := by
    intro m r
    exact (Finset.sum_range_add_sum_Ico _ (by decide : 301≤598)).symm
  simp_rw [hsplit,Finset.sum_add_distrib]
  rw [retained_partial,tail_reindex g hg]

/-- The exact original finite-source floor conversion. Only the actual
per-pair source coefficient bound and its scalar pivot-sum bound remain. -/
theorem rawFour_le_retained_of_multiplier (g : ℕ) (hg : g≤897) (B : ℕ → ℕ → ℝ)
    (hcoef : ∀ p ∈ Finset.Ico 301 598,∀ r ∈ Finset.Ico 1 p,
      (fixedPivotCoeff r p g:ℝ) ≤ B r p*(Nat.fib g:ℝ))
    (hsum : (∑ p ∈ Finset.Ico 301 598,∑ r ∈ Finset.Ico 1 p,B r p) ≤ (221715:ℝ)/1000000) :
    OriginalPopulations.rawFourCount g ≤ retainedFour g+221715*Nat.fastFib g/1000000 := by
  let A : ℕ := ∑ p ∈ Finset.Ico 301 598,∑ r ∈ Finset.Ico 1 p,fixedPivotCoeff r p g
  have hreal : (A:ℝ) ≤ (221715:ℝ)/1000000*(Nat.fib g:ℝ) := by
    calc
      _ = ∑ p ∈ Finset.Ico 301 598,∑ r ∈ Finset.Ico 1 p,(fixedPivotCoeff r p g:ℝ) := by
        simp only [A,Nat.cast_sum]
      _ ≤ ∑ p ∈ Finset.Ico 301 598,∑ r ∈ Finset.Ico 1 p,B r p*(Nat.fib g:ℝ) := by
        apply Finset.sum_le_sum; intro p hp
        apply Finset.sum_le_sum; intro r hr
        exact hcoef p hp r hr
      _ = (∑ p ∈ Finset.Ico 301 598,∑ r ∈ Finset.Ico 1 p,B r p)*(Nat.fib g:ℝ) := by
        simp only [Finset.sum_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hsum (Nat.cast_nonneg _)
  have hmul : (A:ℝ)*1000000 ≤ 221715*(Nat.fib g:ℝ) := by linarith
  have hnat : A*1000000 ≤ 221715*Nat.fib g := by exact_mod_cast hmul
  have hfloor : A ≤ 221715*Nat.fib g/1000000 :=
    (Nat.le_div_iff_mul_le (by decide : 0<1000000)).mpr hnat
  rw [rawFour_eq_retained_add_omitted g hg,Nat.fastFib_eq]
  exact Nat.add_le_add_left hfloor _

#print axioms rawFour_eq_retained_add_omitted
#print axioms rawFour_le_retained_of_multiplier
end SubmittedGenus.FiniteComparison.OmittedSource
