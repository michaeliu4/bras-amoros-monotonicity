import Results.Genus.FiniteArithmetic.Reservoir.PrefixSeries
import Mathlib.RingTheory.PowerSeries.PiTopology

namespace SubmittedGenus.FiniteArithmetic.Reservoir

open PowerSeries
open scoped BigOperators PowerSeries.WithPiTopology
noncomputable section

/-- This formal sum is coefficientwise finite: the n-th summand starts at
weight n. No analytic evaluation of a divergent series is involved. -/
theorem gradedFamily_summable (K : ℕ → PowerSeries ℤ) :
    Summable (fun n => X^n*K n) := by
  apply (PowerSeries.WithPiTopology.summable_iff_summable_coeff ℤ).mpr
  intro g
  apply summable_of_ne_finset_zero (s := Finset.range (g+1))
  intro n hn
  have hn' : ¬ n≤g := by simpa using hn
  rw [coeff_X_pow_mul',if_neg hn']

def gradedTransform (K : ℕ → PowerSeries ℤ) : PowerSeries ℤ := ∑' n, X^n*K n

theorem gradedTransform_coeff (K : ℕ → PowerSeries ℤ) (g : ℕ) :
    coeff g (gradedTransform K) = ∑ n : Fin (g+1), coeff (g-n.val) (K n.val) := by
  have h := (PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff ℤ).mp (gradedFamily_summable K).hasSum g
  unfold gradedTransform
  rw [←h.tsum_eq]
  rw [tsum_eq_sum (s := Finset.range (g+1))]
  · rw [←Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro n _
    rw [coeff_X_pow_mul',if_pos (by omega)]
  · intro n hn
    have hn' : ¬ n≤g := by simpa using hn
    rw [coeff_X_pow_mul',if_neg hn']

theorem gradedTransform_add (K L : ℕ → PowerSeries ℤ) :
    gradedTransform (fun n => K n+L n) = gradedTransform K+gradedTransform L := by
  simp only [gradedTransform,mul_add]
  exact (gradedFamily_summable K).tsum_add (gradedFamily_summable L)

theorem gradedTransform_sub (K L : ℕ → PowerSeries ℤ) :
    gradedTransform (fun n => K n-L n) = gradedTransform K-gradedTransform L := by
  simp only [gradedTransform,mul_sub]
  exact (gradedFamily_summable K).tsum_sub (gradedFamily_summable L)

theorem gradedTransform_mul (K : ℕ → PowerSeries ℤ) (a : PowerSeries ℤ) :
    gradedTransform (fun n => K n*a) = gradedTransform K*a := by
  unfold gradedTransform
  simp only [←mul_assoc]
  exact (HasSum.mul_right a (gradedFamily_summable K).hasSum).tsum_eq

theorem gradedTransform_congr {K L : ℕ → PowerSeries ℤ} (h : ∀ n,K n=L n) :
    gradedTransform K=gradedTransform L := by congr; exact funext h

theorem gradedTransform_one (P : ℕ → Type) [∀ n,Fintype (P n)] :
    gradedTransform (fun n => ∑ _p : P n, (1 : PowerSeries ℤ)) = Graded.series P := by
  apply PowerSeries.ext
  intro g
  rw [gradedTransform_coeff,Graded.coeff_series]
  have he (n : Fin (g+1)) : coeff (g-n.val) (∑ _p : P n.val, (1 : PowerSeries ℤ)) =
      if n.val=g then (Fintype.card (P n.val) : ℤ) else 0 := by
    rw [map_sum]
    by_cases hn : n.val=g
    · simp [hn]
    · have hn' : g-n.val≠0 := by have := n.isLt; omega
      simp [hn,hn']
  simp_rw [he]
  rw [Finset.sum_eq_single ⟨g,by omega⟩]
  · simp
  · intro b hb hne
    have hn : b.val≠g := by intro h; apply hne; exact Fin.ext h
    simp [hn]
  · simp

#print axioms gradedTransform_mul
#print axioms gradedTransform_one
end
end SubmittedGenus.FiniteArithmetic.Reservoir
