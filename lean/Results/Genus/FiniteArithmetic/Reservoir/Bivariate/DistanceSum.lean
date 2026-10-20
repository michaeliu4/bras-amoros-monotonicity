import Results.Genus.FiniteArithmetic.Reservoir.Bivariate.Coefficients

namespace SubmittedGenus.FiniteArithmetic.Reservoir.Bivariate
open PowerSeries
open scoped BigOperators PowerSeries.WithPiTopology
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The original F_d(z) obtained by fixing the distance degree. -/
def distanceSlice (F : PowerSeries (Polynomial ℤ)) (d : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk (fun n => (PowerSeries.coeff n F).coeff d)

/-- All distances able to contribute through a fixed weight. -/
def distanceSupport (F : PowerSeries (Polynomial ℤ)) (g : ℕ) : Finset ℕ :=
  (Finset.range (g+1)).biUnion (fun n => (PowerSeries.coeff n F).support)

theorem support_subset_distanceSupport (F : PowerSeries (Polynomial ℤ)) {n g : ℕ}
    (hn : n≤g) : (PowerSeries.coeff n F).support ⊆ distanceSupport F g := by
  intro d hd
  exact Finset.mem_biUnion.mpr ⟨n,Finset.mem_range.mpr (by omega),hd⟩

theorem distanceWeighted_coeff (F : PowerSeries (Polynomial ℤ)) (K : ℕ → PowerSeries ℤ) (d g : ℕ) :
    PowerSeries.coeff g (distanceSlice F d*K d) =
      ∑ n : Fin (g+1), (PowerSeries.coeff n.val F).coeff d *
        PowerSeries.coeff (g-n.val) (K d) := by
  rw [PowerSeries.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    ←Fin.sum_univ_eq_sum_range]
  simp only [distanceSlice,PowerSeries.coeff_mk]

theorem distanceWeighted_coeff_zero (F : PowerSeries (Polynomial ℤ)) (K : ℕ → PowerSeries ℤ) (d g : ℕ)
    (hd : d ∉ distanceSupport F g) :
    PowerSeries.coeff g (distanceSlice F d*K d)=0 := by
  rw [distanceWeighted_coeff]
  apply Finset.sum_eq_zero
  intro n hn
  have hp : d ∉ (PowerSeries.coeff n.val F).support := by
    intro hp
    exact hd (support_subset_distanceSupport F (by have := n.isLt; omega) hp)
  have hz : (PowerSeries.coeff n.val F).coeff d=0 := by
    simpa only [Polynomial.mem_support_iff,not_not] using hp
  rw [hz,zero_mul]

theorem distanceWeighted_summable (F : PowerSeries (Polynomial ℤ)) (K : ℕ → PowerSeries ℤ) :
    Summable (fun d => distanceSlice F d*K d) := by
  apply (PowerSeries.WithPiTopology.summable_iff_summable_coeff ℤ).mpr
  intro g
  apply summable_of_ne_finset_zero (s := distanceSupport F g)
  intro d hd
  exact distanceWeighted_coeff_zero F K d g hd

theorem distanceWeighted_sum_coeff (F : PowerSeries (Polynomial ℤ)) (K : ℕ → PowerSeries ℤ) (g : ℕ) :
    PowerSeries.coeff g (∑' d,distanceSlice F d*K d) =
      ∑ n : Fin (g+1), ∑ d ∈ (PowerSeries.coeff n.val F).support,
        (PowerSeries.coeff n.val F).coeff d *
          PowerSeries.coeff (g-n.val) (K d) := by
  have h := (PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff ℤ).mp
    (distanceWeighted_summable F K).hasSum g
  rw [←h.tsum_eq,tsum_eq_sum (s := distanceSupport F g)]
  · simp_rw [distanceWeighted_coeff]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n hn
    symm
    apply Finset.sum_subset (support_subset_distanceSupport F (by have := n.isLt; omega))
    intro d hd hdn
    have hz : (PowerSeries.coeff n.val F).coeff d=0 := by
      simpa only [Polynomial.mem_support_iff,not_not] using hdn
    rw [hz,zero_mul]
  · intro d hd
    exact distanceWeighted_coeff_zero F K d g hd

/-- Literal F(z,t)=Σ_d F_d(z)t^d, valid even when t has a nonzero
constant coefficient, because each outer weight has finite distance support. -/
theorem specialize_distanceSum (F : PowerSeries (Polynomial ℤ)) (t : PowerSeries ℤ) :
    specialize F t=∑' d,distanceSlice F d*t^d := by
  apply PowerSeries.ext
  intro g
  rw [specialize,gradedTransform_coeff,distanceWeighted_sum_coeff]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [Polynomial.eval₂_eq_sum,Polynomial.sum_def,map_sum,PowerSeries.coeff_C_mul]

/-- Literal original z Σ_d F_d Q_d expression. Formal summability is proved
from local finiteness, with no positivity or analytic convergence premise. -/
theorem failureOperator_distanceSum (F : PowerSeries (Polynomial ℤ)) :
    failureOperator F=X*(∑' d,distanceSlice F d*failureTailSeries d) := by
  apply PowerSeries.ext
  intro g
  cases g with
  | zero => simp
  | succ g =>
    rw [failureOperator_coeff_succ,PowerSeries.coeff_succ_X_mul,distanceWeighted_sum_coeff]

#print axioms distanceWeighted_summable
#print axioms failureOperator_distanceSum
end
end SubmittedGenus.FiniteArithmetic.Reservoir.Bivariate
