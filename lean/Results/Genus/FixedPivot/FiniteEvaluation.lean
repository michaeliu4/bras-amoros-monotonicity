import Results.Genus.FixedPivot.LocallyFiniteSeries
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-! Coefficientwise evaluation at one of source-rational progression identities. -/
namespace SubmittedGenus.FixedPivot
open Polynomial
open scoped BigOperators PowerSeries.WithPiTopology
noncomputable section
set_option maxHeartbeats 600000

lemma polynomial_coefficients_hasSum (Q : Polynomial (Polynomial ℚ)) :
    HasSum (fun i => (Q.coeff i : PowerSeries ℚ)) ((Polynomial.eval (1 : Polynomial ℚ) Q : Polynomial ℚ) : PowerSeries ℚ) := by
  have he : ((Polynomial.eval (1 : Polynomial ℚ) Q : Polynomial ℚ) : PowerSeries ℚ)=∑ i∈Q.support,(Q.coeff i : PowerSeries ℚ) := by
    rw [Polynomial.eval_eq_sum]
    simp only [Polynomial.sum,one_pow,mul_one]
    change Polynomial.coeToPowerSeries.ringHom (∑ i∈Q.support,Q.coeff i)=_
    rw [map_sum]
    rfl
  rw [he]
  apply hasSum_sum_of_ne_finset_zero
  intro i hi
  rw [Polynomial.notMem_support_iff.mp hi,Polynomial.coe_zero]

lemma convolution_summable (Q : Polynomial (Polynomial ℚ)) (f : ℕ→Polynomial ℚ)
    (hcut : ∀ n k,n<k → (f k).coeff n=0) :
    Summable (fun ij : ℕ×ℕ => (Q.coeff ij.1 : PowerSeries ℚ)*(f ij.2 : PowerSeries ℚ)) := by
  rw [PowerSeries.WithPiTopology.summable_iff_summable_coeff]
  intro n
  apply HasSum.summable (a := ∑ ij∈Finset.range (Q.natDegree+1)×ˢFinset.range (n+1),
    PowerSeries.coeff n ((Q.coeff ij.1 : PowerSeries ℚ)*(f ij.2 : PowerSeries ℚ)))
  apply hasSum_sum_of_ne_finset_zero
  intro ij hij
  by_cases hq : Q.natDegree < ij.1
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hq,Polynomial.coe_zero,zero_mul,map_zero]
  · have hj : n < ij.2 := by
      have hh : ¬(ij.1<Q.natDegree+1 ∧ ij.2<n+1) := by
        simpa only [Finset.mem_product,Finset.mem_range] using hij
      omega
    rw [PowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    intro ab hab
    have he:=(Finset.mem_antidiagonal.mp hab)
    simp only [Polynomial.coeff_coe]
    rw [hcut ab.2 ij.2 (by omega),mul_zero]

/-- The y=1 operation is justified by finite coefficient support, including the
Cauchy product; there is no analytic convergence assumption. -/
theorem evaluate_formal_rational (Q A : Polynomial (Polynomial ℚ))
    (f : ℕ→Polynomial ℚ) (F : PowerSeries ℚ)
    (hcut : ∀ n k,n<k → (f k).coeff n=0)
    (hf : HasSum (fun k => (f k : PowerSeries ℚ)) F)
    (hidentity : (Q : PowerSeries (Polynomial ℚ))*PowerSeries.mk f=
      (A : PowerSeries (Polynomial ℚ))) :
    ((Polynomial.eval (1 : Polynomial ℚ) Q : Polynomial ℚ) : PowerSeries ℚ)*F=((Polynomial.eval (1 : Polynomial ℚ) A : Polynomial ℚ) : PowerSeries ℚ) := by
  have hq:=polynomial_coefficients_hasSum Q
  have hj:=convolution_summable Q f hcut
  have hv:=hq.summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal hf.summable hj
  have he : (fun n => ∑ ij∈Finset.antidiagonal n,
      (Q.coeff ij.1 : PowerSeries ℚ)*(f ij.2 : PowerSeries ℚ))=
      (fun n => (A.coeff n : PowerSeries ℚ)) := by
    funext n
    have hh:=congrArg (PowerSeries.coeff n) hidentity
    rw [PowerSeries.coeff_mul,Polynomial.coeff_coe] at hh
    simp only [Polynomial.coeff_coe,PowerSeries.coeff_mk] at hh
    rw [← hh]
    change _=Polynomial.coeToPowerSeries.ringHom (∑ ij∈Finset.antidiagonal n,Q.coeff ij.1*f ij.2)
    rw [map_sum]
    simp only [map_mul,Polynomial.coeToPowerSeries.ringHom_apply]
  calc
    _=(∑' i,(Q.coeff i : PowerSeries ℚ))*(∑' i,(f i : PowerSeries ℚ)) :=
      congrArg₂ (fun x y : PowerSeries ℚ => x*y) hq.tsum_eq.symm hf.tsum_eq.symm
    _=∑' n,∑ ij∈Finset.antidiagonal n,
      (Q.coeff ij.1 : PowerSeries ℚ)*(f ij.2 : PowerSeries ℚ) := hv
    _=∑' n,(A.coeff n : PowerSeries ℚ) := congrArg tsum he
    _=_ := (polynomial_coefficients_hasSum A).tsum_eq

end
end SubmittedGenus.FixedPivot
