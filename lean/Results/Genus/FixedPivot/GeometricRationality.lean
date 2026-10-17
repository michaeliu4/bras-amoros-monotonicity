import Results.Genus.FixedPivot.RecurrenceAlgebra
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Trunc

/-! Exact formal progression generating functions for the proved finite source modes. -/
namespace SubmittedGenus.FixedPivot
open scoped BigOperators
noncomputable section
section Ring
variable {R I : Type*} [CommRing R] [Fintype I]

def geometricSeries (rate : R) : PowerSeries R := PowerSeries.mk (fun n => rate^n)

def linearModeDenominator (rate : R) : Polynomial R := 1-Polynomial.C rate*Polynomial.X

lemma linearModeDenominator_geometric (rate : R) :
    (linearModeDenominator rate : PowerSeries R)*geometricSeries rate=1 := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp [linearModeDenominator,geometricSeries]
  | succ n =>
    simp only [linearModeDenominator,Polynomial.coe_sub,Polynomial.coe_one,Polynomial.coe_mul,
      Polynomial.coe_C,Polynomial.coe_X,sub_mul,one_mul,mul_assoc,map_sub,
      PowerSeries.coeff_C_mul,PowerSeries.coeff_succ_X_mul,geometricSeries,
      PowerSeries.coeff_mk,PowerSeries.coeff_one,show n+1≠0 by omega,ite_false,pow_succ]
    ring

def modeDenominator {d : ℕ} (rates : Fin (d+1)→R) : Polynomial R :=
  ∏ j,linearModeDenominator (rates j)

def modeNumerator {d : ℕ} (rates : Fin (d+1)→R) (A : I→R) (index : I→Fin (d+1)) : Polynomial R :=
  ∑ i,Polynomial.C (A i)*∏ j ∈ Finset.univ.erase (index i),linearModeDenominator (rates j)

def finiteModeSeries {d : ℕ} (rates : Fin (d+1)→R) (A : I→R) (index : I→Fin (d+1)) : PowerSeries R :=
  PowerSeries.mk (fun n => ∑ i,A i*(rates (index i))^n)

lemma finiteModeSeries_eq {d : ℕ} (rates : Fin (d+1)→R) (A : I→R) (index : I→Fin (d+1)) :
    finiteModeSeries rates A index=∑ i,PowerSeries.C (A i)*geometricSeries (rates (index i)) := by
  apply PowerSeries.ext
  intro n
  simp [finiteModeSeries,geometricSeries]

/-- A chosen factor cancels each actual exponential; duplicated rates are harmless. -/
lemma modeDenominator_mul_geometric {d : ℕ} (rates : Fin (d+1)→R) (i : Fin (d+1)) :
    (modeDenominator rates : PowerSeries R)*geometricSeries (rates i)=
      ((∏ j ∈ Finset.univ.erase i,linearModeDenominator (rates j) : Polynomial R) : PowerSeries R) := by
  classical
  unfold modeDenominator
  rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i),Finset.sdiff_singleton_eq_erase,
    Polynomial.coe_mul,mul_right_comm,linearModeDenominator_geometric,one_mul]

/-- The progression variable is formal: this proof requires no convergence or
positivity of amplitudes and is valid from the initial phase n=0. -/
theorem finiteModeSeries_rational {d : ℕ} (rates : Fin (d+1)→R) (A : I→R) (index : I→Fin (d+1)) :
    (modeDenominator rates : PowerSeries R)*finiteModeSeries rates A index=(modeNumerator rates A index : PowerSeries R) := by
  rw [finiteModeSeries_eq,Finset.mul_sum]
  unfold modeNumerator
  change _=Polynomial.coeToPowerSeries.ringHom (∑ i,Polynomial.C (A i)*
    ∏ j ∈ Finset.univ.erase (index i),linearModeDenominator (rates j))
  rw [map_sum]
  simp only [Polynomial.coeToPowerSeries.ringHom_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [← mul_assoc,mul_comm (modeDenominator rates : PowerSeries R),mul_assoc,
    modeDenominator_mul_geometric,Polynomial.coe_mul,Polynomial.coe_C]

end Ring
end
end SubmittedGenus.FixedPivot
