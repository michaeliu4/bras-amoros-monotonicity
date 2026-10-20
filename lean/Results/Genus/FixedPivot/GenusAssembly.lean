import Results.Genus.FixedPivot.PhaseGenerating
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-! Assembly of the original finite prefix and all multiplicity progressions. -/
namespace SubmittedGenus.FixedPivot
open Polynomial
open scoped BigOperators PowerSeries.WithPiTopology
noncomputable section

lemma rawPolynomialQ_zero_of_le_p {m r p : ℕ} (hm : m≤p) : rawPolynomialQ m r p=0 := by
  unfold rawPolynomialQ
  rw [RawGraph.rawPolynomial_invalid (by unfold RawGraph.Parameters; omega),Polynomial.map_zero]

lemma raw_prefix_eq (r p : ℕ) :
    (∑ m∈Finset.range (2*p+1),(rawPolynomialQ m r p : PowerSeries ℚ))=
      ((∑ m∈Finset.Icc (p+1) (2*p),rawPolynomialQ m r p : Polynomial ℚ) : PowerSeries ℚ) := by
  change _=Polynomial.coeToPowerSeries.ringHom (∑ m∈Finset.Icc (p+1) (2*p),rawPolynomialQ m r p)
  rw [map_sum]
  symm
  apply Finset.sum_subset
  · intro m hm
    simp only [Finset.mem_Icc,Finset.mem_range] at *
    omega
  · intro m hm hn
    simp only [Finset.mem_Icc,Finset.mem_range] at *
    rw [rawPolynomialQ_zero_of_le_p (by omega),map_zero]

lemma sum_fin_succ_eq_Icc {R : Type*} [AddCommMonoid R] (f : ℕ→R) (d : ℕ) :
    (∑ s : Fin d,f (s.val+1))=∑ s∈Finset.Icc 1 d,f s := by
  rw [show (∑ s : Fin d,f (s.val+1))=∑ s∈Finset.range d,f (s+1) from
    Fin.sum_univ_eq_sum_range (fun s => f (s+1)) d]
  apply Finset.sum_bij (fun s _ => s+1)
  · intro s hs
    simp only [Finset.mem_range,Finset.mem_Icc] at *
    omega
  · intro a ha b hb he
    omega
  · intro s hs
    refine ⟨s-1,?_,?_⟩ <;> simp only [Finset.mem_range,Finset.mem_Icc] at * <;> omega
  · intro s _
    rfl

/-- Exact residue-class splitting of the complete source sum. -/
theorem fixedPivotSeriesQ_phases (r p d : ℕ) (hd : 0<d) :
    fixedPivotSeriesQ r p=
      ((∑ m∈Finset.Icc (p+1) (2*p),rawPolynomialQ m r p : Polynomial ℚ) : PowerSeries ℚ)+
      ∑ s∈Finset.Icc 1 d,locallyFinitePolynomialSum (fun k => rawPolynomialQ (2*p+s+k*d) r p) := by
  letI : NeZero d:=⟨by omega⟩
  let e : ℕ≃Fin d×ℕ:=(Nat.divModEquiv d).trans (Equiv.prodComm _ _)
  have hf:=fixedPivotSeriesQ_hasSum r p
  have ht : Summable (fun n => (rawPolynomialQ (n+(2*p+1)) r p : PowerSeries ℚ)) :=
    (summable_nat_add_iff (2*p+1)).mpr hf.summable
  have he : (fun sk : Fin d×ℕ => (rawPolynomialQ (e.symm sk+(2*p+1)) r p : PowerSeries ℚ))=
      (fun sk : Fin d×ℕ => (rawPolynomialQ (2*p+(sk.1.val+1)+sk.2*d) r p : PowerSeries ℚ)) := by
    funext sk
    congr 2
    change sk.2*d+sk.1.val+(2*p+1)=2*p+(sk.1.val+1)+sk.2*d
    omega
  have hp:=e.symm.summable_iff.mpr ht
  change Summable (fun sk : Fin d×ℕ => (rawPolynomialQ (e.symm sk+(2*p+1)) r p : PowerSeries ℚ)) at hp
  rw [he] at hp
  have hs : (∑' n,(rawPolynomialQ (n+(2*p+1)) r p : PowerSeries ℚ))=
      ∑ s : Fin d,locallyFinitePolynomialSum (fun k => rawPolynomialQ (2*p+(s.val+1)+k*d) r p) := by
    calc
      _=∑' sk : Fin d×ℕ,(rawPolynomialQ (e.symm sk+(2*p+1)) r p : PowerSeries ℚ) :=
        (e.symm.tsum_eq _).symm
      _=∑' sk : Fin d×ℕ,(rawPolynomialQ (2*p+(sk.1.val+1)+sk.2*d) r p : PowerSeries ℚ) :=
        congrArg tsum he
      _=_ := by
        rw [hp.tsum_prod' (fun s => (rawProgression_hasSum (2*p+(s.val+1)) r p d hd).summable),tsum_fintype]
        apply Finset.sum_congr rfl
        intro s _
        exact (rawProgression_hasSum (2*p+(s.val+1)) r p d hd).tsum_eq
  have hh:=hf.summable.sum_add_tsum_nat_add (2*p+1)
  rw [hf.tsum_eq,raw_prefix_eq,hs] at hh
  rw [sum_fin_succ_eq_Icc (fun s => locallyFinitePolynomialSum
    (fun k => rawPolynomialQ (2*p+s+k*d) r p)) d] at hh
  exact hh.symm

/-- The paper's initial-data numerator represents the complete original fixed-pivot series. -/
theorem originalInitialNumerator_identity {r d : ℕ} (hr : 0<r) (hd : 0<d) :
    ((Polynomial.eval (1 : Polynomial ℚ) (rationalSourceQ d) : Polynomial ℚ) : PowerSeries ℚ)*
      fixedPivotSeriesQ r (r+d)=
      (originalInitialNumerator r (r+d) d : PowerSeries ℚ) := by
  rw [fixedPivotSeriesQ_phases r (r+d) d hd,mul_add,Finset.mul_sum]
  have hs : (∑ s∈Finset.Icc 1 d,
      ((Polynomial.eval (1 : Polynomial ℚ) (rationalSourceQ d) : Polynomial ℚ) : PowerSeries ℚ)*
        locallyFinitePolynomialSum (fun k => rawPolynomialQ (2*(r+d)+s+k*d) r (r+d)))=
      ∑ s∈Finset.Icc 1 d,(phaseInitialNumerator r (r+d) d s : PowerSeries ℚ) := by
    apply Finset.sum_congr rfl
    intro s hs
    exact phaseInitialNumerator_identity hr hd (by have:=Finset.mem_Icc.mp hs; omega)
  rw [hs]
  unfold originalInitialNumerator
  rw [Polynomial.coe_add,Polynomial.coe_mul,mul_comm]
  congr 1
  change _=Polynomial.coeToPowerSeries.ringHom (∑ s∈Finset.Icc 1 d,phaseInitialNumerator r (r+d) d s)
  rw [map_sum]
  rfl

end
end SubmittedGenus.FixedPivot
