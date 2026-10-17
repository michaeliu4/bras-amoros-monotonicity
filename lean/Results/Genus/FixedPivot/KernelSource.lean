import Results.Genus.FixedPivot.KernelModes
import Results.Genus.RawGraph.Factorization

/-! Direct finite-source interpretation of arbitrary carry endpoint restrictions. -/
namespace SubmittedGenus.FixedPivot
open scoped BigOperators
section Ring
variable {R : Type*} [CommRing R]

/-- Both endpoint factors are evaluated on actual physical endpoint states. -/
theorem weightedCarryKernel_eq_source (z : R) (n : ℕ) (start finish : Fin 3→R) :
    weightedCarryKernel z n start finish=
      ∑ y : Fin (n+1)→Fin 3, start (y 0)*
        RawGraph.Transfer.sourceTerm n (fun _ => carryWeight z)
          (fun _ => carryCompatibility) finish y := by
  rw [RawGraph.Transfer.sum_cons]
  unfold weightedCarryKernel
  apply Finset.sum_congr rfl
  intro i _
  simp only [Fin.cons_zero,← Finset.mul_sum]
  rw [← RawGraph.Transfer.fixedSource,← RawGraph.Transfer.run_eq_fixedSource,
    raw_run_eq_carryPower]
  ring

/-- Exact source word constraints, including n=0 when the endpoints coincide. -/
def CarryKernelAllowed (n : ℕ) (start finish : Fin 3→Prop) (y : Fin (n+1)→Fin 3) : Prop :=
  start (y 0) ∧ finish (y (Fin.last n)) ∧
    ∀ j : Fin n,3≤(y j.castSucc).val+1+((y j.succ).val+1)

instance (n : ℕ) (start finish : Fin 3→Prop) [DecidablePred start] [DecidablePred finish]
    (y : Fin (n+1)→Fin 3) : Decidable (CarryKernelAllowed n start finish y) := by
  unfold CarryKernelAllowed
  infer_instance

/-- Each vertex contributes z to the power of its physical coordinate value once. -/
theorem weightedCarryKernel_gated_source (z : R) (n : ℕ) (start finish : Fin 3→Prop)
    [DecidablePred start] [DecidablePred finish] :
    weightedCarryKernel z n (fun i => if start i then 1 else 0)
      (fun i => if finish i then 1 else 0)=
      ∑ y : Fin (n+1)→Fin 3,
        if CarryKernelAllowed n start finish y then z^(∑ i : Fin (n+1), ((y i).val+1)) else 0 := by
  classical
  rw [weightedCarryKernel_eq_source]
  apply Finset.sum_congr rfl
  intro y _
  unfold RawGraph.Transfer.sourceTerm carryWeight carryCompatibility
  rw [Finset.prod_pow_eq_pow_sum,RawGraph.Factorization.prod_gate]
  unfold CarryKernelAllowed
  split_ifs <;> simp_all

end Ring
end SubmittedGenus.FixedPivot
