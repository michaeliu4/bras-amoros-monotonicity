import Results.Genus.FiniteArithmetic.Reservoir.GradedTransform
import Results.Genus.FiniteArithmetic.Reservoir.PositiveEvaluation
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace SubmittedGenus.FiniteArithmetic.Reservoir
open PowerSeries Analytic
open scoped BigOperators
noncomputable section

/-- Reindex the coefficientwise-finite triangular sum by its prefix and
residual weights. This is the analytic counting bijection, not a convergence
assumption about a formal rational expression. -/
def diagonalEquiv : (Σ g : ℕ, Fin (g+1)) ≃ ℕ×ℕ where
  toFun x := (x.2.val,x.1-x.2.val)
  invFun x := ⟨x.1+x.2,⟨x.1,by omega⟩⟩
  left_inv x := by
    rcases x with ⟨g,⟨n,hn⟩⟩
    have h : n+(g-n)=g := by omega
    apply Sigma.ext h
    exact (Fin.heq_ext_iff (congrArg (fun n=>n+1) h)).mpr rfl
  right_inv x := by rcases x with ⟨n,k⟩; simp

def weightedKernel (r : ℝ) (K : ℕ→PowerSeries ℤ) (p : ℕ×ℕ) : ℝ :=
  r^p.1*(realCoeff (K p.1) p.2*r^p.2)

theorem weightedKernel_nonneg {r : ℝ} (hr : 0≤r) {K : ℕ→PowerSeries ℤ}
    (hK : ∀ n k,0≤coeff k (K n)) (p : ℕ×ℕ) : 0≤weightedKernel r K p := by
  unfold weightedKernel realCoeff
  have h := hK p.1 p.2
  positivity

theorem transform_coeff_nonneg {K : ℕ→PowerSeries ℤ} (hK : ∀ n k,0≤coeff k (K n)) (g : ℕ) :
    0≤coeff g (gradedTransform K) := by
  rw [gradedTransform_coeff]
  exact Finset.sum_nonneg (fun n _=>hK n.val (g-n.val))

theorem weighted_transform_diagonal (r : ℝ) (K : ℕ→PowerSeries ℤ) (g : ℕ) :
    realCoeff (gradedTransform K) g*r^g =
      ∑ i : Fin (g+1),weightedKernel r K (i.val,g-i.val) := by
  unfold realCoeff
  rw [gradedTransform_coeff]
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  unfold weightedKernel realCoeff
  have he : i.val+(g-i.val)=g := by have := i.isLt; omega
  have hp : r^g=r^i.val*r^(g-i.val) := by rw [←pow_add,he]
  rw [hp]
  ring

theorem kernel_summable_of_transform {r : ℝ} (hr : 0≤r) {K : ℕ→PowerSeries ℤ}
    (hK : ∀ n k,0≤coeff k (K n)) (hs : SummableAt r (gradedTransform K)) :
    Summable (weightedKernel r K) := by
  have hd : Summable (fun g=>∑ i : Fin (g+1),weightedKernel r K (i.val,g-i.val)) :=
    (hs.summable hr).congr (weighted_transform_diagonal r K)
  have hσ : Summable (fun x : Σ g : ℕ,Fin (g+1)=>weightedKernel r K (x.2.val,x.1-x.2.val)) := by
    apply (summable_sigma_of_nonneg (fun x=>weightedKernel_nonneg hr hK _)).mpr
    exact ⟨fun _=>(hasSum_fintype _).summable,by simpa only [tsum_fintype] using hd⟩
  exact diagonalEquiv.summable_iff.mp hσ

theorem transform_summable_of_kernel {r : ℝ} (hr : 0≤r) {K : ℕ→PowerSeries ℤ}
    (hK : ∀ n k,0≤coeff k (K n)) (hs : Summable (weightedKernel r K)) :
    SummableAt r (gradedTransform K) := by
  have hσ : Summable (fun x : Σ g : ℕ,Fin (g+1)=>weightedKernel r K (x.2.val,x.1-x.2.val)) :=
    diagonalEquiv.summable_iff.mpr hs
  have hd := ((summable_sigma_of_nonneg (fun x=>weightedKernel_nonneg hr hK _)).mp hσ).2
  change Summable (fun g=>|realCoeff (gradedTransform K) g| * r^g)
  apply hd.congr
  intro g
  have hn : 0≤realCoeff (gradedTransform K) g := by
    unfold realCoeff
    exact_mod_cast transform_coeff_nonneg hK g
  rw [abs_of_nonneg hn,weighted_transform_diagonal]
  exact tsum_fintype _

theorem kernel_row_mass (r : ℝ) (K : ℕ→PowerSeries ℤ) (n : ℕ) :
    (∑' k,weightedKernel r K (n,k))=r^n*massAt r (K n) := by
  unfold weightedKernel massAt
  exact tsum_mul_left (f := fun k=>realCoeff (K n) k*r^k) (a := r^n)

theorem transform_mass_eq_rows {r : ℝ} (hr : 0≤r) {K : ℕ→PowerSeries ℤ}
    (hK : ∀ n k,0≤coeff k (K n)) (hs : SummableAt r (gradedTransform K)) :
    massAt r (gradedTransform K)=∑' n,r^n*massAt r (K n) := by
  have hp := kernel_summable_of_transform hr hK hs
  have hσ : Summable (fun x : Σ g : ℕ,Fin (g+1)=>weightedKernel r K (x.2.val,x.1-x.2.val)) :=
    diagonalEquiv.summable_iff.mpr hp
  calc
    _ = ∑' g,∑' i : Fin (g+1),weightedKernel r K (i.val,g-i.val) := by
      apply tsum_congr
      intro g
      rw [weighted_transform_diagonal,tsum_fintype]
    _ = ∑' x : Σ g : ℕ,Fin (g+1),weightedKernel r K (x.2.val,x.1-x.2.val) := (hσ.tsum_sigma' (fun _=>(hasSum_fintype _).summable)).symm
    _ = ∑' p : ℕ×ℕ,weightedKernel r K p := diagonalEquiv.tsum_eq _
    _ = ∑' n,∑' k,weightedKernel r K (n,k) := hp.tsum_prod
    _ = _ := tsum_congr (kernel_row_mass r K)

/-- Tonelli-style domination for independently specified nonnegative kernels.
This is the convergence gate used for the original failure operator when
c(5/8)>1, where a geometric expansion of (1-c)^(-1) would be invalid. -/
theorem transform_summable_of_row_domination {r C : ℝ} (hr : 0≤r) (hC : 0≤C)
    {K L : ℕ→PowerSeries ℤ} (hK : ∀ n k,0≤coeff k (K n))
    (hL : ∀ n k,0≤coeff k (L n)) (hKs : ∀ n,SummableAt r (K n))
    (hrow : ∀ n,massAt r (K n)≤C*massAt r (L n))
    (hLs : SummableAt r (gradedTransform L)) : SummableAt r (gradedTransform K) := by
  have hLp := kernel_summable_of_transform hr hL hLs
  have hLrows := ((summable_prod_of_nonneg (weightedKernel_nonneg hr hL)).mp hLp).2
  have hKrows : Summable (fun n=>∑' k,weightedKernel r K (n,k)) := by
    apply Summable.of_nonneg_of_le (fun n=>tsum_nonneg (fun k=>weightedKernel_nonneg hr hK _))
      (fun n=>?_) (hLrows.mul_left C)
    rw [kernel_row_mass,kernel_row_mass]
    calc
      _ ≤ r^n*(C*massAt r (L n)) := mul_le_mul_of_nonneg_left (hrow n) (pow_nonneg hr n)
      _ = _ := by ring
  apply transform_summable_of_kernel hr hK
  apply (summable_prod_of_nonneg (weightedKernel_nonneg hr hK)).mpr
  refine ⟨?_,hKrows⟩
  intro n
  exact ((hKs n).summable hr).mul_left (r^n)

#print axioms transform_mass_eq_rows
#print axioms transform_summable_of_row_domination
end
end SubmittedGenus.FiniteArithmetic.Reservoir
