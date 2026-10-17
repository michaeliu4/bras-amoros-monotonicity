import Results.Genus.GoldenTail.QuadraticTail

/-! Exact odd/even interval grouping used by the original omitted-pivot sum. -/
open scoped BigOperators
namespace SubmittedGenus.GoldenTail

/-- Pair every odd pivot2k+1 with its following even pivot2k+2. -/
lemma sum_Ico_odd_even {A : Type*} [AddCommMonoid A] (f : ℕ → A) (K M : ℕ) :
    (∑ p ∈ Finset.Ico (2*K+1) (2*M+1), f p) =
      ∑ k ∈ Finset.Ico K M, (f (2*k+1)+f (2*k+2)) := by
  by_cases hKM : K ≤ M
  · induction M, hKM using Nat.le_induction with
    | base => simp
    | succ M hKM ih =>
      have hbound : 2*K+1 ≤ 2*M+1 := by omega
      rw [show 2*(M+1)+1 = (2*M+1)+1+1 by omega,
        Finset.sum_Ico_succ_top (by omega : 2*K+1 ≤ (2*M+1)+1),
        Finset.sum_Ico_succ_top hbound, ih, Finset.sum_Ico_succ_top hKM]
      simp only [show 2*M+1+1=2*M+2 by omega, add_assoc]
  · rw [Finset.Ico_eq_empty_of_le (by omega : 2*M+1 ≤ 2*K+1),
      Finset.Ico_eq_empty_of_le (by omega : M ≤ K)]
    simp

/-- Every finite omitted-pivot horizon is bounded by complete parity pairs. -/
lemma sum_Ico_le_odd_even (f : ℕ → ℝ) (K N : ℕ) (hf : ∀ p, 0 ≤ f p) :
    (∑ p ∈ Finset.Ico (2*K+1) N, f p) ≤
      ∑ k ∈ Finset.Ico K N, (f (2*k+1)+f (2*k+2)) := by
  calc
    _ ≤ ∑ p ∈ Finset.Ico (2*K+1) (2*N+1), f p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · apply Finset.Ico_subset_Ico (le_refl _)
        omega
      · intro p hp hpn
        exact hf p
    _ = _ := sum_Ico_odd_even f K N

end SubmittedGenus.GoldenTail
