import Results.Genus.CapFourMass.ConditionalProduct

namespace SubmittedGenus.CapFourMass.FiberComparison
open scoped BigOperators
noncomputable section

/-- Finite exterior-slice comparison. A proposed failure family only has to
survive on exterior slices with an actual admissible completion. This makes
no false outside-measurability assumption about preceding avoidances. -/
theorem weighted_failure_lower {E G : Type*} [Fintype E] [Fintype G]
    (outer : E → ℝ) (inner : G → ℝ)
    (houter : ∀ e, 0 ≤ outer e) (hinner : ∀ g, 0 ≤ inner g)
    (P : E → G → Prop) (F : G → Prop)
    [∀ e, DecidablePred (P e)] [DecidablePred F]
    (allowed family : Finset G) (eps : ℝ) (heps : 0 ≤ eps)
    (hallowed : ∀ e g, P e g → g ∈ allowed)
    (hfamily : ∀ e, (∃ g, P e g) → ∀ g ∈ family, P e g ∧ F g)
    (hratio : eps*(∑ g ∈ allowed, inner g) ≤ ∑ g ∈ family, inner g) :
    eps*(∑ e, outer e*(∑ g, if P e g then inner g else 0)) ≤
      ∑ e, outer e*(∑ g, if P e g ∧ F g then inner g else 0) := by
  classical
  have hlocal (e : E) :
      eps*(∑ g, if P e g then inner g else 0) ≤
        ∑ g, if P e g ∧ F g then inner g else 0 := by
    by_cases hex : ∃ g, P e g
    · have hu : Finset.univ.filter (P e) ⊆ allowed := by
        intro g hg
        exact hallowed e g (Finset.mem_filter.mp hg).2
      have hl : family ⊆ Finset.univ.filter (fun g => P e g ∧ F g) := by
        intro g hg
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hfamily e hex g hg⟩
      have hupper := Finset.sum_le_sum_of_subset_of_nonneg hu
        (fun g _ _ => hinner g)
      have hlower := Finset.sum_le_sum_of_subset_of_nonneg hl
        (fun g _ _ => hinner g)
      rw [Finset.sum_filter] at hupper hlower
      exact (mul_le_mul_of_nonneg_left hupper heps).trans (hratio.trans hlower)
    · have hp : ∀ g, ¬P e g := by simpa only [not_exists] using hex
      simp [hp]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e he
  have hh := mul_le_mul_of_nonneg_left (hlocal e) (houter e)
  simpa only [mul_left_comm eps (outer e)] using hh

end
end SubmittedGenus.CapFourMass.FiberComparison
