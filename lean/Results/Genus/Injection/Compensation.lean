import Results.Genus.Injection.ParentReduction

noncomputable section
namespace SubmittedGenus.OriginalPopulations
open scoped BigOperators

/-- The genuine cap-four population, regrouped by its actual genus. -/
def fourWeightFibreEquiv (g : ℕ) :
    {d : GenuineFour // d.val.weight = g} ≃ GenuineFourAt g where
  toFun d := ⟨⟨d.val.val, d.property⟩, d.val.property⟩
  invFun d := ⟨⟨d.val.val, d.property⟩, d.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance (g : ℕ) : Fintype {d : GenuineFour // d.val.weight = g} :=
  Fintype.ofEquiv (GenuineFourAt g) (fourWeightFibreEquiv g).symm

lemma fourWeightFibre_sum (z : ℝ) (g : ℕ) :
    (∑' d : {d : GenuineFour // d.val.weight = g}, z ^ d.val.val.weight) =
      (countFour g : ℝ) * z ^ g := by
  simp only [show ∀ d : {d : GenuineFour // d.val.weight = g}, d.val.val.weight = g from fun d => d.property]
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ,
    Fintype.card_congr (fourWeightFibreEquiv g), nsmul_eq_mul]
  rfl

lemma four_source_summable {z : ℝ} (hz : 0 ≤ z)
    (hs : Summable (fun g => (countFour g : ℝ) * z ^ g)) :
    Summable (fun d : GenuineFour => z ^ d.val.weight) := by
  have hSigma : Summable (fun d : Σ g : ℕ, {d : GenuineFour // d.val.weight = g} =>
      z ^ d.2.val.val.weight) := by
    apply (summable_sigma_of_nonneg (fun _ => pow_nonneg hz _)).mpr
    exact ⟨fun _ => (hasSum_fintype _).summable, by simpa only [fourWeightFibre_sum] using hs⟩
  exact (Equiv.sigmaFiberEquiv (fun d : GenuineFour => d.val.weight)).summable_iff.mp hSigma

lemma massFour_eq_source_tsum {z : ℝ}
    (hs : Summable (fun d : GenuineFour => z ^ d.val.weight)) :
    massFour z = ∑' d : GenuineFour, z ^ d.val.weight := by
  have h := hs.hasSum.tsum_fiberwise (fun d : GenuineFour => d.val.weight)
  have he (g : ℕ) : (∑' d : (fun d : GenuineFour => d.val.weight) ⁻¹' {g}, z ^ d.val.val.weight) =
      (countFour g : ℝ) * z ^ g := fourWeightFibre_sum z g
  simp_rw [he] at h
  exact h.tsum_eq

lemma compensation_weight_term {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (d : FirstResidual ⊕ UniqueFiveResidual) :
    z ^ residualWeight d ≤ z ^ (compensationEmbedding d).val.weight :=
  pow_le_pow_of_le_one hz hz1 (compensationEmbedding_weight d)

/-- D(z) is summed over the actual first two sectors, with source genus. -/
def residualMass (z : ℝ) : ℝ :=
  ∑' d : FirstResidual ⊕ UniqueFiveResidual, z ^ residualWeight d

/-- The positive-real compensation inequality; no coefficientwise
comparison between different genera is asserted. -/
theorem residualMass_le_massFour {z : ℝ} (hz : 0 < z) (hz1 : z ≤ 1)
    (hs : Summable (fun g => (countFour g : ℝ) * z ^ g)) :
    Summable (fun d : FirstResidual ⊕ UniqueFiveResidual => z ^ residualWeight d) ∧
      residualMass z ≤ massFour z := by
  have hf := four_source_summable hz.le hs
  have hc : Summable (fun d : FirstResidual ⊕ UniqueFiveResidual =>
      z ^ (compensationEmbedding d).val.weight) := hf.comp_injective compensationEmbedding.injective
  have hd : Summable (fun d : FirstResidual ⊕ UniqueFiveResidual => z ^ residualWeight d) :=
    hc.of_nonneg_of_le (fun _ => pow_nonneg hz.le _) (compensation_weight_term hz.le hz1)
  refine ⟨hd, ?_⟩
  rw [massFour_eq_source_tsum hf]
  exact Summable.tsum_le_tsum_of_inj compensationEmbedding compensationEmbedding.injective
    (fun _ _ => pow_nonneg hz.le _) (compensation_weight_term hz.le hz1) hd hf

end SubmittedGenus.OriginalPopulations
