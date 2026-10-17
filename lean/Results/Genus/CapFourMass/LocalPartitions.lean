import Results.Genus.CapFourMass.CoordinateFibers

namespace SubmittedGenus.CapFourMass.LocalPartitions
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Independent unary gates factor exactly, without enumerating assignments. -/
theorem gated_product {V S : Type*} [Fintype V]
    (w : V → S → ℝ) (A : V → S → Prop) [∀ v, DecidablePred (A v)]
    (x : V → S) :
    (∏ v, if A v (x v) then w v (x v) else 0) =
      if ∀ v, A v (x v) then ∏ v, w v (x v) else 0 := by
  classical
  by_cases h : ∀ v, A v (x v)
  · simp [h]
  · rw [if_neg h]
    obtain ⟨v,hv⟩ := not_forall.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ v) (by simp [hv])

theorem independent_partition {V S : Type*} [Fintype V] [Fintype S] [DecidableEq V]
    (w : V → S → ℝ) (A : V → S → Prop) [∀ v, DecidablePred (A v)] :
    (∑ x : V → S, if ∀ v, A v (x v) then ∏ v, w v (x v) else 0) =
      ∏ v, ∑ a : S, if A v a then w v a else 0 := by
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x hx
  exact (gated_product w A x).symm

/-- For integer-letter words, this product is exactly the manuscript genus
weight, with no endpoint weights inserted or dropped. -/
theorem genus_weight {m : ℕ} (z : ℝ) (x : Fin (m-1) → Fin 5) :
    (∏ v, z^(x v).val) = z^RawGraph.genus (RawGraph.boundedWord x) := by
  exact Finset.prod_pow_eq_pow_sum Finset.univ (fun v => (x v).val) z

/-- The literal raw cap-four polynomial evaluated at z equals its finite
weighted assignment partition. -/
theorem raw_partition_eval (m r p : ℕ) (z : ℝ) :
    Polynomial.eval₂ (Nat.castRingHom ℝ) z (RawGraph.rawPolynomial m r p 4) =
      ∑ x : Fin (m-1) → Fin 5,
        if RawGraph.SourceModel.Admissible r p 4 (RawGraph.boundedWord x)
        then ∏ v, z^(x v).val else 0 := by
  classical
  unfold RawGraph.rawPolynomial
  rw [Polynomial.eval₂_finsetSum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [← RawGraph.SourceModel.raw_iff_compiled]
  split_ifs <;> simp [Polynomial.eval₂_pow, genus_weight]

end
end SubmittedGenus.CapFourMass.LocalPartitions
