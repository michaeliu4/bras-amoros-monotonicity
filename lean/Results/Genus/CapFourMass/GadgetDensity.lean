import Results.Genus.CapFourMass.GadgetFamilySurvival

namespace SubmittedGenus.CapFourMass.GadgetDensity
open scoped BigOperators
open RawGraph ContractionGeometry GadgetCoordinates GadgetFibers
noncomputable section
attribute [local instance] Classical.propDecidable

lemma failure_iff_values {m r p i n : ℕ}
    (e : Fin n ≃ PhysicalVertices m r p i) (c t : Fin n)
    (hcphys : physical (e c).val=i) (htphys : physical (e t).val=2*i)
    (a : Fin n → Fin 5) (b : Outside m r p i) :
    Failure (KunzWord.coord (naturalWord e a b)) i ↔
      (a c).val=1 ∧ (a t).val=3 := by
  have hc := coord_inside e a b c
  have ht := coord_inside e a b t
  rw [hcphys] at hc
  rw [htphys] at ht
  simp only [Failure,hc,ht]

/-- Exact local-to-global weighted slice bridge over actual bounded physical
word coordinates, with all finite assignment and weight bijections discharged. -/
theorem density_of_model {m r p i n : ℕ}
    (e : Fin n ≃ PhysicalVertices m r p i) (c t : Fin n)
    (hcphys : physical (e c).val=i) (htphys : physical (e t).val=2*i)
    (z eps : ℝ) (hz : 0 ≤ z) (heps : 0 ≤ eps)
    (P : (Fin (m-1) → Fin 5) → Prop)
    (allowed family : (Fin n → Fin 5) → Prop)
    (hallowed : ∀ b a, P (word e a b) → allowed a)
    (hfamily : ∀ b, (∃ a, P (word e a b)) → ∀ a, family a →
      P (word e a b) ∧ (a c).val=1 ∧ (a t).val=3)
    (hratio : eps*(∑ a, if allowed a then GadgetLocalSums.weight z a else 0) ≤
      ∑ a, if family a then GadgetLocalSums.weight z a else 0) :
    eps*(∑ x : Fin (m-1) → Fin 5, if P x then ∏ v, z^(x v).val else 0) ≤
      ∑ x : Fin (m-1) → Fin 5,
        if P x ∧ Failure (KunzWord.coord (boundedWord x)) i
        then ∏ v, z^(x v).val else 0 := by
  classical
  rw [partition_split e z P]
  have hh := FiberComparison.weighted_failure_lower
    (fun b : Outside m r p i => ∏ v, z^(b v).val)
    (fun a : Fin n → Fin 5 => GadgetLocalSums.weight z a)
    (by intro b; exact Finset.prod_nonneg (fun _ _ => pow_nonneg hz _))
    (by intro a; unfold GadgetLocalSums.weight; exact Finset.prod_nonneg (fun _ _ => pow_nonneg hz _))
    (fun b a => P (word e a b)) (fun a => (a c).val=1 ∧ (a t).val=3)
    (Finset.univ.filter allowed) (Finset.univ.filter family) eps heps
    (by intro b a ha; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hallowed b a ha⟩)
    (by
      intro b hex a ha
      exact hfamily b hex a (Finset.mem_filter.mp ha).2)
    (by simpa only [Finset.sum_filter] using hratio)
  have heq : ∀ b a,
      (P (word e a b) ∧ Failure (KunzWord.coord (boundedWord (word e a b))) i) ↔
        P (word e a b) ∧ ((a c).val=1 ∧ (a t).val=3) := by
    intro b a
    exact and_congr_right (fun _ => failure_iff_values e c t hcphys htphys a b)
  have hsplit := partition_split e z
    (fun x => P x ∧ Failure (KunzWord.coord (boundedWord x)) i)
  have hright : (∑ b : Outside m r p i, (∏ v, z^(b v).val) *
      (∑ a : Fin n → Fin 5, if P (word e a b) ∧ ((a c).val=1 ∧ (a t).val=3)
        then GadgetLocalSums.weight z a else 0)) =
      ∑ x : Fin (m-1) → Fin 5,
        if P x ∧ Failure (KunzWord.coord (boundedWord x)) i
        then ∏ v, z^(x v).val else 0 := by
    simp only [heq] at hsplit
    refine hsplit.symm.trans ?_
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hh : P x ∧ Failure (KunzWord.coord (boundedWord x)) i <;> simp [hh]
  exact hh.trans_eq hright

end
end SubmittedGenus.CapFourMass.GadgetDensity
