import Results.Genus.CapFourMass.GadgetDensity

namespace SubmittedGenus.CapFourMass.ConditionalDensity
open scoped BigOperators
open RawGraph RawGraph.SourceModel ContractionGeometry GadgetCoordinates GadgetFibers
open GadgetFamilySurvival GadgetDensity
noncomputable section
attribute [local instance] Classical.propDecidable

def Good (m r p : ℕ) (J : Finset ℕ) (x : Fin (m-1) → Fin 5) : Prop :=
  Admissible r p 4 (boundedWord x) ∧ ∀ j∈J,¬Failure (KunzWord.coord (boundedWord x)) j

theorem nonpostponed_model {m r p i n : ℕ}
    (hr : 1 ≤ r) (hrp : r < p) (hi : Eligible m p i)
    (e : Fin n ≃ PhysicalVertices m r p i) (c t : Fin n)
    (hcphys : physical (e c).val=i) (htphys : physical (e t).val=2*i)
    (z eps : ℝ) (hz : 0 ≤ z) (heps : 0 ≤ eps)
    (J : Finset ℕ) (hJ : ∀j∈J,Eligible m p j)
    (hne : ∀j∈J,i≠j) (horder : ∀j∈J,¬Arrow m r p i j)
    (allowed family : (Fin n → Fin 5) → Prop)
    (hallowed : ∀ b a, Admissible r p 4 (naturalWord e a b) → allowed a)
    (hvalues : ∀ a, family a → (a c).val=1 ∧ (a t).val=3 ∧
      ∀ k, k≠c → 2 ≤ (a k).val ∧ (a k).val ≤ 3)
    (hratio : eps*(∑ a, if allowed a then GadgetLocalSums.weight z a else 0) ≤
      ∑ a, if family a then GadgetLocalSums.weight z a else 0) :
    eps*(∑ x, if Good m r p J x then ∏ v, z^(x v).val else 0) ≤
      ∑ x, if Good m r p J x ∧ Failure (KunzWord.coord (boundedWord x)) i
        then ∏ v, z^(x v).val else 0 := by
  apply density_of_model e c t hcphys htphys z eps hz heps (Good m r p J)
    allowed family
  · intro b a ha
    exact hallowed b a ha.1
  · intro b hex a ha
    obtain ⟨a₀,hbase⟩ := hex
    obtain ⟨hcenter,htarget,hother⟩ := hvalues a ha
    refine ⟨⟨?_,?_⟩,hcenter,htarget⟩
    · exact completion_of_values e c hcphys hi a a₀ b hbase.1 hcenter hother
    · exact prior_of_values hr hrp hi e c t hcphys htphys a a₀ b hcenter htarget
        J hJ hne horder hbase.2
  · exact hratio

theorem postponed_model {m r p i n : ℕ}
    (hr : 1 ≤ r) (hrp : r < p) (hi : Eligible m p i)
    (e : Fin n ≃ PhysicalVertices m r p i) (c t l₁ l₂ : Fin n)
    (hcphys : physical (e c).val=i) (htphys : physical (e t).val=2*i)
    (hl₁ : physical (e l₁).val=m+r-i) (hl₂ : physical (e l₂).val=m+p-i)
    (z eps : ℝ) (hz : 0 ≤ z) (heps : 0 ≤ eps)
    (J : Finset ℕ) (hJ : ∀j∈J,Eligible m p j) (hne : ∀j∈J,i≠j)
    (allowed family : (Fin n → Fin 5) → Prop)
    (hallowed : ∀ b a, Admissible r p 4 (naturalWord e a b) → allowed a)
    (hvalues : ∀ a, family a → (a c).val=1 ∧ (a t).val=3 ∧
      (∀ k, k≠c → 2 ≤ (a k).val ∧ (a k).val ≤ 3) ∧
      (l₁≠t → (a l₁).val=2) ∧ (l₂≠t → (a l₂).val=2))
    (hratio : eps*(∑ a, if allowed a then GadgetLocalSums.weight z a else 0) ≤
      ∑ a, if family a then GadgetLocalSums.weight z a else 0) :
    eps*(∑ x, if Good m r p J x then ∏ v, z^(x v).val else 0) ≤
      ∑ x, if Good m r p J x ∧ Failure (KunzWord.coord (boundedWord x)) i
        then ∏ v, z^(x v).val else 0 := by
  apply density_of_model e c t hcphys htphys z eps hz heps (Good m r p J)
    allowed family
  · intro b a ha
    exact hallowed b a ha.1
  · intro b hex a ha
    obtain ⟨a₀,hbase⟩ := hex
    obtain ⟨hcenter,htarget,hother,hleft,hright⟩ := hvalues a ha
    refine ⟨⟨?_,?_⟩,hcenter,htarget⟩
    · exact completion_of_values e c hcphys hi a a₀ b hbase.1 hcenter hother
    · exact postponed_prior_of_values hr hrp hi e c t l₁ l₂ hcphys htphys hl₁ hl₂
        a a₀ b hcenter htarget hleft hright J hJ hne hbase.2
  · exact hratio

end
end SubmittedGenus.CapFourMass.ConditionalDensity
