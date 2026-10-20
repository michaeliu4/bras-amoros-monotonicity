import Results.Genus.CapFourMass.GadgetSourceBounds

namespace SubmittedGenus.CapFourMass.GadgetFamilySurvival
open ContractionGeometry RawGraph RawGraph.SourceModel GadgetCoordinates GadgetFibers

lemma completion_of_values {m r p i n : ℕ}
    (e : Fin n ≃ PhysicalVertices m r p i) (c : Fin n)
    (hcphys : physical (e c).val = i) (hi : Eligible m p i)
    (a a₀ : Fin n → Fin 5) (b : Outside m r p i)
    (hbase : Admissible r p 4 (naturalWord e a₀ b))
    (hcenter : (a c).val=1)
    (hother : ∀ k, k≠c → 2 ≤ (a k).val ∧ (a k).val ≤ 3) :
    Admissible r p 4 (naturalWord e a b) := by
  apply completion_admissible hbase (e c).val (by simpa [hcphys] using hi)
  · intro v hv
    apply same_exterior e a a₀ b v
    simpa only [hcphys] using hv
  · simpa only [natural_inside] using hcenter
  · intro v hv hvc
    have hvi : physical v ∈ Gadget m r p i := by simpa only [hcphys] using hv
    let k := e.symm ⟨v,hvi⟩
    have hek : e k = ⟨v,hvi⟩ := e.apply_symm_apply _
    have hk : k≠c := by
      intro h
      apply hvc
      exact (congrArg Subtype.val (h ▸ hek)).symm
    have hh := hother k hk
    have hev : (e k).val=v := congrArg Subtype.val hek
    have hw := natural_inside e a b k
    rw [hev] at hw
    simpa only [hw] using hh

lemma failure_of_values {m r p i n : ℕ}
    (e : Fin n ≃ PhysicalVertices m r p i) (c t : Fin n)
    (hcphys : physical (e c).val=i) (htphys : physical (e t).val=2*i)
    (a : Fin n → Fin 5) (b : Outside m r p i)
    (hcenter : (a c).val=1) (htarget : (a t).val=3) :
    Failure (KunzWord.coord (naturalWord e a b)) i := by
  constructor
  · have hh := coord_inside e a b c
    rwa [hcphys,hcenter] at hh
  · have hh := coord_inside e a b t
    rwa [htphys,htarget] at hh

lemma prior_of_values {m r p i n : ℕ}
    (hr : 1 ≤ r) (hrp : r < p) (hi : Eligible m p i)
    (e : Fin n ≃ PhysicalVertices m r p i) (c t : Fin n)
    (hcphys : physical (e c).val=i) (htphys : physical (e t).val=2*i)
    (a a₀ : Fin n → Fin 5) (b : Outside m r p i)
    (hcenter : (a c).val=1) (htarget : (a t).val=3)
    (J : Finset ℕ) (hJ : ∀ j∈J,Eligible m p j)
    (hne : ∀ j∈J,i≠j) (horder : ∀ j∈J,¬Arrow m r p i j)
    (hbase : ∀ j∈J,¬Failure (KunzWord.coord (naturalWord e a₀ b)) j) :
    ∀ j∈J,¬Failure (KunzWord.coord (naturalWord e a b)) j := by
  apply completion_prior_avoids hr hrp (e c).val (by simpa only [hcphys] using hi)
    J hJ (by simpa only [hcphys] using hne) (by simpa only [hcphys] using horder) hbase
  · intro v hv
    apply same_exterior e a a₀ b v
    simpa only [hcphys] using hv
  · simpa only [natural_inside] using hcenter
  · have hh := coord_inside e a b t
    simpa only [hcphys,htphys,htarget] using hh

lemma postponed_prior_of_values {m r p i n : ℕ}
    (hr : 1 ≤ r) (hrp : r < p) (hi : Eligible m p i)
    (e : Fin n ≃ PhysicalVertices m r p i) (c t l₁ l₂ : Fin n)
    (hcphys : physical (e c).val=i) (htphys : physical (e t).val=2*i)
    (hl₁ : physical (e l₁).val=m+r-i) (hl₂ : physical (e l₂).val=m+p-i)
    (a a₀ : Fin n → Fin 5) (b : Outside m r p i)
    (hcenter : (a c).val=1) (htarget : (a t).val=3)
    (hleft : l₁≠t → (a l₁).val=2) (hright : l₂≠t → (a l₂).val=2)
    (J : Finset ℕ) (hJ : ∀ j∈J,Eligible m p j) (hne : ∀ j∈J,i≠j)
    (hbase : ∀ j∈J,¬Failure (KunzWord.coord (naturalWord e a₀ b)) j) :
    ∀ j∈J,¬Failure (KunzWord.coord (naturalWord e a b)) j := by
  apply postponed_completion_prior_avoids hr hrp (e c).val
    (by simpa only [hcphys] using hi) J hJ
    (by simpa only [hcphys] using hne) hbase
  · intro v hv
    apply same_exterior e a a₀ b v
    simpa only [hcphys] using hv
  · simpa only [natural_inside] using hcenter
  · have hh := coord_inside e a b t
    simpa only [hcphys,htphys,htarget] using hh
  · intro hn
    have hne : l₁≠t := by intro he; subst l₁; rw [htphys] at hl₁; simpa [hcphys,hl₁] using hn
    have hh := coord_inside e a b l₁
    simpa only [hcphys,hl₁,hleft hne] using hh
  · intro hn
    have hne : l₂≠t := by intro he; subst l₂; rw [htphys] at hl₂; simpa [hcphys,hl₂] using hn
    have hh := coord_inside e a b l₂
    simpa only [hcphys,hl₂,hright hne] using hh

end SubmittedGenus.CapFourMass.GadgetFamilySurvival
