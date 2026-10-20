import Results.Genus.CapFourMass.GadgetCompletion

namespace SubmittedGenus.CapFourMass.ContractionGeometry
open RawGraph RawGraph.SourceModel

lemma coord_outside_eq {m r p i : ℕ} {x y : Word m}
    (hexterior : ∀ v, physical v ∉ Gadget m r p i → y v = x v)
    {j : ℕ} (hj0 : 0 < j) (hjm : j < m) (hj : j ∉ Gadget m r p i) :
    KunzWord.coord y j = KunzWord.coord x j := by
  have hh : 0 < j ∧ j < m := ⟨hj0,hjm⟩
  simp only [KunzWord.coord, dif_pos hh]
  apply hexterior
  simpa only [physical, Nat.sub_add_cancel hj0] using hj

/-- A full proposed nonpostponed completion preserves every actual preceding
avoidance, even when that earlier event meets the gadget. -/
theorem completion_prior_avoids {m r p : ℕ} {x y : Word m}
    (hr : 1 ≤ r) (hrp : r < p) (c : Fin (m-1))
    (hc : Eligible m p (physical c)) (J : Finset ℕ)
    (hJ : ∀ j ∈ J, Eligible m p j)
    (hne : ∀ j ∈ J, physical c ≠ j)
    (horder : ∀ j ∈ J, ¬ Arrow m r p (physical c) j)
    (hx : ∀ j ∈ J, ¬Failure (KunzWord.coord x) j)
    (hexterior : ∀ v, physical v ∉ Gadget m r p (physical c) → y v = x v)
    (hcenter : y c = 1) (htarget : KunzWord.coord y (2*physical c) = 3) :
    ∀ j ∈ J, ¬Failure (KunzWord.coord y) j := by
  intro j hj
  have he := hJ j hj
  by_cases hmeet : j ∈ Gadget m r p (physical c) ∨
      2*j ∈ Gadget m r p (physical c)
  · apply nonpostponed_survival hr hrp hc he (hne j hj) (horder j hj)
      (x := KunzWord.coord y) _ htarget hmeet
    simpa only [physical, KunzWord.coord_index] using hcenter
  · have hj0 : 0 < j := by have := he.1; omega
    have hjm : j < m := by have := he.2; omega
    have h2j0 : 0 < 2*j := by omega
    have ha := coord_outside_eq hexterior hj0 hjm (not_or.mp hmeet).1
    have hb := coord_outside_eq hexterior h2j0 he.2 (not_or.mp hmeet).2
    simpa only [Failure,ha,hb] using hx j hj

/-- The single postponed assignment preserves all preceding avoidances with
no dependency-order premise. -/
theorem postponed_completion_prior_avoids {m r p : ℕ} {x y : Word m}
    (hr : 1 ≤ r) (hrp : r < p) (c : Fin (m-1))
    (hc : Eligible m p (physical c)) (J : Finset ℕ)
    (hJ : ∀ j ∈ J, Eligible m p j) (hne : ∀ j ∈ J, physical c ≠ j)
    (hx : ∀ j ∈ J, ¬Failure (KunzWord.coord x) j)
    (hexterior : ∀ v, physical v ∉ Gadget m r p (physical c) → y v = x v)
    (hcenter : y c = 1) (htarget : KunzWord.coord y (2*physical c) = 3)
    (hleft : m+r-physical c ≠ 2*physical c → KunzWord.coord y (m+r-physical c) = 2)
    (hright : m+p-physical c ≠ 2*physical c → KunzWord.coord y (m+p-physical c) = 2) :
    ∀ j ∈ J, ¬Failure (KunzWord.coord y) j := by
  intro j hj
  have he := hJ j hj
  by_cases hmeet : j ∈ Gadget m r p (physical c) ∨
      2*j ∈ Gadget m r p (physical c)
  · apply postponed_survival hr hrp hc he (hne j hj)
      (x := KunzWord.coord y) _ htarget hleft hright hmeet
    simpa only [physical, KunzWord.coord_index] using hcenter
  · have hj0 : 0 < j := by have := he.1; omega
    have hjm : j < m := by have := he.2; omega
    have h2j0 : 0 < 2*j := by omega
    have ha := coord_outside_eq hexterior hj0 hjm (not_or.mp hmeet).1
    have hb := coord_outside_eq hexterior h2j0 he.2 (not_or.mp hmeet).2
    simpa only [Failure,ha,hb] using hx j hj

end SubmittedGenus.CapFourMass.ContractionGeometry
