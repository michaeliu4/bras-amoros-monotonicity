import Results.Genus.CapFourMass.ContractionGeometry

namespace SubmittedGenus.CapFourMass.ContractionGeometry
open RawGraph RawGraph.SourceModel

theorem domain_positive {m r p : ℕ} (v : Fin (m-1)) {a : ℕ}
    (h : Domain r p 4 v a) : 1 ≤ a := by
  by_cases hp : IsPivot r p v
  · have := h.1 hp
    omega
  · have hh := (h.2 hp).1
    have hlo : 1 ≤ lower r p 4 v := le_max_left _ _
    omega

theorem gadget_high {m r p i j : ℕ} (hr : 1 ≤ r) (hrp : r < p)
    (hi : Eligible m p i) (hj : j ∈ Gadget m r p i) : p < j := by
  have hg := gadget_bounds hr hrp hi
  simp only [Gadget, Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl | rfl | rfl <;> omega

/-- Every proposed failure-family completion remains admissible for the exact
original raw graph, for any admissible exterior. The target can coincide with
either reflection leaf; no four-distinct-vertices premise is needed. -/
theorem completion_admissible {m r p : ℕ} {x y : Word m}
    (hx : Admissible r p 4 x) (c : Fin (m-1))
    (hc : Eligible m p (physical c))
    (hexterior : ∀ v, physical v ∉ Gadget m r p (physical c) → y v = x v)
    (hcenter : y c = 1)
    (hother : ∀ v, physical v ∈ Gadget m r p (physical c) → v ≠ c →
      2 ≤ y v ∧ y v ≤ 3) : Admissible r p 4 y := by
  have hr := hx.1.1
  have hrp := hx.1.2.1
  have hphys : Function.Injective (@physical m) := by
    intro i j h
    apply Fin.ext
    unfold physical at h
    omega
  have hd : ∀ v, Domain r p 4 v (y v) := by
    intro v
    by_cases hv : physical v ∈ Gadget m r p (physical c)
    · by_cases hvc : v = c
      · subst v
        rw [center_domain hr hrp c hc, hcenter]
        omega
      · exact high_domain hrp v (gadget_high hr hrp hc hv) (hother v hv hvc)
    · rw [hexterior v hv]
      exact hx.2.1 v
  have hpos : ∀ v, 1 ≤ y v := fun v => domain_positive v (hd v)
  refine ⟨hx.1, hd, ?_⟩
  intro u v huv
  by_cases hu : physical u ∈ Gadget m r p (physical c)
  · have hup := gadget_high hr hrp hc hu
    unfold edgeBound
    split_ifs with hzero hstrong hcarry
    · omega
    · have hvpos : 0 < physical v := by unfold physical; omega
      rcases hstrong with hstrong | hstrong <;> omega
    · by_cases huc : u = c
      · subst u
        have hvG : physical v ∈ Gadget m r p (physical c) := by
          simp only [Gadget, Finset.mem_insert, Finset.mem_singleton]
          rcases hcarry with hcarry | hcarry
          · exact Or.inr (Or.inr (Or.inl (by omega)))
          · exact Or.inr (Or.inr (Or.inr (by omega)))
        have hvc : v ≠ c := by intro h; subst v; exact (lt_irrefl c) huv
        have hv2 := (hother v hvG hvc).1
        rw [hcenter]
        omega
      · have hu2 := (hother u hu huc).1
        have hv1 := hpos v
        omega
    · omega
  · by_cases hv : physical v ∈ Gadget m r p (physical c)
    · have hvp := gadget_high hr hrp hc hv
      unfold edgeBound
      split_ifs with hzero hstrong hcarry
      · omega
      · have hup : 0 < physical u := by unfold physical; omega
        rcases hstrong with hstrong | hstrong <;> omega
      · by_cases hvc : v = c
        · subst v
          have huG : physical u ∈ Gadget m r p (physical c) := by
            simp only [Gadget, Finset.mem_insert, Finset.mem_singleton]
            rcases hcarry with hcarry | hcarry
            · exact Or.inr (Or.inr (Or.inl (by omega)))
            · exact Or.inr (Or.inr (Or.inr (by omega)))
          exact (hu huG).elim
        · have hv2 := (hother v hv hvc).1
          have hu1 := hpos u
          omega
      · omega
    · rw [hexterior u hu, hexterior v hv]
      exact hx.2.2 u v huv

end SubmittedGenus.CapFourMass.ContractionGeometry
