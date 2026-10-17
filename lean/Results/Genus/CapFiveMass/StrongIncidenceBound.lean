import Results.Genus.CapFiveMass.StrongGeometry

noncomputable section
open scoped BigOperators
namespace SubmittedGenus.CapFiveMass.ActualComponent
open RawGraph RawGraph.SourceModel RawGraph.Topology RawGraph.Incidence LocalSource

lemma strong_edges_match (m r p : ℕ) :
    (strongEdges m r p).card = totalStrongCount m r p := by
  classical
  have hupper : (Finset.univ.filter (fun ij : FreeVertex m r p × FreeVertex m r p =>
      ij.1 < ij.2 ∧ StrongAdj r p ij.1 ij.2)).card = (strongEdges m r p).card := by
    apply Finset.card_bij (fun ij _ => (ij.1.val, ij.2.val))
    · intro ij hij
      have hh := (Finset.mem_filter.mp hij).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh.1,
        ij.1.property, ij.2.property, hh.2.2⟩
    · intro ij hij kl hkl he
      exact Prod.ext (Subtype.ext (congrArg Prod.fst he)) (Subtype.ext (congrArg Prod.snd he))
    · rintro ⟨i, j⟩ hij
      obtain ⟨_, hij, hi, hj, hs⟩ := Finset.mem_filter.mp hij
      let u : FreeVertex m r p := ⟨i, hi⟩
      let v : FreeVertex m r p := ⟨j, hj⟩
      refine ⟨(u, v), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij, ?_⟩, rfl⟩
      refine ⟨⟨ne_of_lt hij, hi, hj, ?_⟩, hs⟩
      rcases hs with hs | hs
      · exact Or.inl (Or.inl hs)
      · exact Or.inr (Or.inl hs)
  have hdiag : (Finset.univ.filter (fun i : FreeVertex m r p => StrongAdj r p i i)) = ∅ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    exact fun h => (freeGraph m r p).irrefl h.1
  have hh := symmetric_relation_card (StrongAdj (m := m) r p)
    (fun _ _ h => strongAdj_symm h)
  rw [hdiag, Finset.card_empty, add_zero, hupper, strong_pairs_count] at hh
  omega

lemma strong_loops_match (m r p : ℕ) :
    (strongLoops m r p).card = totalEndpointCount m r p .strongLoop := by
  rw [total_strong_loops]
  classical
  symm
  apply Finset.card_bij (fun i _ => i.val)
  · intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.property, (Finset.mem_filter.mp hi).2⟩
  · intro i hi j hj he
    exact Subtype.ext he
  · intro i hi
    obtain ⟨_, hf, hl⟩ := Finset.mem_filter.mp hi
    exact ⟨⟨i, hf⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩, rfl⟩

/-- The original strong-reflection incidence estimate expressed in the actual
ordered component exponents used by the analytic cap-five bound. -/
lemma ordered_strong_incidence_lower {m r p a : ℕ} (hp : Parameters m r p a) :
    r + p ≤ 2 * totalStrongCount m r p + totalEndpointCount m r p .strongLoop + 4 := by
  simpa only [strong_edges_match, strong_loops_match] using strong_incidence_lower hp

end SubmittedGenus.CapFiveMass.ActualComponent
