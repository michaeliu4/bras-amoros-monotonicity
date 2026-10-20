import Results.Genus.CapFourMass.CycleWords

/-! The actual maximal run list alternates positive strong and carry blocks. -/
noncomputable section
namespace SubmittedGenus.CapFourMass.ActualComponent
open RawGraph

lemma run_head_compatible (l : List EdgeKind) (hl : l.IsChain CompatibleKinds) :
    (RunSegmentation.runs id l).IsChain (fun g h => ∃ hg : g≠[],∃ hh : h≠[],
      CompatibleKinds (g.head hg) (h.head hh)) := by
  have hnil : []∉RunSegmentation.runs id l := by
    intro h
    exact RunSegmentation.run_nonempty id l h rfl
  have hflat : (RunSegmentation.runs id l).flatten.IsChain CompatibleKinds := by
    rw [RunSegmentation.flatten_runs]
    exact hl
  have hb := ((List.isChain_flatten hnil).mp hflat).2
  apply hb.imp_of_mem_imp
  intro g h hg hh hboundary
  have hgn := RunSegmentation.run_nonempty id l hg
  have hhn := RunSegmentation.run_nonempty id l hh
  refine ⟨hgn,hhn,?_⟩
  have hc := hboundary (g.getLast hgn) (by simp [List.getLast?_eq_some_getLast hgn])
    (h.head hhn) (by simp [List.head?_eq_some_head hhn])
  have he := RunSegmentation.run_constant id l hg (g.getLast hgn) (List.getLast_mem hgn)
  change g.getLast hgn=g.head hgn at he
  rw [he] at hc
  exact hc

lemma run_heads_alternate_color (l : List EdgeKind) (hl : l.IsChain CompatibleKinds) :
    (RunSegmentation.runs id l).IsChain (fun g h => ∃ hg : g≠[],∃ hh : h≠[],
      strongColor (g.head hg)≠strongColor (h.head hh)) := by
  have ha := actual_runs_alternate l
  have hb := run_head_compatible l hl
  rw [List.isChain_iff_getElem] at ha hb ⊢
  intro j hj
  obtain ⟨hg,hh,hne⟩ := ha j hj
  obtain ⟨_,_,hc⟩ := hb j hj
  refine ⟨hg,hh,?_⟩
  generalize (RunSegmentation.runs id l)[j].head hg=a at hne hc ⊢
  generalize (RunSegmentation.runs id l)[j+1].head hh=b at hne hc ⊢
  cases a <;> cases b <;> simp_all [CompatibleKinds,strongColor]

/-- Every computed block has positive length, alternate source type, and
any restricted block consists of a single E edge. -/
theorem actual_run_properties (l : List EdgeKind) (hl : l.IsChain CompatibleKinds) :
    (∀ g∈RunSegmentation.runs id l,0<g.length) ∧
    (RunSegmentation.runs id l).IsChain (fun g h => ∃ hg : g≠[],∃ hh : h≠[],
      strongColor (g.head hg)≠strongColor (h.head hh)) ∧
    (∀ g (hg : g∈RunSegmentation.runs id l),
      g.head (RunSegmentation.run_nonempty id l hg)=.restricted → g=[.restricted]) := by
  refine ⟨?_,run_heads_alternate_color l hl,?_⟩
  · intro g hg
    exact List.length_pos_iff.mpr (RunSegmentation.run_nonempty id l hg)
  · exact fun g hg he => restricted_run_singleton l hl hg he

end SubmittedGenus.CapFourMass.ActualComponent
