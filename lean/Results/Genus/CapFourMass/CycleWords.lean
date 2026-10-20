import Results.Genus.CapFourMass.RunGeometry

/-! Both source colors actually occur in every compiled cyclic word. -/
noncomputable section
namespace SubmittedGenus.CapFourMass.ActualComponent
open RawGraph RawGraph.SourceModel RawGraph.Topology

lemma consecutive_kind_mem {m r p : ℕ} (c : Component m r p) (j : Fin (edgeCount c)) :
    kind r p (vertex c j.castSucc) (vertex c j.succ) ∈ pathWord c := by
  exact List.mem_ofFn.mpr ⟨j,rfl⟩

lemma adjacency_kind_mem_closed {m r p : ℕ} (c : Component m r p)
    (i j : Fin (edgeCount c+1))
    (he : (rawGraph m r p).Adj (vertex c i) (vertex c j)) :
    kind r p (vertex c i) (vertex c j)∈closedWord c := by
  have hh := ((freeComponentOrder m r p c).adjacent_iff i j).mp he
  rcases hh with hij | hji | ⟨_,hh⟩
  · have hi : i.val<edgeCount c := by have := j.isLt; omega
    have hi' : i=Fin.castSucc (⟨i.val,hi⟩ : Fin (edgeCount c)) := Fin.ext rfl
    have hj' : j=Fin.succ (⟨i.val,hi⟩ : Fin (edgeCount c)) := Fin.ext hij.symm
    simpa only [closedWord,← hi',← hj'] using List.mem_append_left _ (consecutive_kind_mem c ⟨i.val,hi⟩)
  · rw [kind_symm]
    have hj : j.val<edgeCount c := by have := i.isLt; omega
    have hj' : j=Fin.castSucc (⟨j.val,hj⟩ : Fin (edgeCount c)) := Fin.ext rfl
    have hi' : i=Fin.succ (⟨j.val,hj⟩ : Fin (edgeCount c)) := Fin.ext hji.symm
    simpa only [closedWord,← hi',← hj'] using List.mem_append_left _ (consecutive_kind_mem c ⟨j.val,hj⟩)
  · rcases hh with ⟨hi,hj⟩ | ⟨hj,hi⟩
    · have hi' : i=0 := Fin.ext hi
      have hj' : j=Fin.last (edgeCount c) := Fin.ext hj
      rw [hi',hj',kind_symm]
      exact List.mem_append_right _ (by simp)
    · have hi' : i=Fin.last (edgeCount c) := Fin.ext hi
      have hj' : j=0 := Fin.ext hj
      rw [hi',hj']
      exact List.mem_append_right _ (by simp)

/-- Actual cycles have nonempty strong and carry runs, rather than receiving
an unsupported zero-carry spectral block. -/
theorem closedWord_mixed {m r p : ℕ} (hp : Parameters m r p 4) (c : Component m r p)
    (hc : (freeComponentOrder m r p c).cycle=true) :
    EdgeKind.carry∈closedWord c ∧ ∃ k∈closedWord c,k≠EdgeKind.carry := by
  obtain ⟨⟨i,j,hs⟩,⟨u,v,hcarry⟩⟩ := StrongRuns.actual_cycle_mixed hp c hc
  constructor
  · have he : kind r p (vertex c u) (vertex c v)=.carry := (kind_carry_iff hp hcarry.1).2 hcarry
    rw [← he]
    exact adjacency_kind_mem_closed c u v hcarry.1
  · exact ⟨kind r p (vertex c i) (vertex c j),adjacency_kind_mem_closed c i j hs.1,
      (kind_ne_carry_iff hs.1).2 hs⟩

def strongColor (k : EdgeKind) : Bool := decide (k≠.carry)

lemma closedWord_both_colors {m r p : ℕ} (hp : Parameters m r p 4) (c : Component m r p)
    (hc : (freeComponentOrder m r p c).cycle=true) :
    true∈(closedWord c).map strongColor ∧ false∈(closedWord c).map strongColor := by
  obtain ⟨hcarry,k,hk,hne⟩ := closedWord_mixed hp c hc
  exact ⟨List.mem_map.mpr ⟨k,hk,by simp [strongColor,hne]⟩,
    List.mem_map.mpr ⟨.carry,hcarry,by simp [strongColor]⟩⟩

end SubmittedGenus.CapFourMass.ActualComponent
