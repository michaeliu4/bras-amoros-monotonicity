import Results.Genus.RawGraph.Topology

/-! Every physical edge appears in the actual ordered component edge word. -/
noncomputable section
namespace SubmittedGenus.RawGraph.Topology.OrderedComponent
variable {V B : Type*} {G : SimpleGraph V} (O : OrderedComponent G)

def edgeWord (f : V→V→B) : List B :=
  List.ofFn (fun j : Fin O.edges => f (O.label j.castSucc) (O.label j.succ)) ++
    if O.cycle=true then [f (O.label (Fin.last O.edges)) (O.label 0)] else []

lemma edge_mem_word (f : V→V→B) (hs : ∀u v,G.Adj u v→f u v=f v u)
    (u v : V) (h : G.Adj u v) : f u v∈O.edgeWord f := by
  let i:=O.label.symm u
  let j:=O.label.symm v
  have hi : O.label i=u:=O.label.apply_symm_apply u
  have hj : O.label j=v:=O.label.apply_symm_apply v
  have hadj : G.Adj (O.label i) (O.label j) := by rwa [hi,hj]
  rcases (O.adjacent_iff i j).mp hadj with hf | hb | ⟨hc,hclose⟩
  · have hil : i.val<O.edges := by have := j.isLt; omega
    have hei : (⟨i.val,hil⟩ : Fin O.edges).castSucc=i:=Fin.ext rfl
    have hej : (⟨i.val,hil⟩ : Fin O.edges).succ=j:=Fin.ext hf
    apply List.mem_append_left
    apply List.mem_ofFn.mpr
    refine ⟨⟨i.val,hil⟩,?_⟩
    rw [hei,hej,hi,hj]
  · have hjl : j.val<O.edges := by have := i.isLt; omega
    have hej : (⟨j.val,hjl⟩ : Fin O.edges).castSucc=j:=Fin.ext rfl
    have hei : (⟨j.val,hjl⟩ : Fin O.edges).succ=i:=Fin.ext hb
    apply List.mem_append_left
    apply List.mem_ofFn.mpr
    refine ⟨⟨j.val,hjl⟩,?_⟩
    rw [hej,hei,hi,hj]
    exact (hs u v h).symm
  · apply List.mem_append_right
    rw [if_pos hc]
    rcases hclose with ⟨hiz,hjl⟩ | ⟨hjz,hil⟩
    · have heiz : i=0:=Fin.ext hiz
      have hejl : j=Fin.last O.edges:=Fin.ext hjl
      simp only [List.mem_singleton]
      rw [←hi,←hj,heiz,hejl]
      exact hs _ _ (by simpa only [heiz,hejl] using hadj)
    · have hejz : j=0:=Fin.ext hjz
      have heil : i=Fin.last O.edges:=Fin.ext hil
      simp only [List.mem_singleton]
      rw [←hi,←hj,hejz,heil]

end SubmittedGenus.RawGraph.Topology.OrderedComponent
