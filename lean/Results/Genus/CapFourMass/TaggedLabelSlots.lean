import Results.Genus.CapFourMass.TaggedCoverage

/-! Canonical source mode labels survive maximal-run compilation. -/
noncomputable section
namespace SubmittedGenus.CapFourMass.ActualComponent
open RawGraph

lemma carry_mem_taggedAtoms {B : Type*} [Inhabited B] (l : List (TaggedEdge B))
    (hl : l.IsChain TaggedCompatible) (b : B) (hb : TaggedEdge.carry b∈l) :
    ∃ (n : ℕ) (hn : 1≤n),TaggedAtom.carry b n hn∈taggedAtoms l := by
  have hflat : TaggedEdge.carry b∈(RunSegmentation.runs TaggedEdge.kind l).flatten := by
    rwa [RunSegmentation.flatten_runs]
  obtain ⟨g,hg,hmem⟩:=List.mem_flatten.mp hflat
  have hne:=RunSegmentation.run_nonempty TaggedEdge.kind l hg
  have hh:=tagged_run_constant l hl hg (.carry b) hmem
  have hn : 1≤g.length:=List.length_pos_iff.mpr hne
  have he : compileTaggedRun g=TaggedAtom.carry b g.length hn := by
    unfold compileTaggedRun
    rw [dif_neg hne,←hh]
  exact ⟨g.length,hn,List.mem_map.mpr ⟨g,hg,he⟩⟩

lemma tagged_pair_carry_mem {B : Type*} (b : B) (n : ℕ) (hn : 1≤n)
    (bs : List (TaggedBlock B)) :
    TaggedAtom.carry b n hn∈bs.flatMap taggedPair → ∃q∈bs,q.label=b := by
  intro hm
  obtain ⟨q,hq,hmem⟩:=List.mem_flatMap.mp hm
  simp only [taggedPair,List.mem_cons,List.not_mem_nil,or_false] at hmem
  rcases hmem with he | he
  · cases he
  · injection he with hlabel
    exact ⟨q,hq,hlabel.symm⟩

lemma tagged_path_carry_mem {B : Type*} (b : B) (n : ℕ) (hn : 1≤n)
    (q : TaggedPathCode B) (hm : TaggedAtom.carry b n hn∈q.atoms) :
    ∃ pre tag k hk bs post,q=.carried pre tag k hk bs post ∧
      (tag=b ∨ ∃q∈bs,q.label=b) := by
  cases q with
  | pure s =>
    cases s <;> simp [TaggedPathCode.atoms] at hm
  | carried pre tag k hk bs post =>
    refine ⟨pre,tag,k,hk,bs,post,rfl,?_⟩
    simp only [TaggedPathCode.atoms,List.mem_append,List.mem_singleton] at hm
    rcases hm with ((hpre | htag) | hbs) | hpost
    · cases pre <;> simp at hpre
    · left; cases htag; rfl
    · exact Or.inr (tagged_pair_carry_mem b n hn bs hbs)
    · cases post <;> simp at hpost

end SubmittedGenus.CapFourMass.ActualComponent
