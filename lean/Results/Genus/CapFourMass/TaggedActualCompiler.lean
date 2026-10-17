import Results.Genus.CapFourMass.TaggedSourceWords
import Results.Genus.CapFourMass.TaggedMatrices

/-! Actual source paths/cycles compile to labelled signed carry contractions
with exactly the original source exponents. -/
noncomputable section
open scoped Matrix
namespace SubmittedGenus.CapFourMass.ActualComponent
open RawGraph RawGraph.Topology FixedPivot

lemma taggedAtoms_head_color {B : Type*} [Inhabited B] (l : List (TaggedEdge B)) :
    ((taggedAtoms l).map (fun a => a.erase.isStrong)).head?=
      (l.map (fun a => strongColor a.kind)).head? := by
  change ((taggedAtoms l).map (AtomicRun.isStrong∘TaggedAtom.erase)).head?=_
  rw [←List.map_map,taggedAtoms_erase,sourceAtoms_head_color,List.map_map]
  rfl

lemma taggedAtoms_last_color {B : Type*} [Inhabited B] (l : List (TaggedEdge B)) :
    ((taggedAtoms l).map (fun a => a.erase.isStrong)).getLast?=
      (l.map (fun a => strongColor a.kind)).getLast? := by
  change ((taggedAtoms l).map (AtomicRun.isStrong∘TaggedAtom.erase)).getLast?=_
  rw [←List.map_map,taggedAtoms_erase,sourceAtoms_last_color,List.map_map]
  rfl

section Actual
variable {r N d : ℕ} (hr : 0<r) (hd : 0<d) (hN : d<N)

include hr in
/-- The labelled path code is computed from the actual source word. Its
matrix equality holds for arbitrary signed carry matrices. -/
theorem actual_tagged_path (c : Component (r+N) r (r+d)) :
    ∃ q : TaggedPathCode (Option (CarryRepresentative N d hN)),
      taggedAtoms (taggedPathWord hd hN c)=q.atoms ∧
      (∀ C : Option (CarryRepresentative N d hN)→Matrix State State ℝ,
        ((taggedPathWord hd hN c).map (TaggedEdge.matrixWith C)).prod=q.matrixWith C) ∧
      q.erase.strongCount=strongLength (pathWord c) ∧
      q.erase.carryCount=carryLength (pathWord c) ∧
      q.erase.restrictedCount=restrictedLength (pathWord c) := by
  have hc:=taggedPathWord_compatible hr hd hN c
  obtain ⟨q,he⟩:=tagged_path_normal_form (taggedAtoms (taggedPathWord hd hN c))
    (taggedAtoms_alternate _ hc)
  have herase : sourceAtoms (pathWord c)=q.erase.atoms := by
    rw [←taggedPathWord_kinds hd hN c,←taggedAtoms_erase,he,TaggedPathCode.atoms_erase]
  have hcounts:=sourceAtoms_counts (pathWord c) (pathWord_compatible (canonicalParameters hr hd hN) c)
  rw [herase,(PathCode.atoms_counts q.erase).1,(PathCode.atoms_counts q.erase).2.1,
    (PathCode.atoms_counts q.erase).2.2] at hcounts
  refine ⟨q,he,?_,hcounts⟩
  intro C
  rw [←taggedAtoms_matrix C _ hc,he,TaggedPathCode.atoms_matrixWith]

include hr in
/-- Every actual cyclic component has a label-preserving strong/carry cut and
a nonempty list of signed blocks, with all three physical edge counts retained. -/
theorem actual_tagged_cycle (c : Component (r+N) r (r+d))
    (hc : (freeComponentOrder (r+N) r (r+d) c).cycle=true) :
    ∃ (n : ℕ) (bs : List (TaggedBlock (Option (CarryRepresentative N d hN)))),
      bs≠[] ∧ taggedAtoms ((taggedClosedWord hd hN c).rotate n)=bs.flatMap taggedPair ∧
      (∀ C : Option (CarryRepresentative N d hN)→Matrix State State ℝ,
        ((((taggedClosedWord hd hN c).rotate n).map (TaggedEdge.matrixWith C)).prod).trace=
          ((bs.map (TaggedBlock.matrixWith C)).prod).trace) ∧
      ((bs.map TaggedBlock.run).map (fun b => b.strong.strongCount)).sum=strongLength (closedWord c) ∧
      ((bs.map TaggedBlock.run).map CoupledRun.carryLength).sum=carryLength (closedWord c) ∧
      ((bs.map TaggedBlock.run).map (fun b => b.strong.restrictedCount)).sum=restrictedLength (closedWord c) := by
  have hp:=canonicalParameters hr hd hN
  obtain ⟨ht,hf⟩:=closedWord_both_colors hp c hc
  have htag : (taggedClosedWord hd hN c).map (fun a => strongColor a.kind)=
      (closedWord c).map strongColor := by
    change (taggedClosedWord hd hN c).map (strongColor∘TaggedEdge.kind)=_
    rw [←List.map_map,taggedClosedWord_kinds]
  obtain ⟨n,hn,hl,_⟩:=CyclicColors.exists_colored_rotation (fun a => strongColor (TaggedEdge.kind a))
    (show true∈(taggedClosedWord hd hN c).map (fun a => strongColor a.kind) by rwa [htag])
    (show false∈(taggedClosedWord hd hN c).map (fun a => strongColor a.kind) by rwa [htag])
  have hchain:=(cyclicChain_rotate (taggedClosedWord_cyclic_compatible hr hd hN c hc) n).1
  obtain ⟨bs,hbs,he⟩:=tagged_cycle_normal_form (taggedAtoms ((taggedClosedWord hd hN c).rotate n))
    (taggedAtoms_alternate _ hchain) (by rwa [taggedAtoms_head_color]) (by rwa [taggedAtoms_last_color])
  have hk : ((taggedClosedWord hd hN c).rotate n).map TaggedEdge.kind=(closedWord c).rotate n := by
    rw [List.map_rotate,taggedClosedWord_kinds]
  have herase : sourceAtoms ((closedWord c).rotate n)=(bs.map TaggedBlock.run).flatMap pairAtoms := by
    rw [←hk,←taggedAtoms_erase,he,taggedPairs_erase]
  have hcounts:=sourceAtoms_counts ((closedWord c).rotate n)
    (cyclicChain_rotate (closedWord_cyclic_compatible hp c hc) n).1
  rw [herase,(paired_counts (bs.map TaggedBlock.run)).1,(paired_counts (bs.map TaggedBlock.run)).2.1,
    (paired_counts (bs.map TaggedBlock.run)).2.2,(rotated_exponents (closedWord c) n).1,
    (rotated_exponents (closedWord c) n).2.1,(rotated_exponents (closedWord c) n).2.2] at hcounts
  refine ⟨n,bs,hbs,he,?_,hcounts⟩
  intro C
  rw [←taggedAtoms_matrix C _ hchain,he,taggedPairs_matrix]

end Actual
end SubmittedGenus.CapFourMass.ActualComponent
