import Results.Genus.CapFourMass.TaggedLabelSlots
import Results.Genus.CapFourMass.TaggedModeWeights

/-! Complete canonical component choices inject into the actual signed run
slots. Shared labels are retained; extra independent slot choices are only a
later nonnegative majorization. -/
noncomputable section
namespace SubmittedGenus.CapFourMass.ActualComponent
open RawGraph RawGraph.Topology FixedPivot CarryLocalization
attribute [local instance] Classical.propDecidable Classical.decEq

lemma taggedModeLabels_ofFn {B : Type*} (bs : List (TaggedBlock B)) (tag : B) :
    List.ofFn (taggedModeLabels bs tag)=tag::bs.map TaggedBlock.label := by
  induction bs generalizing tag with
  | nil => simp [taggedModeLabels,List.ofFn_succ]
  | cons b bs ih =>
    change List.ofFn (Fin.cons tag (taggedModeLabels bs b.label))=tag::b.label::bs.map TaggedBlock.label
    rw [List.ofFn_succ]
    change tag::List.ofFn (taggedModeLabels bs b.label)=tag::b.label::bs.map TaggedBlock.label
    rw [ih]

lemma taggedModeLabels_mem {B : Type*} (bs : List (TaggedBlock B)) (tag b : B)
    (hb : tag=b ∨ ∃q∈bs,q.label=b) : ∃i,taggedModeLabels bs tag i=b := by
  apply List.mem_ofFn.mp
  rw [taggedModeLabels_ofFn]
  rcases hb with rfl | ⟨q,hq,he⟩
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,he⟩)

lemma choiceMode_injective : Function.Injective choiceMode := by
  intro b c he
  cases b <;> cases c <;> norm_num [choiceMode] at *

section Source
variable {r N d : ℕ} (hr : 0<r) (hd : 0<d) (hN : d<N) (hbig : 2*d<N)

/-- Extend one actual component assignment only for indexing the complete
signed word; every owned canonical label retains its original choice. -/
def componentChoice (c : Component (r+N) r (r+d)) (b : ModeFiber hr hN hbig c→Bool) :
    Option (CarryRepresentative N d hN)→Mode
  | none => 0
  | some a => if ha : owner hr hN hbig a=c then choiceMode (b ⟨a,ha⟩) else 0

@[simp] lemma componentChoice_owned (c : Component (r+N) r (r+d))
    (b : ModeFiber hr hN hbig c→Bool) (a : ModeFiber hr hN hbig c) :
    componentChoice hr hN hbig c b (some a.val)=choiceMode (b a) := by
  simp only [componentChoice,dif_pos a.property]

/-- Coverage, rather than an assumed independence of labels, gives injection. -/
lemma component_slot_injective (c : Component (r+N) r (r+d))
    (bs : List (TaggedBlock (Option (CarryRepresentative N d hN))))
    (tag : Option (CarryRepresentative N d hN))
    (hcover : ∀a : ModeFiber hr hN hbig c,∃i,taggedModeLabels bs tag i=some a.val) :
    Function.Injective (fun b : ModeFiber hr hN hbig c→Bool =>
      taggedModeStates (componentChoice hr hN hbig c b) bs (componentChoice hr hN hbig c b tag)) := by
  intro b b' he
  simp only [taggedModeStates_comp] at he
  funext a
  obtain ⟨i,hi⟩:=hcover a
  have hh:=congrFun he i
  change componentChoice hr hN hbig c b (taggedModeLabels bs tag i)=
    componentChoice hr hN hbig c b' (taggedModeLabels bs tag i) at hh
  rw [hi,componentChoice_owned,componentChoice_owned] at hh
  exact choiceMode_injective hh

include hd in
lemma actual_path_slot_coverage (c : Component (r+N) r (r+d))
    (hc : (freeComponentOrder (r+N) r (r+d) c).cycle=false) (hn : edgeCount c≠0)
    (pre post : Option StrongRun) (tag : Option (CarryRepresentative N d hN))
    (n : ℕ) (hn' : 1≤n) (bs : List (TaggedBlock (Option (CarryRepresentative N d hN))))
    (he : taggedAtoms (taggedPathWord hd hN c)=(TaggedPathCode.carried pre tag n hn' bs post).atoms)
    (a : ModeFiber hr hN hbig c) : ∃i,taggedModeLabels bs tag i=some a.val := by
  have hm:=component_mode_label_coverage hr hd hN hbig c hn a
  simp only [taggedSourceWord,hc,Bool.false_eq_true,if_false] at hm
  obtain ⟨k,hk,hmem⟩:=carry_mem_taggedAtoms _ (taggedPathWord_compatible hr hd hN c) _ hm
  rw [he] at hmem
  apply taggedModeLabels_mem
  simp only [TaggedPathCode.atoms,List.mem_append,List.mem_singleton] at hmem
  rcases hmem with ((hpre | htag) | hbs) | hpost
  · cases pre <;> simp at hpre
  · left
    injection htag with hlabel
    exact hlabel.symm
  · exact Or.inr (tagged_pair_carry_mem _ k hk bs hbs)
  · cases post <;> simp at hpost

include hd in
lemma actual_cycle_slot_coverage (c : Component (r+N) r (r+d))
    (hc : (freeComponentOrder (r+N) r (r+d) c).cycle=true)
    (n : ℕ) (b : TaggedBlock (Option (CarryRepresentative N d hN)))
    (bs : List (TaggedBlock (Option (CarryRepresentative N d hN))))
    (he : taggedAtoms ((taggedClosedWord hd hN c).rotate n)=(b::bs).flatMap taggedPair)
    (a : ModeFiber hr hN hbig c) : ∃i,taggedModeLabels bs b.label i=some a.val := by
  have hmin:=(freeComponentOrder (r+N) r (r+d) c).cycle_min hc
  have hn : edgeCount c≠0:=by change 3≤edgeCount c at hmin; omega
  have hm:=component_mode_label_coverage hr hd hN hbig c hn a
  simp only [taggedSourceWord,hc,if_true] at hm
  have hrot : TaggedEdge.carry (some a.val)∈(taggedClosedWord hd hN c).rotate n:=List.mem_rotate.mpr hm
  obtain ⟨k,hk,hmem⟩:=carry_mem_taggedAtoms _
    (cyclicChain_rotate (taggedClosedWord_cyclic_compatible hr hd hN c hc) n).1 _ hrot
  rw [he] at hmem
  obtain ⟨q,hq,hlabel⟩:=tagged_pair_carry_mem _ k hk (b::bs) hmem
  apply taggedModeLabels_mem
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · exact Or.inl hlabel
  · exact Or.inr ⟨q,hq,hlabel⟩

end Source
end SubmittedGenus.CapFourMass.ActualComponent
