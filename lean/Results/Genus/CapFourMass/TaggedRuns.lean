import Results.Genus.CapFourMass.CompilerCounts

/-! Maximal runs retain a source label on carry edges.  The label is not
removed by the color grouping used in the analytic compiler. -/
noncomputable section
namespace SubmittedGenus.CapFourMass.ActualComponent
open RawGraph

inductive TaggedEdge (B : Type*)
  | strong
  | restricted
  | carry (label : B)

def TaggedEdge.kind {B : Type*} : TaggedEdge B→EdgeKind
  | .strong => .strong
  | .restricted => .restricted
  | .carry _ => .carry

/-- Besides the source E adjacency restriction, adjacent equally colored
edges agree in their carry-component label. -/
def TaggedCompatible {B : Type*} (a b : TaggedEdge B) : Prop :=
  CompatibleKinds a.kind b.kind ∧ (a.kind=b.kind → a=b)

lemma tagged_run_chain {B : Type*} (l : List (TaggedEdge B))
    (hl : l.IsChain TaggedCompatible) {g : List (TaggedEdge B)}
    (hg : g∈RunSegmentation.runs TaggedEdge.kind l) : g.IsChain TaggedCompatible := by
  have hi : List.IsInfix g l := by
    rw [←RunSegmentation.flatten_runs TaggedEdge.kind l]
    exact List.infix_of_mem_flatten hg
  obtain ⟨a,b,he⟩:=hi
  subst l
  exact hl.left_of_append.right_of_append

/-- Every actual carry tag remains constant throughout its maximal carry run. -/
theorem tagged_run_constant {B : Type*} (l : List (TaggedEdge B))
    (hl : l.IsChain TaggedCompatible) {g : List (TaggedEdge B)}
    (hg : g∈RunSegmentation.runs TaggedEdge.kind l)
    (a : TaggedEdge B) (ha : a∈g) :
    a=g.head (RunSegmentation.run_nonempty TaggedEdge.kind l hg) := by
  have heq : g.IsChain Eq := (tagged_run_chain l hl hg).imp_of_mem_imp (by
    intro a b ha hb hab
    apply hab.2
    rw [RunSegmentation.run_constant TaggedEdge.kind l hg a ha,
      RunSegmentation.run_constant TaggedEdge.kind l hg b hb])
  cases g with
  | nil => simp at ha
  | cons b bs =>
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · rfl
    · exact (heq.rel_cons ha).symm

/-- Products of arbitrary signed carry matrices group exactly by the same
source runs, before any absolute value is introduced. -/
theorem tagged_run_product {B M : Type*} [Monoid M] (l : List (TaggedEdge B))
    (hl : l.IsChain TaggedCompatible) (f : TaggedEdge B→M) {g : List (TaggedEdge B)}
    (hg : g∈RunSegmentation.runs TaggedEdge.kind l) :
    (g.map f).prod=(f (g.head (RunSegmentation.run_nonempty TaggedEdge.kind l hg)))^g.length := by
  have hm : g.map f=List.replicate g.length (f (g.head (RunSegmentation.run_nonempty TaggedEdge.kind l hg))) := by
    have hh : ∀x∈g.map f,x=f (g.head (RunSegmentation.run_nonempty TaggedEdge.kind l hg)) := by
      intro x hx
      obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hx
      rw [tagged_run_constant l hl hg a ha]
    simpa only [List.length_map] using List.eq_replicate_length.mpr hh
  rw [hm,List.prod_replicate]

lemma tagged_restricted_singleton {B : Type*} (l : List (TaggedEdge B))
    (hl : l.IsChain TaggedCompatible) {g : List (TaggedEdge B)}
    (hg : g∈RunSegmentation.runs TaggedEdge.kind l)
    (he : g.head (RunSegmentation.run_nonempty TaggedEdge.kind l hg)=.restricted) :
    g=[.restricted] := by
  have hc:=tagged_run_chain l hl hg
  cases g with
  | nil => exact (RunSegmentation.run_nonempty TaggedEdge.kind l hg rfl).elim
  | cons a bs =>
    have ha : a=.restricted := he
    subst a
    cases bs with
    | nil => rfl
    | cons b bs =>
      have hb:=tagged_run_constant l hl hg b (by simp)
      change b=.restricted at hb
      have hh:=hc.rel
      rw [hb] at hh
      exact False.elim (by simpa [TaggedEdge.kind] using hh.1.1 rfl)

end SubmittedGenus.CapFourMass.ActualComponent
