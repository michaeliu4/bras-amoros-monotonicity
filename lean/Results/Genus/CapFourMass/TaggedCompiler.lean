import Results.Genus.CapFourMass.TaggedRuns
import Results.Genus.RawGraph.RunMap

/-! The typed source compiler retains one canonical label per carry block. -/
noncomputable section
namespace SubmittedGenus.CapFourMass.ActualComponent
open RawGraph

inductive TaggedAtom (B : Type*)
  | strong (run : StrongRun)
  | carry (label : B) (length : ℕ) (positive : 1≤length)

def TaggedAtom.erase {B : Type*} : TaggedAtom B→AtomicRun
  | .strong s => .strong s
  | .carry _ n hn => .carry n hn

def compileTaggedRun {B : Type*} [Inhabited B] (g : List (TaggedEdge B)) : TaggedAtom B :=
  if h : g=[] then .carry default 1 (by omega) else
    match g.head h with
    | .strong => .strong (.full g.length (List.length_pos_iff.mpr h))
    | .restricted => .strong .restricted
    | .carry b => .carry b g.length (List.length_pos_iff.mpr h)

lemma compileTaggedRun_erase {B : Type*} [Inhabited B] (g : List (TaggedEdge B)) :
    (compileTaggedRun g).erase=compileRun (g.map TaggedEdge.kind) := by
  cases g with
  | nil => rfl
  | cons a g =>
    cases a <;> simp [compileTaggedRun,compileRun,TaggedAtom.erase,TaggedEdge.kind]

def taggedAtoms {B : Type*} [Inhabited B] (l : List (TaggedEdge B)) : List (TaggedAtom B) :=
  (RunSegmentation.runs TaggedEdge.kind l).map compileTaggedRun

/-- Dropping only the mode labels recovers the original typed compiler exactly. -/
lemma taggedAtoms_erase {B : Type*} [Inhabited B] (l : List (TaggedEdge B)) :
    (taggedAtoms l).map TaggedAtom.erase=sourceAtoms (l.map TaggedEdge.kind) := by
  unfold taggedAtoms sourceAtoms
  rw [RunSegmentation.runs_map]
  simp only [List.map_map,Function.comp_def,compileTaggedRun_erase]

lemma taggedAtoms_alternate {B : Type*} [Inhabited B] (l : List (TaggedEdge B))
    (hl : l.IsChain TaggedCompatible) :
    (taggedAtoms l).IsChain (fun a b => a.erase.isStrong≠b.erase.isStrong) := by
  have hm : (l.map TaggedEdge.kind).IsChain CompatibleKinds :=
    (List.isChain_map TaggedEdge.kind).mpr (hl.imp (fun _ _ h => h.1))
  have hh:=sourceAtoms_alternate (l.map TaggedEdge.kind) hm
  rw [←taggedAtoms_erase] at hh
  exact (List.isChain_map TaggedAtom.erase).mp hh

structure TaggedBlock (B : Type*) where
  run : CoupledRun
  label : B

def taggedPair {B : Type*} (b : TaggedBlock B) : List (TaggedAtom B) :=
  [.strong b.run.strong,.carry b.label b.run.carryLength b.run.carryPositive]

lemma tagged_pair_suffix {B : Type*} (l : List (TaggedAtom B)) :
    l.IsChain (fun a b => a.erase.isStrong≠b.erase.isStrong) →
    (l.map (fun a => a.erase.isStrong)).head?=some true →
    ∃ (bs : List (TaggedBlock B)) (post : Option StrongRun),
      l=bs.flatMap taggedPair ++ post.toList.map TaggedAtom.strong := by
  induction l using List.twoStepInduction with
  | nil => intro _ hf; simp at hf
  | singleton a =>
    intro _ hf
    cases a with
    | carry b n hn => simp [TaggedAtom.erase,AtomicRun.isStrong] at hf
    | strong s => exact ⟨[],some s,rfl⟩
  | cons_cons a b l ih _ =>
    intro hchain hfirst
    cases a with
    | carry b n hn => simp [TaggedAtom.erase,AtomicRun.isStrong] at hfirst
    | strong s =>
      cases b with
      | strong t => exact (hchain.rel rfl).elim
      | carry tag n hn =>
        let block : TaggedBlock B:=⟨⟨s,n,hn⟩,tag⟩
        by_cases hl : l=[]
        · subst l
          exact ⟨[block],none,rfl⟩
        · have hf : (l.map (fun a => a.erase.isStrong)).head?=some true := by
            cases l with
            | nil => contradiction
            | cons a l =>
              have hh:=hchain.tail.rel
              cases a <;> simp_all [TaggedAtom.erase,AtomicRun.isStrong]
          obtain ⟨bs,post,he⟩:=ih hchain.tail.tail hf
          exact ⟨block::bs,post,by simp [taggedPair,block,he]⟩

inductive TaggedPathCode (B : Type*)
  | pure (run : Option StrongRun)
  | carried (pre : Option StrongRun) (label : B) (length : ℕ) (positive : 1≤length)
      (blocks : List (TaggedBlock B)) (post : Option StrongRun)

def TaggedPathCode.atoms {B : Type*} : TaggedPathCode B→List (TaggedAtom B)
  | .pure s => s.toList.map TaggedAtom.strong
  | .carried pre tag n hn bs post => pre.toList.map TaggedAtom.strong ++
      [.carry tag n hn] ++ bs.flatMap taggedPair ++ post.toList.map TaggedAtom.strong

def TaggedPathCode.erase {B : Type*} : TaggedPathCode B→PathCode
  | .pure s => .pure s
  | .carried pre _ n hn bs post => .carried pre n hn (bs.map TaggedBlock.run) post

/-- Every labelled path has the same optional-frame normal form while retaining
all complete-mode labels, including the leading carry block. -/
theorem tagged_path_normal_form {B : Type*} (l : List (TaggedAtom B))
    (hchain : l.IsChain (fun a b => a.erase.isStrong≠b.erase.isStrong)) :
    ∃ q : TaggedPathCode B,l=q.atoms := by
  cases l with
  | nil => exact ⟨.pure none,rfl⟩
  | cons a l =>
    cases a with
    | strong s =>
      cases l with
      | nil => exact ⟨.pure (some s),rfl⟩
      | cons b l =>
        cases b with
        | strong t => exact (hchain.rel rfl).elim
        | carry tag n hn =>
          by_cases hl : l=[]
          · subst l
            exact ⟨.carried (some s) tag n hn [] none,rfl⟩
          · have hf : (l.map (fun a => a.erase.isStrong)).head?=some true := by
              cases l with
              | nil => contradiction
              | cons a l =>
                have hh:=hchain.tail.rel
                cases a <;> simp_all [TaggedAtom.erase,AtomicRun.isStrong]
            obtain ⟨bs,post,he⟩:=tagged_pair_suffix l hchain.tail.tail hf
            exact ⟨.carried (some s) tag n hn bs post,by simp [TaggedPathCode.atoms,he]⟩
    | carry tag n hn =>
      by_cases hl : l=[]
      · subst l
        exact ⟨.carried none tag n hn [] none,rfl⟩
      · have hf : (l.map (fun a => a.erase.isStrong)).head?=some true := by
          cases l with
          | nil => contradiction
          | cons a l =>
            have hh:=hchain.rel
            cases a <;> simp_all [TaggedAtom.erase,AtomicRun.isStrong]
        obtain ⟨bs,post,he⟩:=tagged_pair_suffix l hchain.tail hf
        exact ⟨.carried none tag n hn bs post,by simp [TaggedPathCode.atoms,he]⟩

lemma TaggedPathCode.atoms_erase {B : Type*} (q : TaggedPathCode B) :
    q.atoms.map TaggedAtom.erase=q.erase.atoms := by
  cases q with
  | pure s => cases s <;> rfl
  | carried pre tag n hn bs post =>
    have hb : (bs.flatMap taggedPair).map TaggedAtom.erase=(bs.map TaggedBlock.run).flatMap pairAtoms := by
      induction bs with
      | nil => rfl
      | cons b bs ih => simp [List.flatMap_cons,taggedPair,pairAtoms,TaggedAtom.erase,ih]
    simp only [TaggedPathCode.atoms,TaggedPathCode.erase,PathCode.atoms,List.map_append,List.map_cons,
      List.map_nil,TaggedAtom.erase,hb,List.map_map,Function.comp_def]

/-- Strong-first/carry-last cyclic lists pair without losing any labels. -/
theorem tagged_cycle_normal_form {B : Type*} (l : List (TaggedAtom B))
    (hchain : l.IsChain (fun a b => a.erase.isStrong≠b.erase.isStrong))
    (hfirst : (l.map (fun a => a.erase.isStrong)).head?=some true)
    (hlast : (l.map (fun a => a.erase.isStrong)).getLast?=some false) :
    ∃ bs : List (TaggedBlock B),bs≠[] ∧ l=bs.flatMap taggedPair := by
  obtain ⟨bs,post,he⟩:=tagged_pair_suffix l hchain hfirst
  cases post with
  | none =>
    simp only [Option.toList_none,List.map_nil,List.append_nil] at he
    refine ⟨bs,?_,he⟩
    intro hb
    subst bs
    simp only [List.flatMap_nil] at he
    subst l
    simp at hfirst
  | some s =>
    rw [he] at hlast
    simp [TaggedAtom.erase,AtomicRun.isStrong] at hlast

lemma taggedPairs_erase {B : Type*} (bs : List (TaggedBlock B)) :
    (bs.flatMap taggedPair).map TaggedAtom.erase=(bs.map TaggedBlock.run).flatMap pairAtoms := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [List.flatMap_cons,taggedPair,pairAtoms,TaggedAtom.erase,ih]

end SubmittedGenus.CapFourMass.ActualComponent
