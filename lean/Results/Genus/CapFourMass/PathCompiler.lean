import Results.Genus.CapFourMass.CoupledCompiler

/-! Complete path compilation, including no-carry and zero-edge components. -/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFourMass.ActualComponent
open RawGraph RawGraph.Topology

/-- A strong-first alternating tail is paired except for its optional last
strong run. The latter is an ordinary endpoint operator, never a zero-carry block. -/
lemma pair_atoms_with_suffix (l : List AtomicRun) :
    l.IsChain (fun a b => a.isStrong≠b.isStrong) →
    (l.map AtomicRun.isStrong).head?=some true →
    ∃ (bs : List CoupledRun) (post : Option StrongRun),
      l=bs.flatMap pairAtoms ++ post.toList.map AtomicRun.strong := by
  induction l using List.twoStepInduction with
  | nil => intro _ hf; simp at hf
  | singleton a =>
    intro _ hf
    cases a with
    | carry n hn => simp [AtomicRun.isStrong] at hf
    | strong s => exact ⟨[],some s,rfl⟩
  | cons_cons a b l ih _ =>
    intro hchain hfirst
    cases a with
    | carry n hn => simp [AtomicRun.isStrong] at hfirst
    | strong s =>
      cases b with
      | strong t => exact (hchain.rel rfl).elim
      | carry n hn =>
        let block : CoupledRun := ⟨s,n,hn⟩
        by_cases hl : l=[]
        · subst l
          exact ⟨[block],none,rfl⟩
        · have hfst : (l.map AtomicRun.isStrong).head?=some true := by
            cases l with
            | nil => contradiction
            | cons a l =>
              have hh := hchain.tail.rel
              cases a <;> simp_all [AtomicRun.isStrong]
          obtain ⟨bs,post,he⟩ := ih hchain.tail.tail hfst
          exact ⟨block::bs,post,by simp [pairAtoms,block,he]⟩

inductive PathCode
  | pure (run : Option StrongRun)
  | carried (pre : Option StrongRun) (length : ℕ) (positive : 1≤length)
      (blocks : List CoupledRun) (post : Option StrongRun)

def optionalStrongMatrix (s : Option StrongRun) : Matrix State State ℝ :=
  match s with | none => 1 | some s => s.matrix

def PathCode.atoms : PathCode→List AtomicRun
  | .pure s => s.toList.map AtomicRun.strong
  | .carried pre n hn bs post => pre.toList.map AtomicRun.strong ++
      [.carry n hn] ++ bs.flatMap pairAtoms ++ post.toList.map AtomicRun.strong

def PathCode.matrix : PathCode→Matrix State State ℝ
  | .pure s => optionalStrongMatrix s
  | .carried pre n _ bs post => optionalStrongMatrix pre * carryMatrix^n *
      (bs.map CoupledRun.matrix).prod * optionalStrongMatrix post

/-- All alternating actual run lists are covered; no positive carry block is
introduced for an isolated vertex or an entirely strong path. -/
theorem path_atoms_normal_form (l : List AtomicRun)
    (hchain : l.IsChain (fun a b => a.isStrong≠b.isStrong)) :
    ∃ q : PathCode,l=q.atoms := by
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
        | carry n hn =>
          by_cases hl : l=[]
          · subst l
            exact ⟨.carried (some s) n hn [] none,rfl⟩
          · have hf : (l.map AtomicRun.isStrong).head?=some true := by
              cases l with
              | nil => contradiction
              | cons a l =>
                have hh := hchain.tail.rel
                cases a <;> simp_all [AtomicRun.isStrong]
            obtain ⟨bs,post,he⟩ := pair_atoms_with_suffix l hchain.tail.tail hf
            exact ⟨.carried (some s) n hn bs post,by simp [PathCode.atoms,he]⟩
    | carry n hn =>
      by_cases hl : l=[]
      · subst l
        exact ⟨.carried none n hn [] none,rfl⟩
      · have hf : (l.map AtomicRun.isStrong).head?=some true := by
          cases l with
          | nil => contradiction
          | cons a l =>
            have hh := hchain.rel
            cases a <;> simp_all [AtomicRun.isStrong]
        obtain ⟨bs,post,he⟩ := pair_atoms_with_suffix l hchain.tail hf
        exact ⟨.carried none n hn bs post,by simp [PathCode.atoms,he]⟩

lemma optionalStrong_matrix (s : Option StrongRun) :
    ((s.toList.map AtomicRun.strong).map AtomicRun.matrix).prod=optionalStrongMatrix s := by
  cases s <;> simp [optionalStrongMatrix,AtomicRun.matrix]

lemma PathCode.atoms_matrix (q : PathCode) : (q.atoms.map AtomicRun.matrix).prod=q.matrix := by
  cases q with
  | pure s => exact optionalStrong_matrix s
  | carried pre n hn bs post =>
    simp only [PathCode.atoms,List.map_append,List.prod_append,List.map_cons,List.map_nil,
      List.prod_cons,List.prod_nil,mul_one,optionalStrong_matrix,paired_matrix,AtomicRun.matrix,PathCode.matrix]

/-- The exact actual source path has a typed spectral-run normal form, with
its genuine endpoint vectors and one full weight per physical vertex. -/
theorem actual_path_code {m r p : ℕ} (hp : RawGraph.Parameters m r p 4)
    (c : Component m r p) (hc : (freeComponentOrder m r p c).cycle=false) :
    ∃ q : PathCode,sourceAtoms (pathWord c)=q.atoms ∧
      componentMass c=domainHalf c 0 ⬝ᵥ (q.matrix*ᵥ domainHalf c (Fin.last _)) := by
  obtain ⟨q,he⟩ := path_atoms_normal_form (sourceAtoms (pathWord c))
    (sourceAtoms_alternate _ (pathWord_compatible hp c))
  refine ⟨q,he,?_⟩
  rw [componentMass_path_eq_word hp c hc,← sourceAtoms_matrix _ (pathWord_compatible hp c),he,
    PathCode.atoms_matrix]

end SubmittedGenus.CapFourMass.ActualComponent
