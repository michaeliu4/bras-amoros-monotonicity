import Results.Genus.CapFourMass.PathCompiler
import Results.Genus.CapFourMass.RunBounds

/-! Typed spectral compilation conserves the original source edge exponents. -/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFourMass.ActualComponent
open RawGraph RawGraph.Topology

def AtomicRun.strongCount : AtomicRun→ℕ
  | .strong s => s.strongCount
  | .carry _ _ => 0

def AtomicRun.carryCount : AtomicRun→ℕ
  | .strong _ => 0
  | .carry n _ => n

def AtomicRun.restrictedCount : AtomicRun→ℕ
  | .strong s => s.restrictedCount
  | .carry _ _ => 0

lemma run_cost (l : List EdgeKind) {g : List EdgeKind} (hg : g∈RunSegmentation.runs id l)
    (f : EdgeKind→ℕ) : (g.map f).sum=g.length*f (g.head (RunSegmentation.run_nonempty id l hg)) := by
  have hm : g.map f=List.replicate g.length (f (g.head (RunSegmentation.run_nonempty id l hg))) := by
    have hc : ∀ x∈g.map f,x=f (g.head (RunSegmentation.run_nonempty id l hg)) := by
      intro x hx
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
      exact congrArg f (RunSegmentation.run_constant id l hg a ha)
    simpa only [List.length_map] using List.eq_replicate_length.mpr hc
  rw [hm,List.sum_replicate]
  rfl

lemma compileRun_counts (l : List EdgeKind) (hl : l.IsChain CompatibleKinds)
    {g : List EdgeKind} (hg : g∈RunSegmentation.runs id l) :
    (compileRun g).strongCount=strongLength g ∧ (compileRun g).carryCount=carryLength g ∧
      (compileRun g).restrictedCount=restrictedLength g := by
  have hn:=RunSegmentation.run_nonempty id l hg
  unfold strongLength carryLength restrictedLength
  rw [run_cost l hg,run_cost l hg,run_cost l hg]
  unfold compileRun
  rw [dif_neg hn]
  split
  · simp_all [AtomicRun.strongCount,AtomicRun.carryCount,AtomicRun.restrictedCount,
      StrongRun.strongCount,StrongRun.restrictedCount]
  · have he : g=[.restricted] := restricted_run_singleton l hl hg (by assumption)
    subst g
    simp [AtomicRun.strongCount,AtomicRun.carryCount,AtomicRun.restrictedCount,
      StrongRun.strongCount,StrongRun.restrictedCount]
  · simp_all [AtomicRun.strongCount,AtomicRun.carryCount,AtomicRun.restrictedCount]

lemma sourceAtoms_counts (l : List EdgeKind) (hl : l.IsChain CompatibleKinds) :
    ((sourceAtoms l).map AtomicRun.strongCount).sum=strongLength l ∧
    ((sourceAtoms l).map AtomicRun.carryCount).sum=carryLength l ∧
    ((sourceAtoms l).map AtomicRun.restrictedCount).sum=restrictedLength l := by
  obtain ⟨hs,hc,he⟩ := run_exponents_preserved l
  rw [hs,hc,he]
  unfold sourceAtoms
  simp only [List.map_map,Function.comp_def]
  constructor
  · congr 1
    exact List.map_congr_left (fun g hg => (compileRun_counts l hl hg).1)
  constructor
  · congr 1
    exact List.map_congr_left (fun g hg => (compileRun_counts l hl hg).2.1)
  · congr 1
    exact List.map_congr_left (fun g hg => (compileRun_counts l hl hg).2.2)

lemma paired_counts (bs : List CoupledRun) :
    ((bs.flatMap pairAtoms).map AtomicRun.strongCount).sum=(bs.map (fun b => b.strong.strongCount)).sum ∧
    ((bs.flatMap pairAtoms).map AtomicRun.carryCount).sum=(bs.map CoupledRun.carryLength).sum ∧
    ((bs.flatMap pairAtoms).map AtomicRun.restrictedCount).sum=(bs.map (fun b => b.strong.restrictedCount)).sum := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    simp only [List.flatMap_cons,List.map_append,List.sum_append,pairAtoms,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,AtomicRun.strongCount,AtomicRun.carryCount,AtomicRun.restrictedCount,
      add_zero,zero_add,ih.1,ih.2.1,ih.2.2]
    trivial

def optionalStrongCount (s : Option StrongRun) : ℕ := s.elim 0 StrongRun.strongCount
def optionalRestrictedCount (s : Option StrongRun) : ℕ := s.elim 0 StrongRun.restrictedCount

def PathCode.strongCount : PathCode→ℕ
  | .pure s => optionalStrongCount s
  | .carried pre _ _ bs post => optionalStrongCount pre +
      (bs.map (fun b => b.strong.strongCount)).sum+optionalStrongCount post

def PathCode.carryCount : PathCode→ℕ
  | .pure _ => 0
  | .carried _ n _ bs _ => n+(bs.map CoupledRun.carryLength).sum

def PathCode.restrictedCount : PathCode→ℕ
  | .pure s => optionalRestrictedCount s
  | .carried pre _ _ bs post => optionalRestrictedCount pre +
      (bs.map (fun b => b.strong.restrictedCount)).sum+optionalRestrictedCount post

lemma optional_atoms_counts (s : Option StrongRun) :
    ((s.toList.map AtomicRun.strong).map AtomicRun.strongCount).sum=optionalStrongCount s ∧
    ((s.toList.map AtomicRun.strong).map AtomicRun.carryCount).sum=0 ∧
    ((s.toList.map AtomicRun.strong).map AtomicRun.restrictedCount).sum=optionalRestrictedCount s := by
  cases s <;> simp [AtomicRun.strongCount,AtomicRun.carryCount,AtomicRun.restrictedCount,
    optionalStrongCount,optionalRestrictedCount]

lemma PathCode.atoms_counts (q : PathCode) :
    (q.atoms.map AtomicRun.strongCount).sum=q.strongCount ∧
    (q.atoms.map AtomicRun.carryCount).sum=q.carryCount ∧
    (q.atoms.map AtomicRun.restrictedCount).sum=q.restrictedCount := by
  cases q with
  | pure s => exact optional_atoms_counts s
  | carried pre n hn bs post =>
    simp only [PathCode.atoms,List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,
      List.sum_nil,optional_atoms_counts,paired_counts,AtomicRun.strongCount,AtomicRun.carryCount,
      AtomicRun.restrictedCount,PathCode.strongCount,PathCode.carryCount,PathCode.restrictedCount,
      add_zero,zero_add]
    trivial

/-- The exact cycle compiler conserves every source exponent, including the
restricted singleton E replacement. -/
theorem actual_cycle_coupled_counts {m r p : ℕ} (hp : RawGraph.Parameters m r p 4)
    (c : Component m r p) (hc : (freeComponentOrder m r p c).cycle=true) :
    ∃ bs : List CoupledRun,bs≠[] ∧
      componentMass c=((bs.map CoupledRun.matrix).prod).trace ∧
      (bs.map (fun b => b.strong.strongCount)).sum=strongLength (closedWord c) ∧
      (bs.map CoupledRun.carryLength).sum=carryLength (closedWord c) ∧
      (bs.map (fun b => b.strong.restrictedCount)).sum=restrictedLength (closedWord c) := by
  obtain ⟨n,bs,hbs,he,hm⟩ := actual_cycle_coupled hp c hc
  have hchain := (cyclicChain_rotate (closedWord_cyclic_compatible hp c hc) n).1
  have hcounts := sourceAtoms_counts ((closedWord c).rotate n) hchain
  rw [he,(paired_counts bs).1,(paired_counts bs).2.1,(paired_counts bs).2.2,
    (rotated_exponents (closedWord c) n).1,(rotated_exponents (closedWord c) n).2.1,
    (rotated_exponents (closedWord c) n).2.2] at hcounts
  exact ⟨bs,hbs,hm,hcounts⟩

/-- The typed open-path compiler likewise preserves all source exponents. -/
theorem actual_path_code_counts {m r p : ℕ} (hp : RawGraph.Parameters m r p 4)
    (c : Component m r p) (hc : (freeComponentOrder m r p c).cycle=false) :
    ∃ q : PathCode,
      componentMass c=domainHalf c 0 ⬝ᵥ (q.matrix*ᵥ domainHalf c (Fin.last _)) ∧
      q.strongCount=strongLength (pathWord c) ∧ q.carryCount=carryLength (pathWord c) ∧
      q.restrictedCount=restrictedLength (pathWord c) := by
  obtain ⟨q,he,hm⟩ := actual_path_code hp c hc
  have hcounts := sourceAtoms_counts (pathWord c) (pathWord_compatible hp c)
  rw [he,(PathCode.atoms_counts q).1,(PathCode.atoms_counts q).2.1,(PathCode.atoms_counts q).2.2] at hcounts
  exact ⟨q,hm,hcounts⟩

end SubmittedGenus.CapFourMass.ActualComponent
