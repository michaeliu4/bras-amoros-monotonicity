import Results.Genus.GoldenGraph.RunJunctions

/-! The submitted paid-run count matches the actual typed source compiler. -/
namespace SubmittedGenus.GoldenGraph
open RawGraph CapFourMass CapFourMass.ActualComponent
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

def atomicStrongRuns (l : List AtomicRun) : ℕ :=
  (l.map (fun a => if a.isStrong then 1 else 0)).sum

lemma atomicStrongRuns_append (l s : List AtomicRun) :
    atomicStrongRuns (l++s)=atomicStrongRuns l+atomicStrongRuns s := by
  simp [atomicStrongRuns]

/-- Maximal-run compilation preserves the number of strong runs, counting
both a D-power and the isolated E replacement as one run. -/
theorem sourceAtoms_strong_runs (l : List EdgeKind) :
    atomicStrongRuns (sourceAtoms l)=strongRunCount l := by
  unfold atomicStrongRuns sourceAtoms strongRunCount
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro g hg
  have hn:=RunSegmentation.run_nonempty id l hg
  change (if (compileRun g).isStrong then 1 else 0)=_
  rw [compileRun_color _ hn]
  have hhead : ∀ (g : List EdgeKind) (h : g≠[]),g.headD .carry=g.head h := by
    intro g h; cases g with
    | nil => contradiction
    | cons a l => rfl
  rw [hhead g hn]
  cases g.head hn <;> rfl

lemma paired_strong_runs (bs : List CoupledRun) :
    atomicStrongRuns (bs.flatMap pairAtoms)=bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    rw [List.flatMap_cons,atomicStrongRuns_append,ih]
    simp [atomicStrongRuns,pairAtoms,AtomicRun.isStrong,Nat.add_comm]

def optionalRunCount (s : Option StrongRun) : ℕ := if s.isSome then 1 else 0

lemma optional_strong_runs (s : Option StrongRun) :
    atomicStrongRuns (s.toList.map AtomicRun.strong)=optionalRunCount s := by
  cases s <;> rfl

lemma optionalRunCount_le_one (s : Option StrongRun) : optionalRunCount s≤1 := by
  cases s <;> simp [optionalRunCount]

lemma pathCode_strong_runs_pure (s : Option StrongRun) :
    atomicStrongRuns (PathCode.pure s).atoms=optionalRunCount s :=
  optional_strong_runs s

lemma pathCode_strong_runs_carried (pre : Option StrongRun) (n : ℕ) (hn : 1≤n)
    (bs : List CoupledRun) (post : Option StrongRun) :
    atomicStrongRuns (PathCode.carried pre n hn bs post).atoms=
      optionalRunCount pre+bs.length+optionalRunCount post := by
  simp only [PathCode.atoms,atomicStrongRuns_append,optional_strong_runs,paired_strong_runs]
  simp [atomicStrongRuns,AtomicRun.isStrong]

/-- Discarding two possible endpoint runs never claims more paid blocks than
are present in the actual typed carried-path normal form. -/
theorem pathCode_paid_le_blocks (pre : Option StrongRun) (n : ℕ) (hn : 1≤n)
    (bs : List CoupledRun) (post : Option StrongRun) :
    atomicStrongRuns (PathCode.carried pre n hn bs post).atoms-2≤bs.length := by
  rw [pathCode_strong_runs_carried]
  have hpre:=optionalRunCount_le_one pre
  have hpost:=optionalRunCount_le_one post
  omega

lemma pathCode_pure_paid_zero (s : Option StrongRun) :
    atomicStrongRuns (PathCode.pure s).atoms-2=0 := by
  rw [pathCode_strong_runs_pure]
  have hh:=optionalRunCount_le_one s
  omega

end
end SubmittedGenus.GoldenGraph
