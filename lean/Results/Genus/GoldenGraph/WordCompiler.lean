import Results.Genus.GoldenGraph.SourceEndpoints
import Results.Genus.GoldenGraph.PaidRunCounts
import Results.Genus.GoldenGraph.RunCountBridge
import Results.Genus.GoldenSpectral.PathBounds

/-! The actual source words interpreted in the original golden-q matrices. -/
namespace SubmittedGenus.GoldenGraph.Source
open RawGraph RawGraph.SourceModel RawGraph.Topology RawGraph.Transfer
open CapFourMass.ActualComponent GoldenSpectral CapFiveMass.MatrixSource
open scoped BigOperators Matrix
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

def edgeMatrix : EdgeKind→Matrix State State ℝ
  | .strong => strongMatrix
  | .restricted => restrictedMatrix
  | .carry => carryMatrix

def atomMatrix : AtomicRun→Matrix State State ℝ
  | .strong s => runMatrix s
  | .carry n _ => carryMatrix^n

lemma kind_matrix {m r p : ℕ} (i j : Fin (m-1)) :
    edgeMatrix (kind r p i j)=baseMatrix r p i j := by
  unfold kind baseMatrix
  split_ifs <;> rfl

lemma pathWord_matrix {m r p : ℕ} (c : Component m r p) :
    ((pathWord c).map edgeMatrix).prod=matrixRun (edgeCount c) (baseEdges c) := by
  rw [matrixRun_eq_ofFn_prod]
  simp only [pathWord,List.map_ofFn,Function.comp_def]
  congr 2
  funext j
  rw [kind_matrix]
  simp only [baseEdges,dif_pos j.isLt]

lemma closedWord_matrix {m r p : ℕ} (c : Component m r p) :
    ((closedWord c).map edgeMatrix).prod=matrixRun (edgeCount c) (baseEdges c)*baseClose c := by
  simp only [closedWord,List.map_append,List.map_cons,List.map_nil,List.prod_append,List.prod_cons,
    List.prod_nil,mul_one,pathWord_matrix,kind_matrix,baseClose]

lemma compileRun_matrix (l : List EdgeKind) (hl : l.IsChain CompatibleKinds)
    {g : List EdgeKind} (hg : g∈RunSegmentation.runs id l) :
    atomMatrix (compileRun g)=(g.map edgeMatrix).prod := by
  have hn:=RunSegmentation.run_nonempty id l hg
  have hpower : (g.map edgeMatrix).prod=edgeMatrix (g.head hn)^g.length :=
    RunSegmentation.run_product id l edgeMatrix hg
  rw [hpower]
  unfold compileRun
  rw [dif_neg hn]
  split
  · simp_all [atomMatrix,runMatrix,edgeMatrix]
  · have he : g=[.restricted] := restricted_run_singleton l hl hg (by assumption)
    subst g
    simp [atomMatrix,runMatrix,edgeMatrix]
  · simp_all [atomMatrix,edgeMatrix]

lemma sourceAtoms_matrix (l : List EdgeKind) (hl : l.IsChain CompatibleKinds) :
    ((sourceAtoms l).map atomMatrix).prod=(l.map edgeMatrix).prod := by
  rw [RunSegmentation.product_runs id l]
  unfold sourceAtoms
  rw [List.map_map]
  congr 1
  exact List.map_congr_left (fun g hg => compileRun_matrix l hl hg)

lemma pairAtoms_matrix (b : CoupledRun) : ((pairAtoms b).map atomMatrix).prod=blockMatrix b := by
  simp only [pairAtoms,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]
  rfl

lemma paired_matrix (bs : List CoupledRun) :
    ((bs.flatMap pairAtoms).map atomMatrix).prod=(bs.map blockMatrix).prod := by
  simp only [List.flatMap_def,List.map_flatten,List.prod_flatten,List.map_map,Function.comp_def,pairAtoms_matrix]

lemma optional_matrix (s : Option StrongRun) :
    ((s.toList.map AtomicRun.strong).map atomMatrix).prod=frameMatrix s := by
  cases s <;> simp [frameMatrix,atomMatrix]

lemma path_atoms_matrix (q : CapFourMass.ActualComponent.PathCode) : (q.atoms.map atomMatrix).prod=pathMatrix q := by
  cases q with
  | pure s => exact optional_matrix s
  | carried pre n hn bs post =>
    simp only [CapFourMass.ActualComponent.PathCode.atoms,List.map_append,List.prod_append,List.map_cons,List.map_nil,
      List.prod_cons,List.prod_nil,mul_one,optional_matrix,paired_matrix,atomMatrix,pathMatrix]

lemma pathRunCount_eq_atomic (q : CapFourMass.ActualComponent.PathCode) : pathRunCount q=atomicStrongRuns q.atoms := by
  cases q with
  | pure s => rw [pathCode_strong_runs_pure]; cases s <;> rfl
  | carried pre n hn bs post =>
    rw [pathCode_strong_runs_carried]
    cases pre <;> cases post <;> rfl

/-- The actual source path and its golden-q interpretation use precisely the
same computed typed word, including zero edges and pure carry. -/
theorem actual_path_code_le {m r p : ℕ} (hp : Parameters m r p 4) (c : Component m r p)
    (hc : (freeComponentOrder m r p c).cycle=false) :
    ∃ q : CapFourMass.ActualComponent.PathCode,sourceAtoms (pathWord c)=q.atoms ∧
      componentMass c≤halfWeights c 0 ⬝ᵥ (pathMatrix q*ᵥ halfWeights c (edgeCount c)) := by
  obtain ⟨q,hq⟩:=path_atoms_normal_form (sourceAtoms (pathWord c))
    (sourceAtoms_alternate _ (pathWord_compatible hp c))
  refine ⟨q,hq,?_⟩
  have h:=componentMass_path_le_base hp c hc
  rw [← pathWord_matrix,← sourceAtoms_matrix _ (pathWord_compatible hp c),hq,path_atoms_matrix] at h
  exact h

lemma cycleCut_first {m r p : ℕ} (hp : Parameters m r p 4) (c : Component m r p)
    (hc : (freeComponentOrder m r p c).cycle=true) :
    (((closedWord c).rotate (cycleCut hp c hc)).map strongColor).head?=some true :=
  (Classical.choose_spec (actual_cycle_run_cut hp c hc)).1

/-- This is the same actual carry-last cycle cut used by the physical paid-run
count. Every positive carry run, matrix factor, and source edge is retained. -/
theorem actual_cycle_code_le {m r p : ℕ} (hp : Parameters m r p 4) (c : Component m r p)
    (hc : (freeComponentOrder m r p c).cycle=true) :
    ∃ bs : List CoupledRun,bs≠[] ∧ sourceAtoms (sourceRunWord hp c)=bs.flatMap pairAtoms ∧
      componentMass c≤((bs.map blockMatrix).prod).trace := by
  have hword : sourceRunWord hp c=(closedWord c).rotate (cycleCut hp c hc) := by
    simp only [sourceRunWord,dif_pos hc]
  have hf : ((sourceAtoms (sourceRunWord hp c)).map AtomicRun.isStrong).head?=some true := by
    rw [sourceAtoms_head_color,hword]; exact cycleCut_first hp c hc
  have hl : ((sourceAtoms (sourceRunWord hp c)).map AtomicRun.isStrong).getLast?=some false := by
    rw [sourceAtoms_last_color,hword]; exact cycleCut_last hp c hc
  obtain ⟨bs,hbs,he⟩:=pair_alternating_atoms (sourceAtoms (sourceRunWord hp c))
    (sourceAtoms_alternate _ (sourceRunWord_compatible hp c)) hf hl
  refine ⟨bs,hbs,he,?_⟩
  calc
    componentMass c≤(((closedWord c).map edgeMatrix).prod).trace := by
      rw [closedWord_matrix]; exact componentMass_cycle_le_base hp c hc
    _=(((sourceRunWord hp c).map edgeMatrix).prod).trace := by
      rw [hword,matrix_word_trace_rotate]
    _=_ := by
      rw [← sourceAtoms_matrix _ (sourceRunWord_compatible hp c),he,paired_matrix]

end
end SubmittedGenus.GoldenGraph.Source
