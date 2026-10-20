import Results.Genus.CapFourMass.EdgeMatrices
import Results.Genus.RawGraph.RunSegmentation
import Results.Genus.RawGraph.MixedCycles
import Results.Genus.RawGraph.StrongEdgeCounts

/-! Actual D/E/C edge words and their source-order-preserving maximal runs. -/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFourMass.ActualComponent
open RawGraph RawGraph.SourceModel RawGraph.Topology RawGraph.Transfer
open CapFiveMass.MatrixSource

inductive EdgeKind
  | strong | restricted | carry
  deriving DecidableEq, BEq, Repr

def EdgeKind.matrix : EdgeKind→Matrix State State ℝ
  | .strong => strongMatrix
  | .restricted => restrictedMatrix
  | .carry => carryMatrix

def kind {m : ℕ} (r p : ℕ) (i j : Fin (m-1)) : EdgeKind :=
  if physical i+physical j=r ∨ physical i+physical j=p then
    if r<physical i ∧ r<physical j then .restricted else .strong
  else .carry

lemma kind_matrix {m r p : ℕ} (i j : Fin (m-1)) :
    (kind r p i j).matrix = baseMatrix r p i j := by
  unfold kind baseMatrix
  split_ifs <;> rfl

lemma kind_ne_carry_iff {m r p : ℕ} {i j : Fin (m-1)}
    (he : (rawGraph m r p).Adj i j) : kind r p i j≠.carry ↔ StrongRuns.StrongStep r p i j := by
  unfold kind StrongRuns.StrongStep
  split_ifs <;> simp_all

lemma kind_carry_iff {m r p : ℕ} (hp : Parameters m r p 4) {i j : Fin (m-1)}
    (he : (rawGraph m r p).Adj i j) : kind r p i j=.carry ↔ StrongRuns.CarryStep r p i j := by
  constructor
  · intro hk
    rcases StrongRuns.edge_strong_or_carry he with hs | hc
    · exact ((kind_ne_carry_iff he).2 hs hk).elim
    · exact hc
  · intro hc
    by_contra hne
    exact StrongRuns.strong_carry_disjoint hp i j ⟨(kind_ne_carry_iff he).1 hne,hc⟩

lemma kind_restricted_iff {m r p : ℕ} {i j : Fin (m-1)}
    (he : (rawGraph m r p).Adj i j) : kind r p i j=.restricted ↔
      StrongRuns.StrongStep r p i j ∧ r<physical i ∧ r<physical j := by
  unfold kind StrongRuns.StrongStep
  split_ifs <;> simp_all

/-- The E edge cannot touch another strong edge in the actual graph. -/
lemma restricted_neighbor_carry {m r p : ℕ} {i j k : Fin (m-1)}
    (he : (rawGraph m r p).Adj i j) (hk : kind r p i j=.restricted)
    (hj : (rawGraph m r p).Adj j k) (hne : i≠k) : StrongRuns.CarryStep r p j k := by
  obtain ⟨hs,_,hjhi⟩ := (kind_restricted_iff he).mp hk
  rcases StrongRuns.edge_strong_or_carry hj with hs' | hc
  · exact (hne (StrongRuns.high_strong_unique hjhi (StrongRuns.strongStep_symm hs) hs')).elim
  · exact hc

def pathWord {m r p : ℕ} (c : Component m r p) : List EdgeKind :=
  List.ofFn (fun j : Fin (edgeCount c) => kind r p (vertex c j.castSucc) (vertex c j.succ))

def closedWord {m r p : ℕ} (c : Component m r p) : List EdgeKind :=
  pathWord c ++ [kind r p (vertex c (Fin.last _)) (vertex c 0)]

@[simp] lemma pathWord_length {m r p : ℕ} (c : Component m r p) : (pathWord c).length=edgeCount c := by
  simp [pathWord]
@[simp] lemma closedWord_length {m r p : ℕ} (c : Component m r p) : (closedWord c).length=edgeCount c+1 := by
  simp [closedWord]

lemma matrixRun_eq_ofFn_prod {A : Type*} [Fintype A] [DecidableEq A]
    (n : ℕ) (E : ℕ→Matrix A A ℝ) :
    matrixRun n E = (List.ofFn (fun j : Fin n => E j.val)).prod := by
  induction n generalizing E with
  | zero => simp [matrixRun]
  | succ n ih =>
    rw [matrixRun,ih,List.ofFn_succ,List.prod_cons]
    rfl

lemma pathWord_matrix {m r p : ℕ} (c : Component m r p) :
    ((pathWord c).map EdgeKind.matrix).prod=matrixRun (edgeCount c) (baseEdges c) := by
  rw [matrixRun_eq_ofFn_prod]
  simp only [pathWord,List.map_ofFn,Function.comp_def]
  congr 2
  funext j
  rw [kind_matrix]
  simp only [baseEdges,dif_pos j.isLt]

lemma closedWord_matrix {m r p : ℕ} (c : Component m r p) :
    ((closedWord c).map EdgeKind.matrix).prod=matrixRun (edgeCount c) (baseEdges c)*baseClose c := by
  simp only [closedWord,List.map_append,List.map_cons,List.map_nil,List.prod_append,List.prod_cons,
    List.prod_nil,mul_one,pathWord_matrix,kind_matrix,baseClose]

/-- This is a computed maximal-run layout of the actual path edge word. -/
def pathRuns {m r p : ℕ} (c : Component m r p) : List (List EdgeKind) :=
  RunSegmentation.runs id (pathWord c)

/-- The same compiler is valid for the cyclic word; a cyclic rotation is used
later to place a strong/carry transition at the two outer run boundaries. -/
def closedRuns {m r p : ℕ} (c : Component m r p) : List (List EdgeKind) :=
  RunSegmentation.runs id (closedWord c)

lemma pathRuns_flatten {m r p : ℕ} (c : Component m r p) : (pathRuns c).flatten=pathWord c :=
  RunSegmentation.flatten_runs _ _
lemma closedRuns_flatten {m r p : ℕ} (c : Component m r p) : (closedRuns c).flatten=closedWord c :=
  RunSegmentation.flatten_runs _ _

lemma pathRuns_matrix {m r p : ℕ} (c : Component m r p) :
    matrixRun (edgeCount c) (baseEdges c) =
      ((pathRuns c).map (fun g : List EdgeKind => (g.map EdgeKind.matrix).prod)).prod := by
  rw [← pathWord_matrix]
  exact RunSegmentation.product_runs id _ _

lemma closedRuns_matrix {m r p : ℕ} (c : Component m r p) :
    matrixRun (edgeCount c) (baseEdges c)*baseClose c =
      ((closedRuns c).map (fun g : List EdgeKind => (g.map EdgeKind.matrix).prod)).prod := by
  rw [← closedWord_matrix]
  exact RunSegmentation.product_runs id _ _

lemma actual_run_power (l : List EdgeKind) {g : List EdgeKind}
    (hg : g∈RunSegmentation.runs id l) :
    (g.map EdgeKind.matrix).prod=(g.head (RunSegmentation.run_nonempty id l hg)).matrix^g.length := by
  exact RunSegmentation.run_product id l EdgeKind.matrix hg

lemma actual_runs_alternate (l : List EdgeKind) :
    (RunSegmentation.runs id l).IsChain (fun g h => ∃ hg : g≠[],∃ hh : h≠[],g.head hg≠h.head hh) :=
  RunSegmentation.runs_head_alternate id l

lemma source_path_le_runs {m r p : ℕ} (hp : Parameters m r p 4)
    (c : Component m r p) (hc : (freeComponentOrder m r p c).cycle=false) :
    componentMass c ≤ halfWeights c 0 ⬝ᵥ
      ((((pathRuns c).map (fun g : List EdgeKind => (g.map EdgeKind.matrix).prod)).prod)*ᵥ halfWeights c (edgeCount c)) := by
  rw [← pathRuns_matrix]
  exact componentMass_path_le_base hp c hc

lemma source_cycle_le_runs {m r p : ℕ} (hp : Parameters m r p 4)
    (c : Component m r p) (hc : (freeComponentOrder m r p c).cycle=true) :
    componentMass c ≤ (((closedRuns c).map (fun g : List EdgeKind => (g.map EdgeKind.matrix).prod)).prod).trace := by
  rw [← closedRuns_matrix]
  exact componentMass_cycle_le_base hp c hc

end SubmittedGenus.CapFourMass.ActualComponent
