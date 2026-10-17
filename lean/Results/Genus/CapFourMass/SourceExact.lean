import Results.Genus.CapFourMass.SourceMasks

/-! Exact unmasked D/E/C source words, including all boundary unary masks. -/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFourMass.ActualComponent
open RawGraph RawGraph.SourceModel RawGraph.Topology RawGraph.Transfer
open CapFiveMass.MatrixSource

instance {m r p : ℕ} (c : Component m r p) (x : Fin (edgeCount c+1)→State) :
    Decidable (BoundaryAllowed c x) := by unfold BoundaryAllowed; infer_instance
instance {m r p : ℕ} (c : Component m r p) (x : Fin (edgeCount c+1)→State) :
    Decidable (ConsecutiveBaseAllowed c x) := by unfold ConsecutiveBaseAllowed; infer_instance

def boundaryPathSource {A : Type*} [Fintype A] (n : ℕ) (w : ℕ→A→ℝ) (E : ℕ→A→A→ℝ)
    (start finish : A→Prop) [DecidablePred start] [DecidablePred finish] : ℝ :=
  ∑ x : Fin (n+1)→A,(if start (x 0) then 1 else 0)*
    sourceTerm n (fun j v => (w j v)^2) E (fun v => if finish v then 1 else 0) x

lemma boundaryPathSource_eq_matrix {A : Type*} [Fintype A] [DecidableEq A]
    (n : ℕ) (w : ℕ→A→ℝ) (E : ℕ→A→A→ℝ)
    (start finish : A→Prop) [DecidablePred start] [DecidablePred finish] :
    boundaryPathSource n w E start finish = (fun v => if start v then w 0 v else 0) ⬝ᵥ
      (matrixRun n (splitMatrix w E) *ᵥ (fun v => if finish v then w n v else 0)) := by
  unfold boundaryPathSource
  rw [sum_cons]
  simp only [Fin.cons_zero,← Finset.mul_sum]
  change (∑ first,(if start first then 1 else 0)*fixedSource n (fun j v => (w j v)^2) E
    (fun v => if finish v then 1 else 0) first)=_
  simp_rw [← run_eq_fixedSource,run_split_finish_exact]
  have hf : (fun v => w n v*(if finish v then 1 else 0))=(fun v => if finish v then w n v else 0) := by
    funext v; split_ifs <;> simp
  rw [hf]
  unfold dotProduct
  apply Finset.sum_congr rfl
  intro v _
  split_ifs <;> simp_all

def baseFactor {m r p : ℕ} (i j : Fin (m-1)) (v w : State) : ℝ :=
  if BaseAllowed r p i j v w then 1 else 0

def baseFactors {m r p : ℕ} (c : Component m r p) (j : ℕ) (v w : State) : ℝ :=
  if hj : j<edgeCount c then baseFactor (r:=r) (p:=p)
    (vertex c (Fin.castSucc ⟨j,hj⟩)) (vertex c (Fin.succ ⟨j,hj⟩)) v w else 0

def baseClosing {m r p : ℕ} (c : Component m r p) (v w : State) : ℝ :=
  baseFactor (r:=r) (p:=p) (vertex c (Fin.last _)) (vertex c 0) v w

@[simp] lemma baseFactors_fin {m r p : ℕ} (c : Component m r p) (j : Fin (edgeCount c)) (v w : State) :
    baseFactors c j.val v w=baseFactor (r:=r) (p:=p) (vertex c j.castSucc) (vertex c j.succ) v w := by
  simp only [baseFactors,dif_pos j.isLt]

lemma split_baseFactors {m r p : ℕ} (c : Component m r p) :
    splitMatrix (fun _ => halfWeight) (baseFactors c)=baseEdges c := by
  funext j v w
  unfold splitMatrix baseFactors baseEdges
  split_ifs
  · rw [baseMatrix_eq_gate]
    unfold baseFactor
    split_ifs <;> simp
  · simp

lemma close_baseClosing {m r p : ℕ} (c : Component m r p) :
    closeMatrix (edgeCount c) (fun _ => halfWeight) (baseClosing c)=baseClose c := by
  funext v w
  unfold closeMatrix baseClosing baseClose
  rw [baseMatrix_eq_gate]
  unfold baseFactor
  split_ifs <;> simp

lemma componentMass_path_eq_boundarySource {m r p : ℕ} (hp : Parameters m r p 4)
    (c : Component m r p) (hc : (freeComponentOrder m r p c).cycle=false) :
    componentMass c = boundaryPathSource (edgeCount c) (fun _ => halfWeight) (baseFactors c)
      (fun v => Domain r p 4 (vertex c 0) (v.val+1))
      (fun v => Domain r p 4 (vertex c (Fin.last _)) (v.val+1)) := by
  unfold componentMass boundaryPathSource
  apply Finset.sum_congr rfl
  intro x _
  simp only [allowed_iff_boundary_base hp c x]
  simp only [BoundaryAllowed,ConsecutiveBaseAllowed,hc,Bool.false_eq_true,false_implies,true_implies,and_true]
  unfold sourceTerm
  simp only [halfWeight_sq,baseFactors_fin]
  unfold baseFactor
  rw [Factorization.prod_gate,Finset.prod_pow_eq_pow_sum]
  simp only [Finset.prod_const_one]
  split_ifs <;> simp_all

lemma componentMass_cycle_eq_baseSource {m r p : ℕ} (hp : Parameters m r p 4)
    (c : Component m r p) (hc : (freeComponentOrder m r p c).cycle=true) :
    componentMass c = cycleSource (edgeCount c) (fun _ v => (halfWeight v)^2)
      (baseFactors c) (baseClosing c) := by
  unfold componentMass cycleSource
  apply Finset.sum_congr rfl
  intro x _
  simp only [allowed_iff_boundary_base hp c x]
  simp only [BoundaryAllowed,ConsecutiveBaseAllowed,hc,Bool.true_eq_false,false_implies,true_implies,true_and]
  unfold sourceTerm baseClosing
  simp only [halfWeight_sq,baseFactors_fin]
  unfold baseFactor
  rw [Factorization.prod_gate,Finset.prod_pow_eq_pow_sum]
  simp only [Finset.prod_const_one]
  split_ifs <;> simp_all

/-- Exact original open component, not merely a monotone relaxation. Its two
boundary vectors contain every endpoint alphabet and unary self-pair test. -/
theorem componentMass_path_eq_word {m r p : ℕ} (hp : Parameters m r p 4)
    (c : Component m r p) (hc : (freeComponentOrder m r p c).cycle=false) :
    componentMass c = domainHalf c 0 ⬝ᵥ
      ((((pathWord c).map EdgeKind.matrix).prod) *ᵥ domainHalf c (Fin.last _)) := by
  rw [componentMass_path_eq_boundarySource hp c hc,boundaryPathSource_eq_matrix,split_baseFactors,pathWord_matrix]
  rfl

/-- Exact cyclic D/E/C word. There are no omitted internal alphabet masks,
loops, or independent duplicated closing states. -/
theorem componentMass_cycle_eq_word {m r p : ℕ} (hp : Parameters m r p 4)
    (c : Component m r p) (hc : (freeComponentOrder m r p c).cycle=true) :
    componentMass c = (((closedWord c).map EdgeKind.matrix).prod).trace := by
  rw [componentMass_cycle_eq_baseSource hp c hc,cycleSource_split_exact,
    split_baseFactors,close_baseClosing,closedWord_matrix]

end SubmittedGenus.CapFourMass.ActualComponent
