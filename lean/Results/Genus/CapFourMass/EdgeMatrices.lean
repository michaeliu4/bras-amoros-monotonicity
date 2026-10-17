import Results.Genus.CapFourMass.ComponentMatrices

/-! Original ordinary edges are exactly strong, restricted-strong, or carry
matrices after their actual unary masks are accounted for. -/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFourMass.ActualComponent
open RawGraph RawGraph.SourceModel RawGraph.Topology RawGraph.Transfer
open CapFiveMass.MatrixSource

/-- The E replacement is applied precisely to a strong edge whose two
physical endpoints lie to the right of r. -/
def baseMatrix {m : ℕ} (r p : ℕ) (i j : Fin (m-1)) : Matrix State State ℝ :=
  if physical i+physical j=r ∨ physical i+physical j=p then
    if r<physical i ∧ r<physical j then restrictedMatrix else strongMatrix
  else carryMatrix

lemma baseMatrix_nonneg {m r p : ℕ} (i j : Fin (m-1)) (v w : State) :
    0≤baseMatrix r p i j v w := by
  unfold baseMatrix
  split_ifs <;> apply transfer_nonneg

def splitAt {m r p : ℕ} (c : Component m r p) (i j : Fin (edgeCount c+1)) : Matrix State State ℝ :=
  fun v w => domainHalf c i v * edgeFactor (r:=r) (p:=p) (vertex c i) (vertex c j) v w * domainHalf c j w

lemma domain_value_le_three {m r p : ℕ} (c : Component m r p) (i : Fin (edgeCount c+1))
    (hi : r<physical (vertex c i)) (v : State) (hv : Domain r p 4 (vertex c i) (v.val+1)) :
    v.val+1≤3 := by
  have hu := (domain_iff_endpoint c i v).mp hv
  have hh : upper r 4 (vertex c i)=3 := by unfold upper; rw [if_neg (by omega)]
  simpa only [hh] using hu.1

/-- Exact local identity: the only difference from the original D/E/C matrix
is the actual unary mask at each of its two endpoints. -/
lemma splitAt_eq_masked_base {m r p : ℕ} (hp : Parameters m r p 4)
    (c : Component m r p) (i j : Fin (edgeCount c+1))
    (he : (rawGraph m r p).Adj (vertex c i) (vertex c j)) (v w : State) :
    splitAt c i j v w =
      if Domain r p 4 (vertex c i) (v.val+1) ∧ Domain r p 4 (vertex c j) (w.val+1)
      then baseMatrix r p (vertex c i) (vertex c j) v w else 0 := by
  by_cases hv : Domain r p 4 (vertex c i) (v.val+1)
  swap
  · simp [splitAt,domainHalf,hv]
  by_cases hw : Domain r p 4 (vertex c j) (w.val+1)
  swap
  · simp [splitAt,domainHalf,hw]
  simp only [splitAt,domainHalf,hv,hw,if_true,true_and]
  have vv:=v.isLt
  have ww:=w.isLt
  rcases StrongRuns.edge_strong_or_carry he with hs | hc
  · rw [edgeFactor,strong_edgeBound hs]
    unfold baseMatrix
    rw [if_pos hs.2]
    by_cases hh : r<physical (vertex c i) ∧ r<physical (vertex c j)
    · have hv3:=domain_value_le_three c i hh.1 v hv
      have hw3:=domain_value_le_three c j hh.2 w hw
      rw [if_pos hh]
      simp only [restrictedMatrix,transfer,gate]
      split_ifs <;> simp_all
    · rw [if_neg hh]
      simp only [strongMatrix,transfer,gate]
      split_ifs <;> simp_all
  · rw [edgeFactor,carry_edgeBound hp hc]
    have hv3:=StrongRuns.carry_domain_upper hp hc hv
    have hw3:=StrongRuns.carry_domain_upper hp (StrongRuns.carryStep_symm hc) hw
    have hnot : ¬(physical (vertex c i)+physical (vertex c j)=r ∨
        physical (vertex c i)+physical (vertex c j)=p) := by
      intro hh
      exact StrongRuns.strong_carry_disjoint hp _ _ ⟨⟨he,hh⟩,hc⟩
    rw [baseMatrix,if_neg hnot]
    simp only [carryMatrix,transfer,gate]
    split_ifs <;> simp_all

lemma splitAt_le_base {m r p : ℕ} (hp : Parameters m r p 4)
    (c : Component m r p) (i j : Fin (edgeCount c+1))
    (he : (rawGraph m r p).Adj (vertex c i) (vertex c j)) (v w : State) :
    splitAt c i j v w ≤ baseMatrix r p (vertex c i) (vertex c j) v w := by
  rw [splitAt_eq_masked_base hp c i j he]
  split_ifs
  · rfl
  · exact baseMatrix_nonneg _ _ _ _

lemma splitAt_nonneg {m r p : ℕ} (c : Component m r p) (i j : Fin (edgeCount c+1)) (v w : State) :
    0≤splitAt c i j v w := by
  unfold splitAt edgeFactor
  split_ifs
  · simpa using mul_nonneg (domainHalf_nonneg c i v) (domainHalf_nonneg c j w)
  · simp

lemma consecutive_adj {m r p : ℕ} (c : Component m r p) (j : Fin (edgeCount c)) :
    (rawGraph m r p).Adj (vertex c j.castSucc) (vertex c j.succ) :=
  ((freeComponentOrder m r p c).adjacent_iff _ _).2 (Or.inl rfl)

lemma closing_adj {m r p : ℕ} (c : Component m r p)
    (hc : (freeComponentOrder m r p c).cycle=true) :
    (rawGraph m r p).Adj (vertex c (Fin.last _)) (vertex c 0) :=
  ((freeComponentOrder m r p c).adjacent_iff _ _).2 (Or.inr (Or.inr ⟨hc,Or.inr ⟨rfl,rfl⟩⟩))

def baseEdges {m r p : ℕ} (c : Component m r p) (j : ℕ) : Matrix State State ℝ :=
  if hj : j<edgeCount c then baseMatrix r p (vertex c (Fin.castSucc ⟨j,hj⟩))
    (vertex c (Fin.succ ⟨j,hj⟩)) else 0

def baseClose {m r p : ℕ} (c : Component m r p) : Matrix State State ℝ :=
  baseMatrix r p (vertex c (Fin.last _)) (vertex c 0)

lemma splitMatrix_le_baseEdges {m r p : ℕ} (hp : Parameters m r p 4) (c : Component m r p)
    (j : ℕ) (v w : State) :
    splitMatrix (halfWeights c) (edgeFactors c) j v w ≤ baseEdges c j v w := by
  by_cases hj : j<edgeCount c
  · have hj1 : j<edgeCount c+1 := by omega
    have hj2 : j+1<edgeCount c+1 := by omega
    simp only [splitMatrix,halfWeights,edgeFactors,baseEdges,dif_pos hj,dif_pos hj1,dif_pos hj2]
    convert splitAt_le_base hp c (Fin.castSucc ⟨j,hj⟩) (Fin.succ ⟨j,hj⟩) (consecutive_adj c ⟨j,hj⟩) v w using 1
    unfold splitAt
    congr 1
  · simp [splitMatrix,edgeFactors,baseEdges,hj]

lemma splitMatrix_nonneg {m r p : ℕ} (c : Component m r p) (j : ℕ) (v w : State) :
    0≤splitMatrix (halfWeights c) (edgeFactors c) j v w := by
  have hw (k : ℕ) (u : State) : 0≤halfWeights c k u := by
    unfold halfWeights
    split_ifs
    · exact domainHalf_nonneg _ _ _
    · rfl
  have he : 0≤edgeFactors c j v w := by
    unfold edgeFactors edgeFactor
    split_ifs <;> norm_num
  exact _root_.mul_nonneg (_root_.mul_nonneg (hw j v) he) (hw (j+1) w)

lemma closeMatrix_le_baseClose {m r p : ℕ} (hp : Parameters m r p 4) (c : Component m r p)
    (hc : (freeComponentOrder m r p c).cycle=true) (v w : State) :
    closeMatrix (edgeCount c) (halfWeights c) (closeFactor c) v w ≤ baseClose c v w := by
  simp only [closeMatrix,halfWeights,show edgeCount c<edgeCount c+1 from Nat.lt_succ_self _,
    show 0<edgeCount c+1 from Nat.succ_pos _,dif_pos,closeFactor,baseClose]
  convert splitAt_le_base hp c (Fin.last _) 0 (closing_adj c hc) v w using 1
  unfold splitAt
  congr 1

/-- A path is bounded by its actual endpoint vectors and the unmasked D/E/C
word. Removed internal alphabet masks are nonnegative contractions. -/
theorem componentMass_path_le_base {m r p : ℕ} (hp : Parameters m r p 4)
    (c : Component m r p) (hc : (freeComponentOrder m r p c).cycle=false) :
    componentMass c ≤ halfWeights c 0 ⬝ᵥ
      (matrixRun (edgeCount c) (baseEdges c) *ᵥ halfWeights c (edgeCount c)) := by
  rw [componentMass_eq_matrix,if_neg (by simp [hc])]
  have hw (j : ℕ) (v : State) : 0≤halfWeights c j v := by
    unfold halfWeights; split_ifs
    · exact domainHalf_nonneg _ _ _
    · rfl
  exact boundary_matrix_mono _ _ _ _ _ _
    (matrixRun_nonneg _ _ (splitMatrix_nonneg c))
    (matrixRun_mono _ _ _ (splitMatrix_nonneg c) (splitMatrix_le_baseEdges hp c))
    (hw 0) (hw _) (fun _ => le_rfl) (fun _ => le_rfl)

lemma baseEdges_nonneg {m r p : ℕ} (c : Component m r p) (j : ℕ) (v w : State) :
    0≤baseEdges c j v w := by
  unfold baseEdges
  split_ifs
  · exact baseMatrix_nonneg _ _ _ _
  · rfl

lemma closeMatrix_nonneg {m r p : ℕ} (c : Component m r p) (v w : State) :
    0≤closeMatrix (edgeCount c) (halfWeights c) (closeFactor c) v w := by
  have hw (j : ℕ) (v : State) : 0≤halfWeights c j v := by
    unfold halfWeights; split_ifs
    · exact domainHalf_nonneg _ _ _
    · rfl
  have he : 0≤closeFactor c v w := by unfold closeFactor edgeFactor; split_ifs <;> norm_num
  exact _root_.mul_nonneg (_root_.mul_nonneg (hw _ v) he) (hw _ w)

/-- The analogous dimension-free source comparison for an actual cycle. -/
theorem componentMass_cycle_le_base {m r p : ℕ} (hp : Parameters m r p 4)
    (c : Component m r p) (hc : (freeComponentOrder m r p c).cycle=true) :
    componentMass c ≤ (matrixRun (edgeCount c) (baseEdges c) * baseClose c).trace := by
  rw [componentMass_eq_matrix,if_pos hc]
  simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply]
  apply Finset.sum_le_sum
  intro v _
  apply Finset.sum_le_sum
  intro w _
  exact _root_.mul_le_mul
    (matrixRun_mono _ _ _ (splitMatrix_nonneg c) (splitMatrix_le_baseEdges hp c) v w)
    (closeMatrix_le_baseClose hp c hc w v) (closeMatrix_nonneg c w v)
    (matrixRun_nonneg _ _ (baseEdges_nonneg c) v w)

end SubmittedGenus.CapFourMass.ActualComponent
