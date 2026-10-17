import Results.Genus.CapFiveMass.General.LocalSource

noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFiveMass.General
open RawGraph RawGraph.SourceModel RawGraph.Topology RawGraph.Transfer LocalSource MatrixSource ActualComponent

def halfWeights (H : Control) {m r p : ℕ} (c : Component m r p) (k : ℕ) (v : BoundedState) : ℝ :=
  if hk : k < edgeCount c + 1 then domainHalf r p (vertex c ⟨k, hk⟩) H.z v else 0

def edgeControls (H : Control) {m r p : ℕ} (c : Component m r p) (k : ℕ) : MatrixBounds.Controlled (ι := BoundedState) :=
  if hk : k < edgeCount c then sourceTransfer H r p
    (vertex c (⟨k, hk⟩ : Fin (edgeCount c)).castSucc)
    (vertex c (⟨k, hk⟩ : Fin (edgeCount c)).succ) else strongTransferSix H

def closeControl (H : Control) {m r p : ℕ} (c : Component m r p) : MatrixBounds.Controlled (ι := BoundedState) :=
  sourceTransfer H r p (vertex c (Fin.last _)) (vertex c 0)

@[simp] lemma halfWeights_fin (H : Control) {m r p : ℕ} (c : Component m r p)
    (j : Fin (edgeCount c + 1)) (v : BoundedState) :
    halfWeights H c j.val v = domainHalf r p (vertex c j) H.z v := by
  simp only [halfWeights, dif_pos j.isLt]

lemma halfWeights_nonneg (H : Control) {m r p : ℕ} (c : Component m r p) (k : ℕ) (v : BoundedState) :
    0 ≤ halfWeights H c k v := by
  unfold halfWeights
  split_ifs
  · exact domainHalf_nonneg _ _ _
  · rfl

lemma split_nonneg (H : Control) {m r p : ℕ} (c : Component m r p) (k : ℕ) (v w : BoundedState) :
    0 ≤ splitMatrix (halfWeights H c) (edgeFactors c) k v w :=
  _root_.mul_nonneg (_root_.mul_nonneg (halfWeights_nonneg H c k v) (edgeFactors_nonneg c k v w))
    (halfWeights_nonneg H c (k + 1) w)

lemma split_le_control (H : Control) {m r p : ℕ} (hp : Parameters m r p 5)
    (c : Component m r p) (k : ℕ) (v w : BoundedState) :
    splitMatrix (halfWeights H c) (edgeFactors c) k v w ≤ (edgeControls H c k).matrix v w := by
  by_cases hk : k < edgeCount c
  · have hk0 : k < edgeCount c + 1 := by omega
    have hk1 : k + 1 < edgeCount c + 1 := by omega
    simpa [splitMatrix, halfWeights, edgeFactors, edgeControls, hk, hk0, hk1]
      using split_edge_le_transfer H hp (consecutive_adj c ⟨k, hk⟩) v w
  · simp only [splitMatrix, edgeFactors, dif_neg hk, mul_zero, zero_mul, edgeControls]
    exact thresholdSix_nonneg _ _ _ _

lemma half_le_loopKind (H : Control) {m r p : ℕ} (hp : Parameters m r p 5)
    {i : Fin (m - 1)} (hi : IsFree r p i) (v : BoundedState) :
    domainHalf r p i H.z v ≤ endpointVectorSix (loopKind (r := r) (p := p) i) H.z v := by
  unfold loopKind
  split_ifs with hs hc
  · exact domainHalf_le_strong hi hs _ _
  · exact domainHalf_le_carry hp hi hc _ _
  · exact domainHalf_le_free hi _ _

lemma first_half_le (H : Control) {m r p : ℕ} (hp : Parameters m r p 5) (c : Component m r p) (v : BoundedState) :
    halfWeights H c 0 v ≤ endpointVectorSix (leftKind c) H.z v := by
  have h := half_le_loopKind H hp (vertex_free c 0) v
  change halfWeights H c (0 : Fin (edgeCount c + 1)).val v ≤ _
  rw [halfWeights_fin H]
  exact h

lemma last_half_le (H : Control) {m r p : ℕ} (hp : Parameters m r p 5) (c : Component m r p) (v : BoundedState) :
    halfWeights H c (edgeCount c) v ≤ endpointVectorSix (rightKind c) H.z v := by
  rw [show edgeCount c = (Fin.last (edgeCount c)).val from rfl, halfWeights_fin H]
  unfold rightKind
  split_ifs
  · exact domainHalf_le_free (vertex_free c (Fin.last _)) _ _
  · exact half_le_loopKind H hp (vertex_free c (Fin.last _)) v

/-- Full source mass for an actual ordered component, with the original
unary domains and ordinary edge thresholds retained. -/

def componentMass (H : Control) {m r p : ℕ} (c : Component m r p) : ℝ :=
  if (freeComponentOrder m r p c).cycle = true then
    cycleSource (edgeCount c) (fun k v => halfWeights H c k v ^ 2) (edgeFactors c) (closeFactor c)
  else pathSource (edgeCount c) (fun k v => halfWeights H c k v ^ 2) (edgeFactors c)

def pathBound (H : Control) {m r p : ℕ} (c : Component m r p) : ℝ :=
  Real.sqrt (endpointBound H (leftKind c)) * Real.sqrt (endpointBound H (rightKind c)) *
    MatrixBounds.chainBound (controls (edgeCount c) (edgeControls H c))

def cycleBound (H : Control) {m r p : ℕ} (c : Component m r p) : ℝ :=
  MatrixBounds.chainBound (controls (edgeCount c) (edgeControls H c) ++ [closeControl H c])

lemma path_source_le (H : Control) {m r p : ℕ} (hp : Parameters m r p 5) (c : Component m r p) :
    pathSource (edgeCount c) (fun k v => halfWeights H c k v ^ 2) (edgeFactors c) ≤ pathBound H c := by
  rw [pathSource_split_exact]
  have hmono := boundary_matrix_mono
    (matrixRun (edgeCount c) (splitMatrix (halfWeights H c) (edgeFactors c)))
    (matrixRun (edgeCount c) (fun k => (edgeControls H c k).matrix))
    (halfWeights H c 0) (endpointVectorSix (leftKind c) H.z)
    (halfWeights H c (edgeCount c)) (endpointVectorSix (rightKind c) H.z)
    (matrixRun_nonneg _ _ (split_nonneg H c))
    (matrixRun_mono _ _ _ (split_nonneg H c) (split_le_control H hp c))
    (halfWeights_nonneg H c 0) (halfWeights_nonneg H c (edgeCount c))
    (first_half_le H hp c) (last_half_le H hp c)
  rw [matrixRun_controlled] at hmono
  refine hmono.trans ((MatrixBounds.path_le _ _ _).trans ?_)
  exact mul_le_mul_of_nonneg_right
    (_root_.mul_le_mul (Real.sqrt_le_sqrt (endpointSix_energy_le H (leftKind c)))
      (Real.sqrt_le_sqrt (endpointSix_energy_le H (rightKind c))) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    (MatrixBounds.chainBound_nonneg _)

lemma close_nonneg (H : Control) {m r p : ℕ} (c : Component m r p) (v w : BoundedState) :
    0 ≤ closeMatrix (edgeCount c) (halfWeights H c) (closeFactor c) v w := by
  unfold closeMatrix closeFactor edgeFactor
  split_ifs
  · exact _root_.mul_nonneg (_root_.mul_nonneg (halfWeights_nonneg H c _ v) (by norm_num))
      (halfWeights_nonneg H c 0 w)
  · simp

lemma close_le_control (H : Control) {m r p : ℕ} (hp : Parameters m r p 5) (c : Component m r p)
    (hc : (freeComponentOrder m r p c).cycle = true) (v w : BoundedState) :
    closeMatrix (edgeCount c) (halfWeights H c) (closeFactor c) v w ≤ (closeControl H c).matrix v w := by
  have h := split_edge_le_transfer H hp (closing_adj c hc) v w
  change halfWeights H c (Fin.last (edgeCount c)).val v * closeFactor c v w *
    halfWeights H c (0 : Fin (edgeCount c + 1)).val w ≤ _
  rw [halfWeights_fin H, halfWeights_fin H]
  exact h

lemma cycle_source_le (H : Control) {m r p : ℕ} (hp : Parameters m r p 5) (c : Component m r p)
    (hc : (freeComponentOrder m r p c).cycle = true) :
    cycleSource (edgeCount c) (fun k v => halfWeights H c k v ^ 2) (edgeFactors c) (closeFactor c) ≤
      cycleBound H c := by
  rw [cycleSource_split_exact]
  have hm := matrixRun_mono (edgeCount c) _ _ (split_nonneg H c) (split_le_control H hp c)
  have hmn := matrixRun_nonneg (edgeCount c) _ (split_nonneg H c)
  have htrace : (matrixRun (edgeCount c) (splitMatrix (halfWeights H c) (edgeFactors c)) *
      closeMatrix (edgeCount c) (halfWeights H c) (closeFactor c)).trace ≤
      (matrixRun (edgeCount c) (fun k => (edgeControls H c k).matrix) * (closeControl H c).matrix).trace := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    apply Finset.sum_le_sum
    intro v _
    apply Finset.sum_le_sum
    intro w _
    exact _root_.mul_le_mul (hm v w) (close_le_control H hp c hc w v)
      (close_nonneg H c w v) ((hmn v w).trans (hm v w))
  refine htrace.trans ?_
  rw [matrixRun_controlled]
  have he : MatrixBounds.chain (controls (edgeCount c) (edgeControls H c) ++ [closeControl H c]) =
      MatrixBounds.chain (controls (edgeCount c) (edgeControls H c)) * (closeControl H c).matrix := by
    simp [MatrixBounds.chain, List.map_append, List.prod_append]
  rw [← he]
  apply MatrixBounds.cycle_le
  simp only [List.length_append, controls_length, List.length_singleton]
  exact free_cycle_min m r p c hc

def componentBound (H : Control) {m r p : ℕ} (c : Component m r p) : ℝ :=
  if (freeComponentOrder m r p c).cycle = true then cycleBound H c else pathBound H c

/-- Every actual component obeys its endpoint/edge product bound. This is
source-specific and uses the proved actual reflection decomposition. -/

lemma componentMass_le (H : Control) {m r p : ℕ} (hp : Parameters m r p 5) (c : Component m r p) :
    componentMass H c ≤ componentBound H c := by
  unfold componentMass componentBound
  split_ifs with hc
  · exact cycle_source_le H hp c hc
  · exact path_source_le H hp c

lemma componentBound_nonneg (H : Control) {m r p : ℕ} (c : Component m r p) : 0 ≤ componentBound H c := by
  unfold componentBound
  split_ifs
  · exact MatrixBounds.chainBound_nonneg _
  · exact _root_.mul_nonneg (_root_.mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (MatrixBounds.chainBound_nonneg _)

lemma componentMass_nonneg (H : Control) {m r p : ℕ} (c : Component m r p) : 0 ≤ componentMass H c := by
  have hw : ∀ i v, 0 ≤ halfWeights H c i v ^ 2 := fun _ _ => sq_nonneg _
  have he := edgeFactors_nonneg c
  have hf : ∀ v w, 0 ≤ closeFactor c v w := by
    intro v w
    unfold closeFactor edgeFactor
    split_ifs <;> norm_num
  unfold componentMass
  split_ifs
  · exact Finset.sum_nonneg fun x _ => term_nonneg _ _ _ _ hw he (fun v => hf v (x 0)) x
  · exact Finset.sum_nonneg fun x _ => term_nonneg _ _ _ _ hw he (fun _ => by norm_num) x

end SubmittedGenus.CapFiveMass.General
