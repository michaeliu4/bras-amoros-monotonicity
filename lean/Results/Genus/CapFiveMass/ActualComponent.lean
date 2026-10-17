import Results.Genus.CapFiveMass.LocalSource

/-!
# Contractive bounds for the actual free raw components

The components and their vertex bijections are the proved components of the
original reflection graph, not a user-supplied graph decomposition.
-/

noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFiveMass
namespace ActualComponent
open RawGraph RawGraph.SourceModel RawGraph.Topology RawGraph.Transfer LocalSource MatrixSource

abbrev Component (m r p : ℕ) := (freeGraph m r p).ConnectedComponent
abbrev edgeCount {m r p : ℕ} (c : Component m r p) := (freeComponentOrder m r p c).edges

def vertex {m r p : ℕ} (c : Component m r p) (j : Fin (edgeCount c + 1)) : Fin (m - 1) :=
  ((freeComponentOrder m r p c).label j).val.val

lemma vertex_free {m r p : ℕ} (c : Component m r p) (j : Fin (edgeCount c + 1)) :
    IsFree r p (vertex c j) := ((freeComponentOrder m r p c).label j).val.property

lemma consecutive_adj {m r p : ℕ} (c : Component m r p) (j : Fin (edgeCount c)) :
    (rawGraph m r p).Adj (vertex c j.castSucc) (vertex c j.succ) := by
  exact ((freeComponentOrder m r p c).adjacent_iff j.castSucc j.succ).mpr (Or.inl rfl)

lemma closing_adj {m r p : ℕ} (c : Component m r p)
    (hc : (freeComponentOrder m r p c).cycle = true) :
    (rawGraph m r p).Adj (vertex c (Fin.last (edgeCount c))) (vertex c 0) := by
  exact ((freeComponentOrder m r p c).adjacent_iff (Fin.last _) 0).mpr
    (Or.inr (Or.inr ⟨hc, Or.inr ⟨rfl, rfl⟩⟩))

def halfWeights {m r p : ℕ} (c : Component m r p) (k : ℕ) (v : BoundedState) : ℝ :=
  if hk : k < edgeCount c + 1 then domainHalf r p (vertex c ⟨k, hk⟩) radius v else 0

def edgeFactors {m r p : ℕ} (c : Component m r p) (k : ℕ) (v w : BoundedState) : ℝ :=
  if hk : k < edgeCount c then edgeFactor r p
    (vertex c (⟨k, hk⟩ : Fin (edgeCount c)).castSucc)
    (vertex c (⟨k, hk⟩ : Fin (edgeCount c)).succ) v w else 0

def edgeControls {m r p : ℕ} (c : Component m r p) (k : ℕ) : MatrixBounds.Controlled (ι := BoundedState) :=
  if hk : k < edgeCount c then sourceTransfer r p
    (vertex c (⟨k, hk⟩ : Fin (edgeCount c)).castSucc)
    (vertex c (⟨k, hk⟩ : Fin (edgeCount c)).succ) else strongTransferSix

def closeFactor {m r p : ℕ} (c : Component m r p) : BoundedState → BoundedState → ℝ :=
  edgeFactor r p (vertex c (Fin.last _)) (vertex c 0)

def closeControl {m r p : ℕ} (c : Component m r p) : MatrixBounds.Controlled (ι := BoundedState) :=
  sourceTransfer r p (vertex c (Fin.last _)) (vertex c 0)

@[simp] lemma halfWeights_fin {m r p : ℕ} (c : Component m r p)
    (j : Fin (edgeCount c + 1)) (v : BoundedState) :
    halfWeights c j.val v = domainHalf r p (vertex c j) radius v := by
  simp only [halfWeights, dif_pos j.isLt]

lemma halfWeights_nonneg {m r p : ℕ} (c : Component m r p) (k : ℕ) (v : BoundedState) :
    0 ≤ halfWeights c k v := by
  unfold halfWeights
  split_ifs
  · exact domainHalf_nonneg _ _ _
  · rfl

lemma edgeFactors_nonneg {m r p : ℕ} (c : Component m r p) (k : ℕ) (v w : BoundedState) :
    0 ≤ edgeFactors c k v w := by
  unfold edgeFactors edgeFactor
  split_ifs <;> norm_num

lemma split_nonneg {m r p : ℕ} (c : Component m r p) (k : ℕ) (v w : BoundedState) :
    0 ≤ splitMatrix (halfWeights c) (edgeFactors c) k v w :=
  _root_.mul_nonneg (_root_.mul_nonneg (halfWeights_nonneg c k v) (edgeFactors_nonneg c k v w))
    (halfWeights_nonneg c (k + 1) w)

lemma split_le_control {m r p : ℕ} (hp : Parameters m r p 5)
    (c : Component m r p) (k : ℕ) (v w : BoundedState) :
    splitMatrix (halfWeights c) (edgeFactors c) k v w ≤ (edgeControls c k).matrix v w := by
  by_cases hk : k < edgeCount c
  · have hk0 : k < edgeCount c + 1 := by omega
    have hk1 : k + 1 < edgeCount c + 1 := by omega
    simpa [splitMatrix, halfWeights, edgeFactors, edgeControls, hk, hk0, hk1]
      using split_edge_le_transfer hp (consecutive_adj c ⟨k, hk⟩) v w
  · simp only [splitMatrix, edgeFactors, dif_neg hk, mul_zero, zero_mul, edgeControls]
    exact thresholdSix_nonneg _ _ _ _

def loopKind {m r p : ℕ} (i : Fin (m - 1)) : EndpointKind :=
  if StrongLoop r p i then .strongLoop else if CarryLoop r p i then .carryLoop else .free

lemma half_le_loopKind {m r p : ℕ} (hp : Parameters m r p 5)
    {i : Fin (m - 1)} (hi : IsFree r p i) (v : BoundedState) :
    domainHalf r p i radius v ≤ endpointVectorSix (loopKind (r := r) (p := p) i) radius v := by
  unfold loopKind
  split_ifs with hs hc
  · exact domainHalf_le_strong hi hs _ _
  · exact domainHalf_le_carry hp hi hc _ _
  · exact domainHalf_le_free hi _ _

def leftKind {m r p : ℕ} (c : Component m r p) : EndpointKind := loopKind (r := r) (p := p) (vertex c 0)
def rightKind {m r p : ℕ} (c : Component m r p) : EndpointKind :=
  if edgeCount c = 0 then .free else loopKind (r := r) (p := p) (vertex c (Fin.last _))

lemma first_half_le {m r p : ℕ} (hp : Parameters m r p 5) (c : Component m r p) (v : BoundedState) :
    halfWeights c 0 v ≤ endpointVectorSix (leftKind c) radius v := by
  have h := half_le_loopKind hp (vertex_free c 0) v
  change halfWeights c (0 : Fin (edgeCount c + 1)).val v ≤ _
  rw [halfWeights_fin]
  exact h

lemma last_half_le {m r p : ℕ} (hp : Parameters m r p 5) (c : Component m r p) (v : BoundedState) :
    halfWeights c (edgeCount c) v ≤ endpointVectorSix (rightKind c) radius v := by
  rw [show edgeCount c = (Fin.last (edgeCount c)).val from rfl, halfWeights_fin]
  unfold rightKind
  split_ifs
  · exact domainHalf_le_free (vertex_free c (Fin.last _)) _ _
  · exact half_le_loopKind hp (vertex_free c (Fin.last _)) v

/-- Full source mass for an actual ordered component, with the original
unary domains and ordinary edge thresholds retained. -/
def componentMass {m r p : ℕ} (c : Component m r p) : ℝ :=
  if (freeComponentOrder m r p c).cycle = true then
    cycleSource (edgeCount c) (fun k v => halfWeights c k v ^ 2) (edgeFactors c) (closeFactor c)
  else pathSource (edgeCount c) (fun k v => halfWeights c k v ^ 2) (edgeFactors c)

def pathBound {m r p : ℕ} (c : Component m r p) : ℝ :=
  Real.sqrt (endpointBound (leftKind c)) * Real.sqrt (endpointBound (rightKind c)) *
    MatrixBounds.chainBound (controls (edgeCount c) (edgeControls c))

def cycleBound {m r p : ℕ} (c : Component m r p) : ℝ :=
  MatrixBounds.chainBound (controls (edgeCount c) (edgeControls c) ++ [closeControl c])

lemma path_source_le {m r p : ℕ} (hp : Parameters m r p 5) (c : Component m r p) :
    pathSource (edgeCount c) (fun k v => halfWeights c k v ^ 2) (edgeFactors c) ≤ pathBound c := by
  rw [pathSource_split_exact]
  have hmono := boundary_matrix_mono
    (matrixRun (edgeCount c) (splitMatrix (halfWeights c) (edgeFactors c)))
    (matrixRun (edgeCount c) (fun k => (edgeControls c k).matrix))
    (halfWeights c 0) (endpointVectorSix (leftKind c) radius)
    (halfWeights c (edgeCount c)) (endpointVectorSix (rightKind c) radius)
    (matrixRun_nonneg _ _ (split_nonneg c))
    (matrixRun_mono _ _ _ (split_nonneg c) (split_le_control hp c))
    (halfWeights_nonneg c 0) (halfWeights_nonneg c (edgeCount c))
    (first_half_le hp c) (last_half_le hp c)
  rw [matrixRun_controlled] at hmono
  refine hmono.trans ((MatrixBounds.path_le _ _ _).trans ?_)
  exact mul_le_mul_of_nonneg_right
    (_root_.mul_le_mul (Real.sqrt_le_sqrt (endpointSix_energy_le (leftKind c)))
      (Real.sqrt_le_sqrt (endpointSix_energy_le (rightKind c))) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    (MatrixBounds.chainBound_nonneg _)

lemma close_nonneg {m r p : ℕ} (c : Component m r p) (v w : BoundedState) :
    0 ≤ closeMatrix (edgeCount c) (halfWeights c) (closeFactor c) v w := by
  unfold closeMatrix closeFactor edgeFactor
  split_ifs
  · exact _root_.mul_nonneg (_root_.mul_nonneg (halfWeights_nonneg c _ v) (by norm_num))
      (halfWeights_nonneg c 0 w)
  · simp

lemma close_le_control {m r p : ℕ} (hp : Parameters m r p 5) (c : Component m r p)
    (hc : (freeComponentOrder m r p c).cycle = true) (v w : BoundedState) :
    closeMatrix (edgeCount c) (halfWeights c) (closeFactor c) v w ≤ (closeControl c).matrix v w := by
  have h := split_edge_le_transfer hp (closing_adj c hc) v w
  change halfWeights c (Fin.last (edgeCount c)).val v * closeFactor c v w *
    halfWeights c (0 : Fin (edgeCount c + 1)).val w ≤ _
  rw [halfWeights_fin, halfWeights_fin]
  exact h

lemma cycle_source_le {m r p : ℕ} (hp : Parameters m r p 5) (c : Component m r p)
    (hc : (freeComponentOrder m r p c).cycle = true) :
    cycleSource (edgeCount c) (fun k v => halfWeights c k v ^ 2) (edgeFactors c) (closeFactor c) ≤
      cycleBound c := by
  rw [cycleSource_split_exact]
  have hm := matrixRun_mono (edgeCount c) _ _ (split_nonneg c) (split_le_control hp c)
  have hmn := matrixRun_nonneg (edgeCount c) _ (split_nonneg c)
  have htrace : (matrixRun (edgeCount c) (splitMatrix (halfWeights c) (edgeFactors c)) *
      closeMatrix (edgeCount c) (halfWeights c) (closeFactor c)).trace ≤
      (matrixRun (edgeCount c) (fun k => (edgeControls c k).matrix) * (closeControl c).matrix).trace := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    apply Finset.sum_le_sum
    intro v _
    apply Finset.sum_le_sum
    intro w _
    exact _root_.mul_le_mul (hm v w) (close_le_control hp c hc w v)
      (close_nonneg c w v) ((hmn v w).trans (hm v w))
  refine htrace.trans ?_
  rw [matrixRun_controlled]
  have he : MatrixBounds.chain (controls (edgeCount c) (edgeControls c) ++ [closeControl c]) =
      MatrixBounds.chain (controls (edgeCount c) (edgeControls c)) * (closeControl c).matrix := by
    simp [MatrixBounds.chain, List.map_append, List.prod_append]
  rw [← he]
  apply MatrixBounds.cycle_le
  simp only [List.length_append, controls_length, List.length_singleton]
  exact free_cycle_min m r p c hc

def componentBound {m r p : ℕ} (c : Component m r p) : ℝ :=
  if (freeComponentOrder m r p c).cycle = true then cycleBound c else pathBound c

/-- Every actual component obeys its endpoint/edge product bound. This is
source-specific and uses the proved actual reflection decomposition. -/
lemma componentMass_le {m r p : ℕ} (hp : Parameters m r p 5) (c : Component m r p) :
    componentMass c ≤ componentBound c := by
  unfold componentMass componentBound
  split_ifs with hc
  · exact cycle_source_le hp c hc
  · exact path_source_le hp c

lemma componentBound_nonneg {m r p : ℕ} (c : Component m r p) : 0 ≤ componentBound c := by
  unfold componentBound
  split_ifs
  · exact MatrixBounds.chainBound_nonneg _
  · exact _root_.mul_nonneg (_root_.mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (MatrixBounds.chainBound_nonneg _)

lemma term_nonneg {A : Type*} [Fintype A] (n : ℕ) (w : ℕ → A → ℝ)
    (e : ℕ → A → A → ℝ) (f : A → ℝ)
    (hw : ∀ i a, 0 ≤ w i a) (he : ∀ i a b, 0 ≤ e i a b) (hf : ∀ a, 0 ≤ f a)
    (x : Fin (n + 1) → A) : 0 ≤ sourceTerm n w e f x :=
  _root_.mul_nonneg (_root_.mul_nonneg (Finset.prod_nonneg fun i _ => hw _ _)
    (Finset.prod_nonneg fun i _ => he _ _ _)) (hf _)

lemma componentMass_nonneg {m r p : ℕ} (c : Component m r p) : 0 ≤ componentMass c := by
  have hw : ∀ i v, 0 ≤ halfWeights c i v ^ 2 := fun _ _ => sq_nonneg _
  have he := edgeFactors_nonneg c
  have hf : ∀ v w, 0 ≤ closeFactor c v w := by
    intro v w
    unfold closeFactor edgeFactor
    split_ifs <;> norm_num
  unfold componentMass
  split_ifs
  · exact Finset.sum_nonneg fun x _ => term_nonneg _ _ _ _ hw he (fun v => hf v (x 0)) x
  · exact Finset.sum_nonneg fun x _ => term_nonneg _ _ _ _ hw he (fun _ => by norm_num) x

end ActualComponent
end SubmittedGenus.CapFiveMass
