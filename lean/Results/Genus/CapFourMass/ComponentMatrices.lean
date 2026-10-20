import Results.Genus.CapFourMass.ComponentSource
import Results.Genus.CapFiveMass.MatrixSource

/-! Exact source-to-matrix normalization for every actual cap-four component. -/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFourMass.ActualComponent
open RawGraph RawGraph.SourceModel RawGraph.Topology RawGraph.Transfer
open CapFiveMass.MatrixSource

def domainHalf {m r p : ℕ} (c : Component m r p) (j : Fin (edgeCount c+1)) (v : State) : ℝ :=
  if Domain r p 4 (vertex c j) (v.val+1) then halfWeight v else 0

lemma domainHalf_nonneg {m r p : ℕ} (c : Component m r p) (j : Fin (edgeCount c+1)) (v : State) :
    0≤domainHalf c j v := by
  unfold domainHalf
  split_ifs
  · exact (halfWeight_pos v).le
  · rfl

lemma domainHalf_sq {m r p : ℕ} (c : Component m r p) (j : Fin (edgeCount c+1)) (v : State) :
    (domainHalf c j v)^2 = if Domain r p 4 (vertex c j) (v.val+1) then radius^(v.val+1) else 0 := by
  unfold domainHalf
  split_ifs
  · exact halfWeight_sq v
  · norm_num

def halfWeights {m r p : ℕ} (c : Component m r p) (j : ℕ) (v : State) : ℝ :=
  if hj : j<edgeCount c+1 then domainHalf c ⟨j,hj⟩ v else 0

def edgeFactor {m r p : ℕ} (i j : Fin (m-1)) (v w : State) : ℝ :=
  if edgeBound r p 4 i j ≤ (v.val+1)+(w.val+1) then 1 else 0

def edgeFactors {m r p : ℕ} (c : Component m r p) (j : ℕ) (v w : State) : ℝ :=
  if hj : j<edgeCount c then edgeFactor (r:=r) (p:=p)
    (vertex c (Fin.castSucc ⟨j,hj⟩)) (vertex c (Fin.succ ⟨j,hj⟩)) v w else 0

def closeFactor {m r p : ℕ} (c : Component m r p) (v w : State) : ℝ :=
  edgeFactor (r:=r) (p:=p) (vertex c (Fin.last _)) (vertex c 0) v w

@[simp] lemma halfWeights_fin {m r p : ℕ} (c : Component m r p) (j : Fin (edgeCount c+1)) (v : State) :
    halfWeights c j.val v = domainHalf c j v := by simp only [halfWeights,dif_pos j.isLt]
@[simp] lemma edgeFactors_fin {m r p : ℕ} (c : Component m r p) (j : Fin (edgeCount c)) (v w : State) :
    edgeFactors c j.val v w = edgeFactor (r:=r) (p:=p) (vertex c j.castSucc) (vertex c j.succ) v w := by
  simp only [edgeFactors,dif_pos j.isLt]

def sourceTermGate {m r p : ℕ} (c : Component m r p) (x : Fin (edgeCount c+1)→State) : ℝ :=
  (∏ j,if Domain r p 4 (vertex c j) ((x j).val+1) then radius^((x j).val+1) else 0)*
    (∏ j : Fin (edgeCount c),edgeFactor (r:=r) (p:=p) (vertex c j.castSucc) (vertex c j.succ)
      (x j.castSucc) (x j.succ))*
    (if (freeComponentOrder m r p c).cycle=true then closeFactor c (x (Fin.last _)) (x 0) else 1)

lemma sourceTermGate_eq {m r p : ℕ} (c : Component m r p) (x : Fin (edgeCount c+1)→State) :
    sourceTermGate c x = if Allowed c x then radius^(∑ j,((x j).val+1)) else 0 := by
  unfold sourceTermGate closeFactor edgeFactor
  rw [Factorization.prod_gate,Factorization.prod_gate,Finset.prod_pow_eq_pow_sum]
  simp only [Finset.prod_const_one]
  unfold Allowed AllowedValues
  split_ifs <;> simp_all

/-- Exact source equality before any spectral estimate or alphabet relaxation. -/
theorem componentMass_eq_transfer {m r p : ℕ} (c : Component m r p) :
    componentMass c = if (freeComponentOrder m r p c).cycle=true then
      cycleSource (edgeCount c) (fun j v => (halfWeights c j v)^2) (edgeFactors c) (closeFactor c)
    else pathSource (edgeCount c) (fun j v => (halfWeights c j v)^2) (edgeFactors c) := by
  unfold componentMass
  simp_rw [← sourceTermGate_eq]
  split_ifs with hc
  · unfold cycleSource
    apply Finset.sum_congr rfl
    intro x _
    simp only [sourceTerm,sourceTermGate,halfWeights_fin,domainHalf_sq,edgeFactors_fin,hc,if_true]
  · unfold pathSource
    apply Finset.sum_congr rfl
    intro x _
    simp only [sourceTerm,sourceTermGate,halfWeights_fin,domainHalf_sq,edgeFactors_fin,hc,Bool.false_eq_true,if_false]

/-- Every physical coordinate has one full weight after the half-weight
matrix split, including an isolated loop-bearing vertex. -/
theorem componentMass_eq_matrix {m r p : ℕ} (c : Component m r p) :
    componentMass c = if (freeComponentOrder m r p c).cycle=true then
      (matrixRun (edgeCount c) (splitMatrix (halfWeights c) (edgeFactors c))*
        closeMatrix (edgeCount c) (halfWeights c) (closeFactor c)).trace
    else halfWeights c 0 ⬝ᵥ (matrixRun (edgeCount c) (splitMatrix (halfWeights c) (edgeFactors c))*ᵥ
      halfWeights c (edgeCount c)) := by
  rw [componentMass_eq_transfer]
  split_ifs <;> first | exact cycleSource_split_exact _ _ _ _ | exact pathSource_split_exact _ _ _

lemma domain_iff_endpoint {m r p : ℕ} (c : Component m r p) (j : Fin (edgeCount c+1)) (v : State) :
    Domain r p 4 (vertex c j) (v.val+1) ↔
      v.val+1≤upper r 4 (vertex c j) ∧
        ((StrongLoop r p (vertex c j) ∨ CarryLoop r p (vertex c j)) → 2≤v.val+1) := by
  rw [domain_iff_unary]
  have hf := vertex_free c j
  simp only [Unary,show ¬IsPivot r p (vertex c j) from hf,false_implies,true_and,hf,forall_const]
  constructor
  · rintro ⟨_, hu, hs, hc⟩
    exact ⟨hu,by rintro (h | h) <;> [have := hs h; have := hc h] <;> omega⟩
  · rintro ⟨hu,hl⟩
    refine ⟨by omega,hu,?_,?_⟩
    · intro hs; have := hl (Or.inl hs); omega
    · intro hc; have := hl (Or.inr hc); omega

/-- The physical unary source is exactly the compiled cap/loop endpoint mask. -/
lemma domainHalf_eq_endpoint {m r p : ℕ} (c : Component m r p) (j : Fin (edgeCount c+1)) :
    domainHalf c j = endpoint (upper r 4 (vertex c j))
      (decide (StrongLoop r p (vertex c j) ∨ CarryLoop r p (vertex c j))) := by
  funext v
  unfold domainHalf endpoint
  simp only [domain_iff_endpoint,decide_eq_true_eq]

lemma domainHalf_energy_le {m r p : ℕ} (c : Component m r p) (j : Fin (edgeCount c+1)) :
    CapFiveMass.MatrixBounds.vectorEnergy (domainHalf c j) ≤ alphabetMass := by
  rw [domainHalf_eq_endpoint]
  exact endpoint_energy_free _ _

lemma domainHalf_loop_energy_le {m r p : ℕ} (c : Component m r p) (j : Fin (edgeCount c+1))
    (hl : StrongLoop r p (vertex c j) ∨ CarryLoop r p (vertex c j)) :
    CapFiveMass.MatrixBounds.vectorEnergy (domainHalf c j) ≤ loopMass := by
  rw [domainHalf_eq_endpoint,show decide (StrongLoop r p (vertex c j) ∨ CarryLoop r p (vertex c j))=true by simp [hl]]
  exact endpoint_energy_loop _

lemma strong_edgeBound {m r p : ℕ} {i j : Fin (m-1)} (hs : StrongRuns.StrongStep r p i j) :
    edgeBound r p 4 i j=4 := by
  unfold edgeBound
  rw [if_neg (by exact fun h => h.elim hs.1.2.1 (fun h => h.elim hs.1.2.2.1 hs.1.1)),if_pos hs.2]

lemma carry_edgeBound {m r p : ℕ} (hp : Parameters m r p 4) {i j : Fin (m-1)}
    (hc : StrongRuns.CarryStep r p i j) : edgeBound r p 4 i j=3 := by
  have hnot : ¬(physical i+physical j=r ∨ physical i+physical j=p) := by
    have h1 := hp.1; have h2 := hp.2.1; have h3 := hp.2.2.1; have hh := hc.2
    omega
  unfold edgeBound
  rw [if_neg (by exact fun h => h.elim hc.1.2.1 (fun h => h.elim hc.1.2.2.1 hc.1.1)),if_neg hnot,if_pos hc.2]

end SubmittedGenus.CapFourMass.ActualComponent
