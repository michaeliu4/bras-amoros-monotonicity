import Results.Genus.CapFourMass.ComponentMatrices
import Results.Genus.GoldenSpectral.Matrices

/-! Original raw cap-four source evaluated at the golden-ratio point. All
physical vertex weights and original unary/binary gates are retained exactly. -/
namespace SubmittedGenus.GoldenGraph.Source
open RawGraph RawGraph.SourceModel RawGraph.Topology RawGraph.Transfer
open CapFourMass.ActualComponent GoldenSpectral CapFiveMass.MatrixSource
open scoped BigOperators Matrix
noncomputable section

def componentMass {m r p : ℕ} (c : Component m r p) : ℝ :=
  ∑ x : Fin (edgeCount c+1)→State,
    if Allowed c x then radius^(∑ j,((x j).val+1)) else 0

lemma componentMass_nonneg {m r p : ℕ} (c : Component m r p) : 0≤componentMass c := by
  apply Finset.sum_nonneg
  intro x _
  split_ifs
  · exact pow_nonneg radius_pos.le _
  · rfl

lemma componentMass_eq_eval {m r p : ℕ} (c : Component m r p) :
    componentMass c=Polynomial.eval₂ (Nat.castRingHom ℝ) radius (componentPolynomial c) := by
  unfold componentMass componentPolynomial
  rw [Polynomial.eval₂_finsetSum]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp

theorem raw_eval_eq_component_product {m r p : ℕ} (hp : Parameters m r p 4) :
    Polynomial.eval₂ (Nat.castRingHom ℝ) radius (rawPolynomial m r p 4)=
      radius^8*∏ c : Component m r p,componentMass c := by
  rw [rawPolynomial_eq_component_product hp]
  change (Polynomial.eval₂RingHom (Nat.castRingHom ℝ) radius) _=_
  rw [map_mul,map_prod]
  simp only [Polynomial.coe_eval₂RingHom,Polynomial.eval₂_pow,Polynomial.eval₂_X]
  simp_rw [componentMass_eq_eval]

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

end
end SubmittedGenus.GoldenGraph.Source
