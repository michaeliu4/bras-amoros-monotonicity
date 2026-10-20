import Results.Genus.CapFourMass.RetainedModeRun
import Results.Genus.CapFourMass.AsymmetricMatrixSource

/-! Direct finite tail-spin summation for signed normalized rank-one carry
edges. All tail alphabet and terminal loop gates are physical source gates. -/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFourMass.CarryLocalization
open RawGraph.Transfer CapFiveMass.MatrixSource
attribute [local instance] Classical.propDecidable Classical.decEq

/-- One normalized signed edge, with no weight charged to a fixed core port. -/
def normalizedModeEdge (j : Mode) (v w : State) : ℝ :=
  modeRoot j*modeVector j v*modeVector j w/(halfWeight v*halfWeight w)

def tailWeight (v : State) : ℝ := if v.val+1 ≤ 3 then radius^(v.val+1) else 0

def tailInitial (free : Prop) (j : Mode) (left v : State) : ℝ :=
  if free then 1 else normalizedModeEdge j left v

def tailFinish (loop : Prop) (j : Mode) (right v : State) : ℝ :=
  if loop then (if 2 ≤ v.val+1 then 1 else 0) else normalizedModeEdge j v right

def normalizedTailTerm (n : ℕ) (free loop : Prop) (j : Mode) (left right : State)
    (y : Fin (n+1)→State) : ℝ :=
  (∏ t : Fin (n+1),if (y t).val+1 ≤ 3 ∧ ((loop ∧ t.val+1=n+1) → 2 ≤ (y t).val+1)
    then radius^((y t).val+1) else 0)*
  (∏ k : Fin n,normalizedModeEdge j (y k.castSucc) (y k.succ))*
  tailInitial free j left (y 0)*
  (if loop then 1 else normalizedModeEdge j (y (Fin.last n)) right)

lemma tail_vertex_product (n : ℕ) (loop : Prop) (y : Fin (n+1)→State) :
    (∏ t : Fin (n+1),if (y t).val+1 ≤ 3 ∧ ((loop ∧ t.val+1=n+1) → 2 ≤ (y t).val+1)
      then radius^((y t).val+1) else 0)=
      (∏ t : Fin (n+1),tailWeight (y t))*(if loop then if 2 ≤ (y (Fin.last n)).val+1 then 1 else 0 else 1) := by
  rw [Fin.prod_univ_castSucc,Fin.prod_univ_castSucc]
  have hi (t : Fin n) :
      (if (y t.castSucc).val+1 ≤ 3 ∧ ((loop ∧ t.castSucc.val+1=n+1) → 2 ≤ (y t.castSucc).val+1)
        then radius^((y t.castSucc).val+1) else (0:ℝ))=tailWeight (y t.castSucc) := by
    have hn : t.castSucc.val+1≠n+1 := by
      change t.val+1≠n+1
      have:=t.isLt
      omega
    simp only [hn,and_false,false_implies,and_true,tailWeight]
  have hp := Finset.prod_congr (s₁ := (Finset.univ : Finset (Fin n))) rfl (fun t _ => hi t)
  change (∏ t : Fin n,_)=(∏ t : Fin n,_) at hp
  rw [hp]
  clear hi hp
  simp only [Fin.val_last,eq_self_iff_true,and_true,tailWeight]
  split_ifs <;> simp_all

lemma normalizedTailTerm_source (n : ℕ) (free loop : Prop) (j : Mode) (left right : State)
    (y : Fin (n+1)→State) :
    normalizedTailTerm n free loop j left right y=
      tailInitial free j left (y 0)*sourceTerm n (fun _ => tailWeight)
        (fun _ => normalizedModeEdge j) (tailFinish loop j right) y := by
  rw [normalizedTailTerm,tail_vertex_product]
  unfold sourceTerm tailFinish
  split_ifs <;> ring

lemma weighted_path_eq_matrix (n : ℕ) (w : State→ℝ) (E : ℕ→Matrix State State ℝ)
    (start finish : State→ℝ) :
    (∑ y : Fin (n+1)→State,start (y 0)*sourceTerm n (fun _ v => (w v)^2) E finish y)=
      (fun v => start v*w v) ⬝ᵥ
        (matrixRun n (splitMatrix (fun _ => w) E)*ᵥ (fun v => w v*finish v)) := by
  rw [sum_cons]
  simp only [Fin.cons_zero,←Finset.mul_sum]
  change (∑ first,start first*fixedSource n (fun _ v => (w v)^2) E finish first)=_
  simp_rw [←run_eq_fixedSource,run_split_finish_exact]
  simp only [dotProduct,mul_assoc]

lemma freeBoundary_eq_gate (v : State) :
    freeBoundary v=if v.val+1 ≤ 3 then halfWeight v else 0 := by
  fin_cases v <;> simp [freeBoundary,halfScale]
lemma tailWeight_eq_sq (v : State) : tailWeight v=(freeBoundary v)^2 := by
  rw [freeBoundary_eq_gate]
  unfold tailWeight
  split_ifs <;> simp [halfWeight_sq]
lemma tail_mode_last (j : Mode) : modeVector j (3 : State)=0 := by
  fin_cases j <;> simp [modeVector,qplus,qminus,plusRaw,minusRaw,plusVector,minusVector,halfScale]
lemma freeBoundary_mode_cancel (j : Mode) (v : State) :
    freeBoundary v*modeVector j v/halfWeight v=modeVector j v := by
  by_cases hv : v.val+1 ≤ 3
  · rw [freeBoundary_eq_gate,if_pos hv]
    field_simp [ne_of_gt (halfWeight_pos v)]
  · have he : v=3 := Fin.ext (by have:=v.isLt; omega)
    subst v
    simp only [tail_mode_last,mul_zero,zero_div]

lemma split_normalizedModeEdge (j : Mode) :
    splitMatrix (fun _ => freeBoundary) (fun _ => normalizedModeEdge j)=
      fun _ => modeRoot j • modeProjector j := by
  funext k v w
  change freeBoundary v*normalizedModeEdge j v w*freeBoundary w=modeRoot j*(modeVector j v*modeVector j w)
  calc
    _ = modeRoot j*(freeBoundary v*modeVector j v/halfWeight v)*
        (freeBoundary w*modeVector j w/halfWeight w) := by
      unfold normalizedModeEdge
      field_simp [ne_of_gt (halfWeight_pos v),ne_of_gt (halfWeight_pos w)]
      <;> ring
    _ = _ := by rw [freeBoundary_mode_cancel,freeBoundary_mode_cancel]; ring

def tailLeftVector (free : Prop) (j : Mode) (left : State) : State→ℝ :=
  if free then freeBoundary else fun v => (modeRoot j*modeVector j left/halfWeight left)*modeVector j v

def tailRightVector (loop : Prop) (j : Mode) (right : State) : State→ℝ :=
  if loop then loopBoundary else fun v => (modeRoot j*modeVector j right/halfWeight right)*modeVector j v

lemma tail_initial_vector (free : Prop) (j : Mode) (left : State) :
    (fun v => tailInitial free j left v*freeBoundary v)=tailLeftVector free j left := by
  funext v
  unfold tailInitial tailLeftVector
  split_ifs
  · simp
  · calc
      normalizedModeEdge j left v*freeBoundary v=
          (modeRoot j*modeVector j left/halfWeight left)*(freeBoundary v*modeVector j v/halfWeight v) := by
        unfold normalizedModeEdge
        field_simp [ne_of_gt (halfWeight_pos left),ne_of_gt (halfWeight_pos v)]
        <;> ring
      _ = _ := by rw [freeBoundary_mode_cancel]

lemma tail_finish_vector (loop : Prop) (j : Mode) (right : State) :
    (fun v => freeBoundary v*tailFinish loop j right v)=tailRightVector loop j right := by
  funext v
  unfold tailFinish tailRightVector
  split_ifs
  · fin_cases v <;> simp_all [freeBoundary,loopBoundary,halfScale]
  · fin_cases v <;> simp_all [freeBoundary,loopBoundary,halfScale]
  · calc
      freeBoundary v*normalizedModeEdge j v right=
          (modeRoot j*modeVector j right/halfWeight right)*(freeBoundary v*modeVector j v/halfWeight v) := by
        unfold normalizedModeEdge
        field_simp [ne_of_gt (halfWeight_pos right),ne_of_gt (halfWeight_pos v)]
        <;> ring
      _ = _ := by rw [freeBoundary_mode_cancel]

lemma matrixRun_constant (n : ℕ) (A : Matrix State State ℝ) : matrixRun n (fun _ => A)=A^n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change A*matrixRun n (fun _ => A)=A^(n+1)
    rw [ih,pow_succ']

/-- Exact finite normalized tail sum, with all physical gates retained. -/
theorem normalizedTailSum_matrix (n : ℕ) (free loop : Prop) (j : Mode) (left right : State) :
    (∑ y : Fin (n+1)→State,normalizedTailTerm n free loop j left right y)=
      tailLeftVector free j left ⬝ᵥ
        (((modeRoot j • modeProjector j)^n)*ᵥ tailRightVector loop j right) := by
  simp_rw [normalizedTailTerm_source]
  have hw : tailWeight=(fun v => (freeBoundary v)^2) := funext tailWeight_eq_sq
  rw [hw]
  rw [weighted_path_eq_matrix,split_normalizedModeEdge,matrixRun_constant,
    tail_initial_vector,tail_finish_vector]

end SubmittedGenus.CapFourMass.CarryLocalization
