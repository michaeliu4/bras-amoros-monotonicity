import Results.Genus.CapFourMass.EndpointBounds
import Results.Genus.CapFourMass.ModePartitions

/-!
# Exact alternating-run compilation and its analytic bounds

Every coupled block has a positive carry length. A path's leading carry run is
kept in its boundary; a cycle is cut at a strong/carry transition. No estimate
for a bare projected strong run is used.
-/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFourMass
open CapFiveMass.MatrixBounds

inductive StrongRun
  | full (length : ℕ) (positive : 1≤length)
  | restricted

def StrongRun.matrix : StrongRun → Matrix State State ℝ
  | .full k _ => strongMatrix^k
  | .restricted => restrictedMatrix

def StrongRun.bound : StrongRun → ℝ
  | .full k _ => strongBound^k
  | .restricted => restrictedBound

structure CoupledRun where
  strong : StrongRun
  carryLength : ℕ
  carryPositive : 1≤carryLength

def CoupledRun.matrix (b : CoupledRun) : Matrix State State ℝ :=
  b.strong.matrix*carryMatrix^b.carryLength

def CoupledRun.spectral (b : CoupledRun) : Matrix Mode Mode ℝ :=
  coupledBlock b.strong.matrix b.carryLength

def CoupledRun.dominated (b : CoupledRun) : DominatedBlock :=
  match b.strong with
  | .full k hk => strongBlock k b.carryLength hk b.carryPositive
  | .restricted => restrictedBlock b.carryLength b.carryPositive

lemma CoupledRun.dominated_matrix (b : CoupledRun) :
    b.dominated.matrix=absoluteMatrix b.spectral := by cases b with | mk s n hn => cases s <;> rfl
lemma CoupledRun.dominated_bound (b : CoupledRun) :
    b.dominated.bound=b.strong.bound*lam^b.carryLength := by cases b with | mk s n hn => cases s <;> rfl

lemma carry_power_matrix (n : ℕ) (hn : 1≤n) :
    carryMatrix^n=modeMatrix*Matrix.diagonal (fun j => modeRoot j^n)*modeMatrix.transpose := by
  obtain ⟨k,rfl⟩ : ∃ k,n=k+1 := ⟨n-1,by omega⟩
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  rw [carry_power_modes]
  simp only [← Matrix.mulVec_mulVec]
  ext i
  simp only [Matrix.mulVec_diagonal,modeMatrix,Matrix.transpose_apply,
    Matrix.mulVec,dotProduct,Fin.sum_univ_two,modeVector,modeRoot,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  norm_num [Matrix.diagonal,modeRoot]
  ring

lemma coupled_run_left (b : CoupledRun) :
    modeMatrix.transpose*b.matrix=b.spectral*modeMatrix.transpose := by
  rw [CoupledRun.matrix,carry_power_matrix b.carryLength b.carryPositive]
  simp only [CoupledRun.spectral,coupledBlock,projected,Matrix.mul_assoc]

lemma coupled_runs_left (l : List CoupledRun) :
    modeMatrix.transpose*(l.map CoupledRun.matrix).prod=
      (l.map CoupledRun.spectral).prod*modeMatrix.transpose := by
  induction l with
  | nil => simp
  | cons b l ih =>
    simp only [List.map_cons,List.prod_cons]
    rw [← Matrix.mul_assoc,coupled_run_left,Matrix.mul_assoc,ih,← Matrix.mul_assoc]

/-- Exact source-to-mode conversion, with no absolute values or estimates yet. -/
theorem coupled_cycle_eq_spectral (b : CoupledRun) (l : List CoupledRun) :
    (b.matrix*(l.map CoupledRun.matrix).prod).trace=
      (b.spectral*(l.map CoupledRun.spectral).prod).trace := by
  rw [CoupledRun.matrix,carry_power_matrix b.carryLength b.carryPositive]
  simp only [Matrix.mul_assoc]
  rw [coupled_runs_left]
  rw [← Matrix.mul_assoc,← Matrix.mul_assoc,Matrix.trace_mul_comm]
  simp only [CoupledRun.spectral,coupledBlock,projected,Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

/-- A path begins at a positive carry run after absorbing its strong prefix. -/
theorem carry_coupled_path_eq_spectral (n : ℕ) (hn : 1≤n) (l : List CoupledRun)
    (x y : State → ℝ) :
    x ⬝ᵥ ((carryMatrix^n*(l.map CoupledRun.matrix).prod)*ᵥ y)=
      (fun j => modeRoot j^n*(modeVector j ⬝ᵥ x)) ⬝ᵥ
        ((l.map CoupledRun.spectral).prod *ᵥ (modeMatrix.transpose *ᵥ y)) := by
  rw [carry_power_matrix n hn,Matrix.mul_assoc,coupled_runs_left]
  rw [← Matrix.mulVec_mulVec,Matrix.dotProduct_mulVec]
  simp only [← Matrix.mulVec_mulVec,← Matrix.vecMul_vecMul,Matrix.vecMul_diagonal]
  congr 1
  ext j
  rw [Matrix.vecMul_diagonal]
  simp only [Matrix.vecMul,modeMatrix,Matrix.transpose_apply,dotProduct]
  rw [mul_comm]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => mul_comm (x i) (modeVector j i))

lemma absolute_matrix_mul_le (A B : Matrix Mode Mode ℝ) (i j : Mode) :
    |(A*B) i j| ≤ (absoluteMatrix A*absoluteMatrix B) i j := by
  rw [Matrix.mul_apply,Matrix.mul_apply]
  calc
    _ ≤ ∑ k,|A i k*B k j| := Finset.abs_sum_le_sum_abs _ _
    _ = _ := by simp only [abs_mul,absoluteMatrix]

lemma absolute_matrix_product_le (l : List (Matrix Mode Mode ℝ)) (i j : Mode) :
    |l.prod i j| ≤ ((l.map absoluteMatrix).prod) i j := by
  induction l generalizing i j with
  | nil => simp [Matrix.one_apply]; split_ifs <;> norm_num
  | cons A l ih =>
    simp only [List.prod_cons,List.map_cons]
    apply (absolute_matrix_mul_le A l.prod i j).trans
    rw [Matrix.mul_apply,Matrix.mul_apply]
    exact Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (ih k j) (abs_nonneg _))

lemma signed_cycle_le_absolute (l : List (Matrix Mode Mode ℝ)) :
    l.prod.trace ≤ (l.map absoluteMatrix).prod.trace := by
  apply Finset.sum_le_sum
  intro i _
  exact (le_abs_self _).trans (absolute_matrix_product_le l i i)

/-- Actual alternating cycle words satisfy the dimension-free source bound. -/
theorem coupled_cycle_le (b : CoupledRun) (l : List CoupledRun) :
    (b.matrix*(l.map CoupledRun.matrix).prod).trace ≤
      b.dominated.bound*(l.map (fun b => b.dominated.bound)).prod := by
  rw [coupled_cycle_eq_spectral]
  have hh:=signed_cycle_le_absolute ((b::l).map CoupledRun.spectral)
  simp only [List.map_cons,List.prod_cons,List.map_map,Function.comp_def] at hh
  have he : (l.map (fun b => absoluteMatrix b.spectral)).prod=
      ((l.map CoupledRun.dominated).map DominatedBlock.matrix).prod := by
    simp only [List.map_map,Function.comp_def,CoupledRun.dominated_matrix]
  rw [← b.dominated_matrix,he] at hh
  exact hh.trans (by simpa only [List.map_map,Function.comp_def] using
    spectral_cycle_le b.dominated (l.map CoupledRun.dominated))

lemma signed_path_le_absolute (l : List (Matrix Mode Mode ℝ)) (x y : Mode → ℝ) :
    x ⬝ᵥ (l.prod *ᵥ y) ≤
      (fun i => |x i|) ⬝ᵥ ((l.map absoluteMatrix).prod *ᵥ (fun i => |y i|)) := by
  simp only [Matrix.mulVec,dotProduct,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  calc
    x i*(l.prod i j*y j) ≤ |x i*(l.prod i j*y j)| := le_abs_self _
    _ = |x i| *|l.prod i j| *|y j| := by rw [abs_mul,abs_mul]; ring
    _ ≤ |x i| *(l.map absoluteMatrix).prod i j*|y j| :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (absolute_matrix_product_le l i j) (abs_nonneg _)) (abs_nonneg _)
    _ = _ := by ring

/-- Sum of absolute complete carry-mode assignments for this path word. -/
def coupledPathAbsolute (n : ℕ) (l : List CoupledRun) (x y : State → ℝ) : ℝ :=
  carryBoundary n x ⬝ᵥ
    ((l.map (fun b => b.dominated.matrix)).prod *ᵥ modeBoundary y)

lemma coupledPathAbsolute_nil (n : ℕ) (x y : State → ℝ) :
    coupledPathAbsolute n [] x y=carryAbsolute n x y := by
  simp only [coupledPathAbsolute,List.map_nil,List.prod_nil,Matrix.one_mulVec,
    carryAbsolute,dotProduct,carryBoundary,modeBoundary]
  apply Finset.sum_congr rfl
  intro j _
  rw [abs_mul,abs_mul,abs_mul]
  have he : (∑ i, x i*modeVector j i)=(∑ i, modeVector j i*x i) :=
    Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  rw [he]
  ring

lemma sqrt_energy_le {ι : Type*} [Fintype ι] {v : ι → ℝ} {c E : ℝ} (hc : 0≤c)
    (he : vectorEnergy v ≤ c^2*E) : Real.sqrt (vectorEnergy v) ≤ c*Real.sqrt E := by
  calc
    _ ≤ Real.sqrt (c^2*E) := Real.sqrt_le_sqrt he
    _ = _ := by rw [Real.sqrt_mul (sq_nonneg c),Real.sqrt_sq hc]

/-- Absolute source path bound with no extra factor for internal mode junctions.
The leading carry boundary may also have length zero for the separately
justified isolated free/carry-loop corner. -/
theorem coupledPathAbsolute_le (n : ℕ) (l : List CoupledRun) (x y : State → ℝ) :
    coupledPathAbsolute n l x y ≤
      Real.sqrt (vectorEnergy x)*Real.sqrt (vectorEnergy y)*
        (lam^n*(l.map (fun b => b.dominated.bound)).prod) := by
  cases l with
  | nil => simpa only [List.map_nil,List.prod_nil,mul_one,coupledPathAbsolute_nil] using carryAbsolute_le n x y
  | cons b l =>
    have hc : Real.sqrt (vectorEnergy (carryBoundary n x)) ≤ lam^n*Real.sqrt (vectorEnergy x) :=
      sqrt_energy_le (pow_nonneg lam_pos.le n) (by
        simpa only [← pow_mul,Nat.mul_comm n 2] using carryBoundary_energy n x)
    have hy := Real.sqrt_le_sqrt (modeBoundary_energy y)
    have hh:=spectral_path_le b.dominated (l.map CoupledRun.dominated) (carryBoundary n x) (modeBoundary y)
    have hp : 0 ≤ b.dominated.bound*(l.map (fun b => b.dominated.bound)).prod :=
      mul_nonneg b.dominated.bound_nonneg (List.prod_nonneg (by
        intro t ht
        obtain ⟨a,ha,rfl⟩:=List.mem_map.mp ht
        exact a.dominated.bound_nonneg))
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul hc hy (Real.sqrt_nonneg _) (mul_nonneg (pow_nonneg lam_pos.le _) (Real.sqrt_nonneg _))) hp
    simp only [List.map_map,Function.comp_def] at hh
    change coupledPathAbsolute n (b::l) x y ≤ _
    unfold coupledPathAbsolute
    simp only [List.map_cons,List.prod_cons]
    exact hh.trans (h.trans_eq (by ring))

/-- The signed actual path word is dominated by the same absolute-mode scalar. -/
theorem carry_coupled_path_le_absolute (n : ℕ) (hn : 1≤n) (l : List CoupledRun)
    (x y : State → ℝ) :
    x ⬝ᵥ ((carryMatrix^n*(l.map CoupledRun.matrix).prod)*ᵥ y) ≤ coupledPathAbsolute n l x y := by
  rw [carry_coupled_path_eq_spectral n hn]
  have hh:=signed_path_le_absolute (l.map CoupledRun.spectral)
    (fun j => modeRoot j^n*(modeVector j ⬝ᵥ x)) (modeMatrix.transpose *ᵥ y)
  simpa only [coupledPathAbsolute,carryBoundary,modeBoundary,List.map_map,Function.comp_def,
    CoupledRun.dominated_matrix,modeMatrix,Matrix.mulVec,Matrix.transpose_apply,dotProduct] using hh

/-- The generic actual path estimate consumed by the computed run layout. -/
theorem carry_coupled_path_le (n : ℕ) (hn : 1≤n) (l : List CoupledRun)
    (x y : State → ℝ) :
    x ⬝ᵥ ((carryMatrix^n*(l.map CoupledRun.matrix).prod)*ᵥ y) ≤
      Real.sqrt (vectorEnergy x)*Real.sqrt (vectorEnergy y)*
        (lam^n*(l.map (fun b => b.dominated.bound)).prod) :=
  (carry_coupled_path_le_absolute n hn l x y).trans (coupledPathAbsolute_le n l x y)

lemma StrongRun.bound_nonneg (s : StrongRun) : 0 ≤ s.bound := by
  cases s with
  | full k hk => exact pow_nonneg strongBound_pos.le k
  | restricted => norm_num [StrongRun.bound,restrictedBound]

lemma StrongRun.symmetric (s : StrongRun) : s.matrix.transpose=s.matrix := by
  cases s with
  | full k hk => exact strong_power_symmetric k
  | restricted => exact transfer_symmetric 4 3

lemma StrongRun.energy_le (s : StrongRun) (x : State → ℝ) :
    vectorEnergy (s.matrix *ᵥ x) ≤ s.bound^2*vectorEnergy x := by
  cases s with
  | full k hk => simpa only [StrongRun.matrix,StrongRun.bound,← pow_mul,Nat.mul_comm k 2] using strong_power_energy_le k x
  | restricted => exact restricted_energy_le x

lemma StrongRun.sqrt_energy_le (s : StrongRun) (x : State → ℝ) :
    Real.sqrt (vectorEnergy (s.matrix *ᵥ x)) ≤ s.bound*Real.sqrt (vectorEnergy x) :=
  CapFourMass.sqrt_energy_le s.bound_nonneg (s.energy_le x)

/-- A component with no carry edges uses only the ordinary operator estimate. -/
theorem StrongRun.path_le (s : StrongRun) (x y : State → ℝ) :
    x ⬝ᵥ (s.matrix *ᵥ y) ≤ Real.sqrt (vectorEnergy x)*Real.sqrt (vectorEnergy y)*s.bound := by
  apply le_of_sq_le_sq _ (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) s.bound_nonneg)
  have hh:=(dot_sq_le x (s.matrix *ᵥ y)).trans
    (mul_le_mul_of_nonneg_left (s.energy_le y) (vectorEnergy_nonneg x))
  simpa only [mul_pow,Real.sq_sqrt (vectorEnergy_nonneg x),
    Real.sq_sqrt (vectorEnergy_nonneg y),mul_assoc,mul_comm,mul_left_comm] using hh

/-- Strong prefixes and suffixes are absorbed in the actual boundary vectors;
their scalar costs multiply exactly, without an extra path factor. -/
theorem framedCoupledPathAbsolute_le (pre post : StrongRun) (n : ℕ) (l : List CoupledRun)
    (x y : State → ℝ) :
    coupledPathAbsolute n l (pre.matrix *ᵥ x) (post.matrix *ᵥ y) ≤
      Real.sqrt (vectorEnergy x)*Real.sqrt (vectorEnergy y)*
        (pre.bound*post.bound*lam^n*(l.map (fun b => b.dominated.bound)).prod) := by
  have hh:=coupledPathAbsolute_le n l (pre.matrix *ᵥ x) (post.matrix *ᵥ y)
  have hp : 0≤lam^n*(l.map (fun b => b.dominated.bound)).prod :=
    mul_nonneg (pow_nonneg lam_pos.le _) (List.prod_nonneg (by
      intro t ht
      obtain ⟨b,hb,rfl⟩:=List.mem_map.mp ht
      exact b.dominated.bound_nonneg))
  have h:=mul_le_mul_of_nonneg_right
    (mul_le_mul (pre.sqrt_energy_le x) (post.sqrt_energy_le y) (Real.sqrt_nonneg _)
      (mul_nonneg pre.bound_nonneg (Real.sqrt_nonneg _))) hp
  exact hh.trans (h.trans_eq (by ring))

/-- Trace of the absolute complete-mode product, the cycle spectral envelope. -/
def coupledCycleAbsolute (l : List CoupledRun) : ℝ :=
  (l.map (fun b : CoupledRun => (CoupledRun.dominated b).matrix)).prod.trace

lemma coupledCycleAbsolute_le (b : CoupledRun) (l : List CoupledRun) :
    coupledCycleAbsolute (b::l) ≤
      b.dominated.bound*(l.map (fun b => b.dominated.bound)).prod := by
  simpa only [coupledCycleAbsolute,List.map_cons,List.prod_cons,List.map_map,Function.comp_def]
    using spectral_cycle_le b.dominated (l.map CoupledRun.dominated)

end SubmittedGenus.CapFourMass
