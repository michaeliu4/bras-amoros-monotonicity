import Results.Genus.GoldenSpectral.Endpoints
import Results.Genus.GoldenSpectral.RankProducts
import Results.Genus.CapFourMass.CompilerCounts

/-! Golden-q interpretation of the already computed actual strong/carry run
syntax. Only genuinely positive carry runs enter spectral blocks. -/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.GoldenSpectral
open CapFiveMass.MatrixBounds
abbrev StrongRun := CapFourMass.StrongRun
abbrev CoupledRun := CapFourMass.CoupledRun
abbrev PathCode := CapFourMass.ActualComponent.PathCode

def runMatrix : StrongRun→Matrix State State ℝ
  | .full k _ => strongMatrix^k
  | .restricted => restrictedMatrix

def runCharge : StrongRun→ℕ
  | .full k _ => k
  | .restricted => 3

def runBound (s : StrongRun) : ℝ := strongBound^runCharge s

def blockMatrix (b : CoupledRun) : Matrix State State ℝ := runMatrix b.strong*carryMatrix^b.carryLength

def blockSpectral (b : CoupledRun) : Matrix Mode Mode ℝ := coupledBlock (runMatrix b.strong) b.carryLength

def blockDominated (b : CoupledRun) : DominatedBlock :=
  match b.strong with
  | .full k hk => strongBlock k b.carryLength hk b.carryPositive
  | .restricted => restrictedBlock b.carryLength b.carryPositive

lemma blockDominated_matrix (b : CoupledRun) :
    (blockDominated b).matrix=absoluteMatrix (blockSpectral b) := by
  cases b with | mk s n hn => cases s <;> rfl

lemma runCharge_eq (s : StrongRun) : runCharge s=s.strongCount+2*s.restrictedCount := by
  cases s <;> simp [runCharge,CapFourMass.StrongRun.strongCount,CapFourMass.StrongRun.restrictedCount]

lemma runMatrix_symmetric (s : StrongRun) : (runMatrix s).transpose=runMatrix s := by
  cases s with
  | full k hk => exact strong_power_symmetric k
  | restricted => exact transfer_symmetric 4 3

lemma runBound_nonneg (s : StrongRun) : 0 ≤ runBound s := pow_nonneg strongBound_pos.le _

lemma run_energy_le (s : StrongRun) (x : State→ℝ) :
    vectorEnergy (runMatrix s*ᵥ x) ≤ (runBound s)^2*vectorEnergy x := by
  cases s with
  | full k hk =>
    simpa only [runMatrix,runBound,runCharge,←pow_mul,Nat.mul_comm k 2] using strong_power_energy_le k x
  | restricted =>
    apply (restricted_energy_le x).trans
    apply mul_le_mul_of_nonneg_right _ (vectorEnergy_nonneg x)
    change restrictedBound^2 ≤ (strongBound^3)^2
    apply pow_le_pow_left₀ (by norm_num [restrictedBound])
    exact paid_decay_comparisons.2.2.1.le

lemma run_sqrt_energy_le (s : StrongRun) (x : State→ℝ) :
    Real.sqrt (vectorEnergy (runMatrix s*ᵥ x)) ≤ runBound s*Real.sqrt (vectorEnergy x) :=
  CapFourMass.sqrt_energy_le (runBound_nonneg s) (run_energy_le s x)

lemma coupled_run_left (b : CoupledRun) :
    modeMatrix.transpose*blockMatrix b=blockSpectral b*modeMatrix.transpose := by
  rw [blockMatrix,carry_power_matrix b.carryLength b.carryPositive]
  simp only [blockSpectral,coupledBlock,projected,Matrix.mul_assoc]

lemma coupled_runs_left (l : List CoupledRun) :
    modeMatrix.transpose*(l.map blockMatrix).prod=(l.map blockSpectral).prod*modeMatrix.transpose := by
  induction l with
  | nil => simp
  | cons b l ih =>
    simp only [List.map_cons,List.prod_cons]
    rw [←Matrix.mul_assoc,coupled_run_left,Matrix.mul_assoc,ih,←Matrix.mul_assoc]

theorem coupled_cycle_eq_spectral (b : CoupledRun) (l : List CoupledRun) :
    (blockMatrix b*(l.map blockMatrix).prod).trace=
      (blockSpectral b*(l.map blockSpectral).prod).trace := by
  rw [blockMatrix,carry_power_matrix b.carryLength b.carryPositive]
  simp only [Matrix.mul_assoc]
  rw [coupled_runs_left]
  rw [←Matrix.mul_assoc,←Matrix.mul_assoc,Matrix.trace_mul_comm]
  simp only [blockSpectral,coupledBlock,projected,Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem carry_coupled_path_eq_spectral (n : ℕ) (hn : 1 ≤ n) (l : List CoupledRun)
    (x y : State→ℝ) :
    x ⬝ᵥ ((carryMatrix^n*(l.map blockMatrix).prod)*ᵥ y)=
      (fun j => modeRoot j^n*(modeVector j ⬝ᵥ x)) ⬝ᵥ
        ((l.map blockSpectral).prod*ᵥ (modeMatrix.transpose*ᵥ y)) := by
  rw [carry_power_matrix n hn,Matrix.mul_assoc,coupled_runs_left]
  rw [←Matrix.mulVec_mulVec,Matrix.dotProduct_mulVec]
  simp only [←Matrix.mulVec_mulVec,←Matrix.vecMul_vecMul,Matrix.vecMul_diagonal]
  congr 1
  ext j
  rw [Matrix.vecMul_diagonal]
  simp only [Matrix.vecMul,modeMatrix,Matrix.transpose_apply,dotProduct]
  rw [mul_comm]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => mul_comm (x i) (modeVector j i))

theorem coupled_cycle_le (b : CoupledRun) (l : List CoupledRun) :
    (blockMatrix b*(l.map blockMatrix).prod).trace ≤
      (blockDominated b).bound*(l.map (fun b => (blockDominated b).bound)).prod := by
  rw [coupled_cycle_eq_spectral]
  have hh:=CapFourMass.signed_cycle_le_absolute ((b::l).map blockSpectral)
  change (blockSpectral b*(l.map blockSpectral).prod).trace ≤
    (((b::l).map blockSpectral).map absoluteMatrix).prod.trace at hh
  simp only [List.map_cons,List.prod_cons,List.map_map,Function.comp_def] at hh
  have he : (l.map (fun b => absoluteMatrix (blockSpectral b))).prod=
      ((l.map blockDominated).map DominatedBlock.matrix).prod := by
    simp only [List.map_map,Function.comp_def,blockDominated_matrix]
  rw [←blockDominated_matrix b,he] at hh
  exact hh.trans (by simpa only [List.map_map,Function.comp_def] using
    spectral_cycle_le (blockDominated b) (l.map blockDominated))

def coupledPathAbsolute (n : ℕ) (l : List CoupledRun) (x y : State→ℝ) : ℝ :=
  carryBoundary n x ⬝ᵥ ((l.map (fun b => (blockDominated b).matrix)).prod*ᵥ modeBoundary y)

lemma dot_le_sqrt_energy {A : Type*} [Fintype A] [DecidableEq A] (x y : A→ℝ) :
    x ⬝ᵥ y ≤ Real.sqrt (vectorEnergy x)*Real.sqrt (vectorEnergy y) := by
  apply le_of_sq_le_sq _ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  simpa only [mul_pow,Real.sq_sqrt (vectorEnergy_nonneg x),Real.sq_sqrt (vectorEnergy_nonneg y)] using dot_sq_le x y

lemma pathInflation_one_le : 1 ≤ pathInflation := by norm_num [pathInflation]

theorem coupledPathAbsolute_le (n : ℕ) (l : List CoupledRun) (x y : State→ℝ) :
    coupledPathAbsolute n l x y ≤
      Real.sqrt (vectorEnergy x)*Real.sqrt (vectorEnergy y)*
        (pathInflation*(l.map (fun b => (blockDominated b).bound)).prod) := by
  have hc:=Real.sqrt_le_sqrt (carryBoundary_energy n x)
  have hy:=Real.sqrt_le_sqrt (modeBoundary_energy y)
  cases l with
  | nil =>
    simp only [coupledPathAbsolute,List.map_nil,List.prod_nil,Matrix.one_mulVec,mul_one]
    apply (dot_le_sqrt_energy _ _).trans
    apply (mul_le_mul hc hy (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).trans
    exact le_mul_of_one_le_right (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) pathInflation_one_le
  | cons b l =>
    have hh:=spectral_path_le (blockDominated b) (l.map blockDominated) (carryBoundary n x) (modeBoundary y)
    have hp : 0 ≤ pathInflation*((blockDominated b).bound*(l.map (fun b => (blockDominated b).bound)).prod) :=
      mul_nonneg pathInflation_pos.le (mul_nonneg (blockDominated b).bound_nonneg
        (List.prod_nonneg (by
          intro t ht
          obtain ⟨a,ha,rfl⟩:=List.mem_map.mp ht
          exact (blockDominated a).bound_nonneg)))
    have h:=mul_le_mul_of_nonneg_right
      (mul_le_mul hc hy (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hp
    simp only [List.map_map,Function.comp_def] at hh
    change coupledPathAbsolute n (b::l) x y ≤ _
    unfold coupledPathAbsolute
    simp only [List.map_cons,List.prod_cons]
    exact hh.trans h

theorem carry_coupled_path_le_absolute (n : ℕ) (hn : 1 ≤ n) (l : List CoupledRun)
    (x y : State→ℝ) :
    x ⬝ᵥ ((carryMatrix^n*(l.map blockMatrix).prod)*ᵥ y) ≤ coupledPathAbsolute n l x y := by
  rw [carry_coupled_path_eq_spectral n hn]
  have hh:=CapFourMass.signed_path_le_absolute (l.map blockSpectral)
    (fun j => modeRoot j^n*(modeVector j ⬝ᵥ x)) (modeMatrix.transpose*ᵥ y)
  change _ ≤ (fun j => |modeRoot j^n*(modeVector j ⬝ᵥ x)|) ⬝ᵥ
    (((l.map blockSpectral).map absoluteMatrix).prod*ᵥ (fun j => |(modeMatrix.transpose*ᵥ y) j|)) at hh
  simpa only [coupledPathAbsolute,carryBoundary,modeBoundary,List.map_map,Function.comp_def,
    blockDominated_matrix,absoluteMatrix,CapFourMass.absoluteMatrix,modeMatrix,
    Matrix.mulVec,Matrix.transpose_apply,dotProduct] using hh

end SubmittedGenus.GoldenSpectral
