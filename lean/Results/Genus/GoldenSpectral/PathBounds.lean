import Results.Genus.GoldenSpectral.RunCharges

/-! Every actual typed golden-q path has at most two unpaid strong frames.
The zero-edge and pure-carry cases are included without introducing a bare
zero-length strong/carry block. -/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.GoldenSpectral
open CapFiveMass.MatrixBounds

def frameMatrix : Option StrongRun→Matrix State State ℝ
  | none => 1
  | some s => runMatrix s

def frameCharge : Option StrongRun→ℕ
  | none => 0
  | some s => runCharge s

def frameBound (s : Option StrongRun) : ℝ := strongBound^frameCharge s

def pathMatrix : PathCode→Matrix State State ℝ
  | .pure s => frameMatrix s
  | .carried pre n _ bs post => frameMatrix pre*carryMatrix^n*(bs.map blockMatrix).prod*frameMatrix post

def pathCharge : PathCode→ℕ
  | .pure s => frameCharge s
  | .carried pre _ _ bs post => frameCharge pre+frameCharge post+(bs.map (fun b => runCharge b.strong)).sum

def pathPaid : PathCode→ℕ
  | .pure _ => 0
  | .carried _ _ _ bs _ => bs.length

def pathRunCount : PathCode→ℕ
  | .pure s => s.toList.length
  | .carried pre _ _ bs post => pre.toList.length+bs.length+post.toList.length

lemma frameCharge_eq (s : Option StrongRun) :
    frameCharge s=CapFourMass.ActualComponent.optionalStrongCount s+
      2*CapFourMass.ActualComponent.optionalRestrictedCount s := by
  cases s with
  | none => rfl
  | some s => exact runCharge_eq s

lemma pathCharge_eq (q : PathCode) : pathCharge q=q.strongCount+2*q.restrictedCount := by
  cases q with
  | pure s => exact frameCharge_eq s
  | carried pre n hn bs post =>
    simp only [pathCharge,CapFourMass.ActualComponent.PathCode.strongCount,
      CapFourMass.ActualComponent.PathCode.restrictedCount,frameCharge_eq,blocks_charge_eq]
    ring

lemma pathPaid_conservative (q : PathCode) : pathRunCount q-2 ≤ pathPaid q := by
  cases q with
  | pure s => cases s <;> simp [pathRunCount,pathPaid]
  | carried pre n hn bs post => cases pre <;> cases post <;> simp [pathRunCount,pathPaid] <;> omega

lemma frameBound_nonneg (s : Option StrongRun) : 0 ≤ frameBound s := pow_nonneg strongBound_pos.le _
lemma frameMatrix_symmetric (s : Option StrongRun) : (frameMatrix s).transpose=frameMatrix s := by
  cases s with
  | none => simp [frameMatrix]
  | some s => exact runMatrix_symmetric s
lemma frame_energy_le (s : Option StrongRun) (x : State→ℝ) :
    vectorEnergy (frameMatrix s*ᵥ x) ≤ (frameBound s)^2*vectorEnergy x := by
  cases s with
  | none => simp [frameMatrix,frameBound,frameCharge]
  | some s => exact run_energy_le s x
lemma frame_sqrt_energy_le (s : Option StrongRun) (x : State→ℝ) :
    Real.sqrt (vectorEnergy (frameMatrix s*ᵥ x)) ≤ frameBound s*Real.sqrt (vectorEnergy x) :=
  CapFourMass.sqrt_energy_le (frameBound_nonneg s) (frame_energy_le s x)
lemma frame_path_le (s : Option StrongRun) (x y : State→ℝ) :
    x ⬝ᵥ (frameMatrix s*ᵥ y) ≤ Real.sqrt (vectorEnergy x)*Real.sqrt (vectorEnergy y)*frameBound s := by
  have h:=(dot_le_sqrt_energy x (frameMatrix s*ᵥ y)).trans
    (mul_le_mul_of_nonneg_left (frame_sqrt_energy_le s y) (Real.sqrt_nonneg _))
  exact h.trans_eq (by ring)

lemma framed_path_eq (pre post : Option StrongRun) (n : ℕ) (bs : List CoupledRun) (x y : State→ℝ) :
    x ⬝ᵥ ((frameMatrix pre*carryMatrix^n*(bs.map blockMatrix).prod*frameMatrix post)*ᵥ y)=
      (frameMatrix pre*ᵥ x) ⬝ᵥ ((carryMatrix^n*(bs.map blockMatrix).prod)*ᵥ (frameMatrix post*ᵥ y)) := by
  simp only [Matrix.mul_assoc,←Matrix.mulVec_mulVec]
  have h:=Matrix.dotProduct_transpose_mulVec (frameMatrix pre) x
    (carryMatrix^n*ᵥ ((bs.map blockMatrix).prod*ᵥ (frameMatrix post*ᵥ y)))
  rw [frameMatrix_symmetric] at h
  exact h.trans (dotProduct_comm _ _)

lemma framed_path_le (pre post : Option StrongRun) (n : ℕ) (hn : 1 ≤ n)
    (bs : List CoupledRun) (x y : State→ℝ) :
    x ⬝ᵥ ((frameMatrix pre*carryMatrix^n*(bs.map blockMatrix).prod*frameMatrix post)*ᵥ y) ≤
      Real.sqrt (vectorEnergy x)*Real.sqrt (vectorEnergy y)*
        (frameBound pre*frameBound post*pathInflation*(bs.map (fun b => (blockDominated b).bound)).prod) := by
  rw [framed_path_eq]
  have h:=(carry_coupled_path_le_absolute n hn bs (frameMatrix pre*ᵥ x) (frameMatrix post*ᵥ y)).trans
    (coupledPathAbsolute_le n bs _ _)
  have hp:=mul_nonneg pathInflation_pos.le (block_bounds_nonneg bs)
  have hh:=mul_le_mul_of_nonneg_right
    (mul_le_mul (frame_sqrt_energy_le pre x) (frame_sqrt_energy_le post y)
      (Real.sqrt_nonneg _) (mul_nonneg (frameBound_nonneg pre) (Real.sqrt_nonneg _))) hp
  exact h.trans (hh.trans_eq (by ring))

/-- Exact original edge charge and paid-block exponent, with only one k0 per path. -/
theorem path_paid_bound (q : PathCode) (x y : State→ℝ) :
    x ⬝ᵥ (pathMatrix q*ᵥ y) ≤ Real.sqrt (vectorEnergy x)*Real.sqrt (vectorEnergy y)*
      pathInflation*strongBound^(q.strongCount+2*q.restrictedCount)*paidCost^(pathPaid q) := by
  rw [←pathCharge_eq]
  cases q with
  | pure s =>
    simp only [pathMatrix,pathCharge,pathPaid,pow_zero,mul_one]
    have h:=frame_path_le s x y
    have hh:=mul_le_mul_of_nonneg_right
      (le_mul_of_one_le_right (mul_nonneg (Real.sqrt_nonneg (vectorEnergy x))
        (Real.sqrt_nonneg (vectorEnergy y))) pathInflation_one_le)
      (frameBound_nonneg s)
    exact h.trans hh
  | carried pre n hn bs post =>
    have h:=framed_path_le pre post n hn bs x y
    have hh:=mul_le_mul_of_nonneg_left (blocks_paid_charge bs)
      (mul_nonneg (mul_nonneg (frameBound_nonneg pre) (frameBound_nonneg post)) pathInflation_pos.le)
    have hh':=mul_le_mul_of_nonneg_left hh (mul_nonneg (Real.sqrt_nonneg (vectorEnergy x))
      (Real.sqrt_nonneg (vectorEnergy y)))
    exact h.trans (hh'.trans_eq (by
      simp only [pathCharge,pathPaid,frameBound,pow_add]
      ring))

/-- Two endpoint strong runs may be discarded uniformly in the paid count. -/
theorem path_conservative_bound (q : PathCode) (x y : State→ℝ) :
    x ⬝ᵥ (pathMatrix q*ᵥ y) ≤ Real.sqrt (vectorEnergy x)*Real.sqrt (vectorEnergy y)*
      pathInflation*strongBound^(q.strongCount+2*q.restrictedCount)*paidCost^(pathRunCount q-2) := by
  apply (path_paid_bound q x y).trans
  exact mul_le_mul_of_nonneg_left (paid_exponent_weaken _ _ (pathPaid_conservative q))
    (mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      pathInflation_pos.le) (pow_nonneg strongBound_pos.le _))

end SubmittedGenus.GoldenSpectral
