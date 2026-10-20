import Results.Genus.CapFourMass.RunBounds

/-! Optional strong prefix/suffix frames for every actual alternating path normal form. -/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFourMass
open CapFiveMass.MatrixBounds

def frameMatrix : Option StrongRun → Matrix State State ℝ
  | none => 1
  | some s => s.matrix

def frameBound : Option StrongRun → ℝ
  | none => 1
  | some s => s.bound

def frameStrongCount : Option StrongRun → ℕ
  | none => 0
  | some s => s.strongCount

def frameRestrictedCount : Option StrongRun → ℕ
  | none => 0
  | some s => s.restrictedCount

lemma frameBound_nonneg (s : Option StrongRun) : 0≤frameBound s := by
  cases s with
  | none => norm_num [frameBound]
  | some s => exact s.bound_nonneg

lemma frameBound_eq (s : Option StrongRun) :
    frameBound s=strongBound^(frameStrongCount s)*sigma^(frameRestrictedCount s) := by
  cases s with
  | none => simp [frameBound,frameStrongCount,frameRestrictedCount]
  | some s => exact s.bound_eq

lemma frameMatrix_symmetric (s : Option StrongRun) : (frameMatrix s).transpose=frameMatrix s := by
  cases s with
  | none => simp [frameMatrix]
  | some s => exact s.symmetric

lemma frame_energy_le (s : Option StrongRun) (x : State → ℝ) :
    vectorEnergy (frameMatrix s *ᵥ x) ≤ (frameBound s)^2*vectorEnergy x := by
  cases s with
  | none => simp [frameMatrix,frameBound]
  | some s => exact s.energy_le x

lemma frame_sqrt_energy_le (s : Option StrongRun) (x : State → ℝ) :
    Real.sqrt (vectorEnergy (frameMatrix s *ᵥ x)) ≤ frameBound s*Real.sqrt (vectorEnergy x) :=
  sqrt_energy_le (frameBound_nonneg s) (frame_energy_le s x)

def framedPathAbsolute (pre post : Option StrongRun) (n : ℕ) (l : List CoupledRun)
    (x y : State → ℝ) : ℝ :=
  coupledPathAbsolute n l (frameMatrix pre *ᵥ x) (frameMatrix post *ᵥ y)

/-- Exact source boundary absorption, before taking any absolute values. -/
lemma optional_frame_path_eq (pre post : Option StrongRun) (n : ℕ) (l : List CoupledRun)
    (x y : State → ℝ) :
    x ⬝ᵥ ((frameMatrix pre*carryMatrix^n*(l.map CoupledRun.matrix).prod*frameMatrix post)*ᵥ y)=
      (frameMatrix pre *ᵥ x) ⬝ᵥ
        ((carryMatrix^n*(l.map CoupledRun.matrix).prod)*ᵥ (frameMatrix post *ᵥ y)) := by
  simp only [Matrix.mul_assoc,← Matrix.mulVec_mulVec]
  have hh:=Matrix.dotProduct_transpose_mulVec (frameMatrix pre) x
    (carryMatrix^n *ᵥ ((l.map CoupledRun.matrix).prod *ᵥ (frameMatrix post *ᵥ y)))
  rw [frameMatrix_symmetric] at hh
  exact hh.trans (dotProduct_comm _ _)

/-- The exact signed path word is bounded by its absolute complete-mode scalar. -/
theorem optional_frame_path_le_absolute (pre post : Option StrongRun) (n : ℕ) (hn : 1≤n)
    (l : List CoupledRun) (x y : State → ℝ) :
    x ⬝ᵥ ((frameMatrix pre*carryMatrix^n*(l.map CoupledRun.matrix).prod*frameMatrix post)*ᵥ y) ≤
      framedPathAbsolute pre post n l x y := by
  rw [optional_frame_path_eq]
  exact carry_coupled_path_le_absolute n hn l _ _

/-- Missing strong frames cost exactly one; present frames retain their actual
D^k or single-E norm cost. -/
theorem optional_frame_absolute_le (pre post : Option StrongRun) (n : ℕ) (l : List CoupledRun)
    (x y : State → ℝ) :
    framedPathAbsolute pre post n l x y ≤
      Real.sqrt (vectorEnergy x)*Real.sqrt (vectorEnergy y)*
        (frameBound pre*frameBound post*lam^n*(l.map (fun b => b.dominated.bound)).prod) := by
  have hh:=coupledPathAbsolute_le n l (frameMatrix pre *ᵥ x) (frameMatrix post *ᵥ y)
  have hp : 0≤lam^n*(l.map (fun b => b.dominated.bound)).prod :=
    mul_nonneg (pow_nonneg lam_pos.le _) (List.prod_nonneg (by
      intro t ht
      obtain ⟨b,hb,rfl⟩:=List.mem_map.mp ht
      exact b.dominated.bound_nonneg))
  have h:=mul_le_mul_of_nonneg_right
    (mul_le_mul (frame_sqrt_energy_le pre x) (frame_sqrt_energy_le post y) (Real.sqrt_nonneg _)
      (mul_nonneg (frameBound_nonneg pre) (Real.sqrt_nonneg _))) hp
  exact hh.trans (h.trans_eq (by ring))

theorem optional_frame_path_le (pre post : Option StrongRun) (n : ℕ) (hn : 1≤n)
    (l : List CoupledRun) (x y : State → ℝ) :
    x ⬝ᵥ ((frameMatrix pre*carryMatrix^n*(l.map CoupledRun.matrix).prod*frameMatrix post)*ᵥ y) ≤
      Real.sqrt (vectorEnergy x)*Real.sqrt (vectorEnergy y)*
        (frameBound pre*frameBound post*lam^n*(l.map (fun b => b.dominated.bound)).prod) :=
  (optional_frame_path_le_absolute pre post n hn l x y).trans (optional_frame_absolute_le pre post n l x y)

lemma optional_frame_bounds_product (pre post : Option StrongRun) (n : ℕ) (l : List CoupledRun) :
    frameBound pre*frameBound post*lam^n*(l.map (fun b => b.dominated.bound)).prod=
      strongBound^(frameStrongCount pre+frameStrongCount post+(l.map (fun b => b.strong.strongCount)).sum)*
      sigma^(frameRestrictedCount pre+frameRestrictedCount post+(l.map (fun b => b.strong.restrictedCount)).sum)*
      lam^(n+(l.map CoupledRun.carryLength).sum) := by
  rw [coupled_bounds_product,frameBound_eq,frameBound_eq]
  simp only [pow_add]
  ring

end SubmittedGenus.CapFourMass
