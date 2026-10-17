import Results.Genus.CapFourMass.BlockProducts

/-! Actual alphabet/loop boundaries, carry projections, and boundary-only components. -/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFourMass
open CapFiveMass.MatrixBounds

def alphabetMass : ℝ := ∑ i : State, radius^(i.val+1)
def loopMass : ℝ := radius^2+radius^3+radius^4

def endpoint (cap : ℕ) (loop : Bool) : State → ℝ := fun i =>
  if i.val+1 ≤ cap ∧ (loop=true → 2 ≤ i.val+1) then halfWeight i else 0

lemma alphabetMass_gt_one : 1 < alphabetMass := by
  norm_num [alphabetMass,radius,Fin.sum_univ_succ]
lemma loopMass_lt_one : loopMass < 1 := by norm_num [loopMass,radius]
lemma loopMass_nonneg : 0 ≤ loopMass := by norm_num [loopMass,radius]

lemma endpoint_energy_free (cap : ℕ) (loop : Bool) : vectorEnergy (endpoint cap loop) ≤ alphabetMass := by
  apply Finset.sum_le_sum
  intro i _
  unfold endpoint
  split_ifs
  · exact (halfWeight_sq i).le
  · simp only [zero_pow (by decide : 2≠0)]
    exact pow_nonneg radius_pos.le _

lemma endpoint_energy_loop (cap : ℕ) : vectorEnergy (endpoint cap true) ≤ loopMass := by
  have h : vectorEnergy (endpoint cap true) ≤
      ∑ i : State, if 2 ≤ i.val+1 then radius^(i.val+1) else 0 := by
    apply Finset.sum_le_sum
    intro i _
    unfold endpoint
    split_ifs with hgate hhigh
    · exact (halfWeight_sq i).le
    · simp at hgate
      omega
    · simpa using pow_nonneg radius_pos.le (i.val+1)
    · simp
  have hs : (∑ i : State, if 2 ≤ i.val+1 then radius^(i.val+1) else 0) = loopMass := by
    norm_num [Fin.sum_univ_succ,loopMass]
    ring
  exact h.trans_eq hs

/-- An arbitrary endpoint alphabet mask is a Euclidean contraction. -/
lemma mask_energy_le (allowed : State → Prop) [DecidablePred allowed] (x : State → ℝ) :
    vectorEnergy (fun i => if allowed i then x i else 0) ≤ vectorEnergy x := by
  apply Finset.sum_le_sum
  intro i _
  dsimp only
  split_ifs
  · rfl
  · simp only [zero_pow (by decide : 2≠0)]
    exact sq_nonneg _

def modeBoundary (x : State → ℝ) : Mode → ℝ := fun j => |modeVector j ⬝ᵥ x|
lemma modeBoundary_energy (x : State → ℝ) : vectorEnergy (modeBoundary x) ≤ vectorEnergy x := by
  simpa [vectorEnergy,modeBoundary,modeVector,Fin.sum_univ_succ,sq_abs] using two_mode_bessel x

lemma strong_prefix_energy (k : ℕ) (x : State → ℝ) :
    vectorEnergy (modeBoundary ((strongMatrix^k) *ᵥ x)) ≤ strongBound^(2*k)*vectorEnergy x :=
  (modeBoundary_energy _).trans (strong_power_energy_le k x)
lemma restricted_prefix_energy (x : State → ℝ) :
    vectorEnergy (modeBoundary (restrictedMatrix *ᵥ x)) ≤ restrictedBound^2*vectorEnergy x :=
  (modeBoundary_energy _).trans (restricted_energy_le x)

lemma modeRoot_power_abs_le (n : ℕ) (j : Mode) : |(modeRoot j)^n| ≤ lam^n := by
  have hm : |mu| ≤ lam := mu_abs_le.trans (by nlinarith [lam_pos])
  fin_cases j
  · norm_num [modeRoot,abs_of_pos (pow_pos lam_pos n)]
  · simpa [modeRoot,abs_pow] using pow_le_pow_left₀ (abs_nonneg mu) hm n

def carryBoundary (n : ℕ) (x : State → ℝ) : Mode → ℝ := fun j =>
  |(modeRoot j)^n*(modeVector j ⬝ᵥ x)|

lemma carryBoundary_energy (n : ℕ) (x : State → ℝ) :
    vectorEnergy (carryBoundary n x) ≤ lam^(2*n)*vectorEnergy x := by
  calc
    vectorEnergy (carryBoundary n x) ≤ lam^(2*n)*vectorEnergy (modeBoundary x) := by
      simp only [vectorEnergy,Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      have h := mul_le_mul_of_nonneg_right (modeRoot_power_abs_le n j)
        (abs_nonneg (modeVector j ⬝ᵥ x))
      have hh := pow_le_pow_left₀ (by positivity : 0 ≤ |(modeRoot j)^n| * |modeVector j ⬝ᵥ x|) h 2
      simpa only [carryBoundary,modeBoundary,abs_mul,mul_pow,← pow_mul,Nat.mul_comm] using hh
    _ ≤ lam^(2*n)*vectorEnergy x := mul_le_mul_of_nonneg_left
      (modeBoundary_energy x) (pow_nonneg lam_pos.le _)

def carryAbsolute (n : ℕ) (x y : State → ℝ) : ℝ :=
  ∑ j : Mode, |(x ⬝ᵥ modeVector j)*(modeRoot j)^n*(modeVector j ⬝ᵥ y)|

/-- Entire pure-carry components are controlled at length zero as well.
This is kept separate from the strong/carry block estimate, which needs n≥1. -/
theorem carryAbsolute_le (n : ℕ) (x y : State → ℝ) :
    carryAbsolute n x y ≤ Real.sqrt (vectorEnergy x)*Real.sqrt (vectorEnergy y)*lam^n := by
  calc
    carryAbsolute n x y ≤ lam^n*
        (|(x ⬝ᵥ qplus)*(qplus ⬝ᵥ y)|+|(x ⬝ᵥ qminus)*(qminus ⬝ᵥ y)|) := by
      have hs : lam^n*(|(x ⬝ᵥ qplus)*(qplus ⬝ᵥ y)|+|(x ⬝ᵥ qminus)*(qminus ⬝ᵥ y)|) =
          ∑ j : Mode, |x ⬝ᵥ modeVector j| * lam^n*|modeVector j ⬝ᵥ y| := by
        norm_num [modeVector,Fin.sum_univ_succ,abs_mul]
        ring
      rw [hs]
      apply Finset.sum_le_sum
      intro j _
      simp only [abs_mul]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (modeRoot_power_abs_le n j) (abs_nonneg _)) (abs_nonneg _)
    _ ≤ lam^n*(Real.sqrt (vectorEnergy x)*Real.sqrt (vectorEnergy y)) :=
      mul_le_mul_of_nonneg_left (absolute_two_mode_boundary_le x y) (pow_nonneg lam_pos.le _)
    _ = _ := by ring

/-- Exact source identity behind the preceding pure-carry bound. -/
lemma carrySource_eq_modes (n : ℕ) (x y : State → ℝ) :
    x ⬝ᵥ ((carryMatrix^(n+1)) *ᵥ y) =
      ∑ j : Mode, (x ⬝ᵥ modeVector j)*(modeRoot j)^(n+1)*(modeVector j ⬝ᵥ y) := by
  rw [carry_power_modes,dot_add_right,dot_scale_right,dot_scale_right]
  norm_num [modeVector,modeRoot,Fin.sum_univ_succ]
  ring

theorem carrySource_le_absolute (n : ℕ) (x y : State → ℝ) :
    x ⬝ᵥ ((carryMatrix^(n+1)) *ᵥ y) ≤ carryAbsolute (n+1) x y := by
  rw [carrySource_eq_modes]
  exact Finset.sum_le_sum fun j _ => le_abs_self _

end SubmittedGenus.CapFourMass
