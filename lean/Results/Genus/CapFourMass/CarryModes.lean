import Results.Genus.CapFourMass.CarrySpectrum

/-! Source eigenvector identities, two-mode carry powers, and zero-edge corner. -/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFourMass
open CapFiveMass.MatrixBounds

lemma carry_symmetric : carryMatrix.transpose=carryMatrix := transfer_symmetric 3 3

lemma plusVector_eigen : rationalTransfer 3 3 *ᵥ plusVector = fun i => lam*plusVector i := by
  have hq := lam_quadratic
  norm_num [carryA,carryB,radius] at hq
  funext i
  fin_cases i <;> norm_num [rationalTransfer,gate,Matrix.mulVec,dotProduct,
    plusVector,carryA,carryB,radius,Fin.sum_univ_succ] <;> nlinarith

lemma minusVector_eigen : rationalTransfer 3 3 *ᵥ minusVector = fun i => mu*minusVector i := by
  have hq := lam_quadratic
  norm_num [carryA,carryB,radius] at hq
  funext i
  fin_cases i <;> norm_num [rationalTransfer,gate,Matrix.mulVec,dotProduct,
    minusVector,carryA,carryB,radius,mu,Fin.sum_univ_succ] <;> nlinarith

lemma halfScale_scale (c : ℝ) (v : State → ℝ) :
    halfScale (fun i => c*v i) = fun i => c*halfScale v i := by
  funext i
  simp only [halfScale]
  ring

lemma plusRaw_eigen : carryMatrix *ᵥ plusRaw = fun i => lam*plusRaw i := by
  rw [plusRaw,carryMatrix,transfer_halfScale,plusVector_eigen,halfScale_scale]
lemma minusRaw_eigen : carryMatrix *ᵥ minusRaw = fun i => mu*minusRaw i := by
  rw [minusRaw,carryMatrix,transfer_halfScale,minusVector_eigen,halfScale_scale]

lemma matrix_mulVec_div (A : Matrix State State ℝ) (v : State → ℝ) (c : ℝ) :
    A *ᵥ (fun i => v i/c) = fun i => (A *ᵥ v) i/c := by
  funext i
  simp only [Matrix.mulVec,dotProduct,mul_div_assoc,Finset.sum_div]

lemma qplus_eigen : carryMatrix *ᵥ qplus = fun i => lam*qplus i := by
  unfold qplus
  rw [matrix_mulVec_div,plusRaw_eigen]
  funext i
  simp only
  ring
lemma qminus_eigen : carryMatrix *ᵥ qminus = fun i => mu*qminus i := by
  unfold qminus
  rw [matrix_mulVec_div,minusRaw_eigen]
  funext i
  simp only
  ring

lemma dot_add_right (v x y : State → ℝ) :
    v ⬝ᵥ (fun i => x i+y i) = v ⬝ᵥ x+v ⬝ᵥ y := by
  simp only [dotProduct,mul_add,Finset.sum_add_distrib]
lemma dot_scale_right (c : ℝ) (v w : State → ℝ) :
    v ⬝ᵥ (fun i => c*w i) = c*(v ⬝ᵥ w) := by
  simp only [dotProduct,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring
lemma dot_scale_left (c : ℝ) (v w : State → ℝ) :
    (fun i => c*v i) ⬝ᵥ w = c*(v ⬝ᵥ w) := by
  simp only [dotProduct,Finset.mul_sum,mul_assoc]
lemma dot_comm (v w : State → ℝ) : v ⬝ᵥ w = w ⬝ᵥ v := dotProduct_comm _ _
lemma qplus_self : qplus ⬝ᵥ qplus = 1 := by rw [← vectorEnergy_eq_dot,qplus_energy]
lemma qminus_self : qminus ⬝ᵥ qminus = 1 := by rw [← vectorEnergy_eq_dot,qminus_energy]
lemma qminus_qplus : qminus ⬝ᵥ qplus = 0 := by rw [dot_comm,qplus_qminus]

/-- Any vector in the actual two-dimensional carry image has its two-mode
orthogonal expansion, including the ordinary-edge-length-zero boundaries. -/
lemma span_modes (v : State → ℝ) (a b : ℝ)
    (hv : v = fun i => a*qplus i+b*qminus i) :
    v = fun i => (qplus ⬝ᵥ v)*qplus i+(qminus ⬝ᵥ v)*qminus i := by
  conv_rhs => rw [hv]
  simp only [dot_add_right,dot_scale_right,qplus_self,qminus_self,
    qplus_qminus,qminus_qplus,mul_one,mul_zero,add_zero,zero_add]
  exact hv

/-- Solve the actual carry-image coordinates in the two raw eigenvectors. -/
lemma halfScale_span (v : State → ℝ) (h23 : v 2=v 1) (h4 : v 3=0) :
    ∃ a b : ℝ, halfScale v = fun i => a*qplus i+b*qminus i := by
  let s := lam^2+carryA*carryB
  have hs : s ≠ 0 := by
    dsimp [s]
    have := carryA_pos
    have := carryB_pos
    positivity
  refine ⟨((carryA*v 0+lam*v 1)/s)*Real.sqrt plusNorm,
    ((lam*v 0-carryB*v 1)/s)*Real.sqrt minusNorm, ?_⟩
  have hp := ne_of_gt (Real.sqrt_pos.mpr plusNorm_pos)
  have hm := ne_of_gt (Real.sqrt_pos.mpr minusNorm_pos)
  funext i
  simp only [qplus,qminus,plusRaw,minusRaw,halfScale]
  field_simp [hp,hm]
  fin_cases i <;> simp [plusVector,minusVector,h23,h4] <;>
    field_simp [hs] <;> dsimp [s] <;> ring

def freeBoundary : State → ℝ := halfScale ![1,1,1,0]
def loopBoundary : State → ℝ := halfScale ![0,1,1,0]

lemma loopBoundary_modes : loopBoundary = fun i =>
    (qplus ⬝ᵥ loopBoundary)*qplus i+(qminus ⬝ᵥ loopBoundary)*qminus i := by
  obtain ⟨a,b,h⟩ := halfScale_span (![0,1,1,0] : State → ℝ) rfl rfl
  exact span_modes loopBoundary a b h

/-- The exact zero-edge convention in the submitted manuscript. -/
theorem zero_edge_split : freeBoundary ⬝ᵥ loopBoundary =
    (freeBoundary ⬝ᵥ qplus)*(qplus ⬝ᵥ loopBoundary)+
    (freeBoundary ⬝ᵥ qminus)*(qminus ⬝ᵥ loopBoundary) := by
  conv_lhs => rw [loopBoundary_modes]
  rw [dot_add_right,dot_scale_right,dot_scale_right]
  ring

theorem zero_edge_source : freeBoundary ⬝ᵥ loopBoundary = radius^2+radius^3 := by
  rw [freeBoundary,loopBoundary,halfScale_dot]
  norm_num [Fin.sum_univ_succ]

lemma halfScale_unscale (v : State → ℝ) :
    halfScale (fun i => v i/halfWeight i) = v := by
  funext i
  dsimp [halfScale]
  field_simp [ne_of_gt (halfWeight_pos i)]

lemma carry_image_span (v : State → ℝ) :
    ∃ a b : ℝ, carryMatrix *ᵥ v = fun i => a*qplus i+b*qminus i := by
  have h1 : halfWeight 1 ≠ 0 := ne_of_gt (halfWeight_pos 1)
  have h2 : halfWeight 2 ≠ 0 := ne_of_gt (halfWeight_pos 2)
  have hrow : (carryMatrix *ᵥ v) 2/halfWeight 2 =
      (carryMatrix *ᵥ v) 1/halfWeight 1 := by
    norm_num [carryMatrix,transfer,gate,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
    field_simp
    <;> ring
  have hzero : (carryMatrix *ᵥ v) 3/halfWeight 3 = 0 := by
    norm_num [carryMatrix,transfer,gate,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  have h := halfScale_span (fun i => (carryMatrix *ᵥ v) i/halfWeight i) hrow hzero
  rw [halfScale_unscale] at h
  exact h

lemma qplus_carry_dot (v : State → ℝ) :
    qplus ⬝ᵥ (carryMatrix *ᵥ v) = lam*(qplus ⬝ᵥ v) := by
  have h := Matrix.dotProduct_transpose_mulVec carryMatrix qplus v
  rw [carry_symmetric] at h
  rw [h,qplus_eigen,dot_scale_right,dot_comm]
lemma qminus_carry_dot (v : State → ℝ) :
    qminus ⬝ᵥ (carryMatrix *ᵥ v) = mu*(qminus ⬝ᵥ v) := by
  have h := Matrix.dotProduct_transpose_mulVec carryMatrix qminus v
  rw [carry_symmetric] at h
  rw [h,qminus_eigen,dot_scale_right,dot_comm]

lemma carry_modes (v : State → ℝ) : carryMatrix *ᵥ v = fun i =>
    lam*(qplus ⬝ᵥ v)*qplus i+mu*(qminus ⬝ᵥ v)*qminus i := by
  obtain ⟨a,b,hv⟩ := carry_image_span v
  have h := span_modes (carryMatrix *ᵥ v) a b hv
  simpa only [qplus_carry_dot,qminus_carry_dot] using h

lemma matrix_mulVec_add (A : Matrix State State ℝ) (v w : State → ℝ) :
    A *ᵥ (fun i => v i+w i) = fun i => (A *ᵥ v) i+(A *ᵥ w) i := by
  funext i
  simp only [Matrix.mulVec,dotProduct,mul_add,Finset.sum_add_distrib]
lemma matrix_mulVec_scale (A : Matrix State State ℝ) (c : ℝ) (v : State → ℝ) :
    A *ᵥ (fun i => c*v i) = fun i => c*(A *ᵥ v) i := by
  funext i
  simp only [Matrix.mulVec,dotProduct,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The complete genuine carry transfer has exactly these two modes after
one edge, not just on an assumed invariant source subspace. -/
theorem carry_power_modes (n : ℕ) (v : State → ℝ) :
    (carryMatrix^(n+1)) *ᵥ v = fun i =>
      lam^(n+1)*(qplus ⬝ᵥ v)*qplus i+mu^(n+1)*(qminus ⬝ᵥ v)*qminus i := by
  induction n with
  | zero => simpa only [Nat.zero_add,pow_one] using carry_modes v
  | succ n ih =>
    rw [pow_succ',← Matrix.mulVec_mulVec,ih,matrix_mulVec_add,
      matrix_mulVec_scale,matrix_mulVec_scale,qplus_eigen,qminus_eigen]
    funext i
    simp only [pow_succ]
    ring

lemma projection_residual_energy (x : State → ℝ) (a b : ℝ) :
    vectorEnergy (fun i => x i-a*qplus i-b*qminus i) =
      vectorEnergy x+a^2+b^2-2*a*(qplus ⬝ᵥ x)-2*b*(qminus ⬝ᵥ x) := by
  have he : vectorEnergy (fun i => x i-a*qplus i-b*qminus i) =
      vectorEnergy x+a^2*vectorEnergy qplus+b^2*vectorEnergy qminus-
      2*a*(qplus ⬝ᵥ x)-2*b*(qminus ⬝ᵥ x)+2*a*b*(qplus ⬝ᵥ qminus) := by
    simp only [vectorEnergy,dotProduct,Finset.mul_sum,← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simpa only [qplus_energy,qminus_energy,qplus_qminus,mul_one,mul_zero,add_zero] using he

lemma two_mode_bessel (x : State → ℝ) :
    (qplus ⬝ᵥ x)^2+(qminus ⬝ᵥ x)^2 ≤ vectorEnergy x := by
  have h := vectorEnergy_nonneg (fun i => x i-(qplus ⬝ᵥ x)*qplus i-(qminus ⬝ᵥ x)*qminus i)
  rw [projection_residual_energy] at h
  nlinarith

/-- Absolute mode summation is contractive at every pair of boundaries.
This includes the otherwise exceptional zero-ordinary-edge carry loop. -/
theorem absolute_two_mode_boundary_le (x y : State → ℝ) :
    |(x ⬝ᵥ qplus)*(qplus ⬝ᵥ y)|+|(x ⬝ᵥ qminus)*(qminus ⬝ᵥ y)| ≤
      Real.sqrt (vectorEnergy x)*Real.sqrt (vectorEnergy y) := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 2))
    (![|qplus ⬝ᵥ x|,|qminus ⬝ᵥ x|]) (![|qplus ⬝ᵥ y|,|qminus ⬝ᵥ y|])
  norm_num [Fin.sum_univ_succ,sq_abs] at hc
  have hb := mul_le_mul (two_mode_bessel x) (two_mode_bessel y)
    (by positivity) (vectorEnergy_nonneg x)
  apply (sq_le_sq₀ (by positivity) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
  rw [mul_pow,Real.sq_sqrt (vectorEnergy_nonneg x),Real.sq_sqrt (vectorEnergy_nonneg y)]
  simp only [abs_mul,dot_comm x] at *
  exact hc.trans hb

end SubmittedGenus.CapFourMass
