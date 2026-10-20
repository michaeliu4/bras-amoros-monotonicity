import Results.Genus.CapFourMass.SpectralMoments
import Results.Genus.CapFourMass.CarryModes
import Results.Genus.FixedPivot.KernelModes

/-!
# Exact rational/symmetric carry-mode convention adapter

The rational rank-one source amplitudes equal the symmetric orthonormal-mode
amplitudes term by term, including the zero-edge boundary convention. Positive
diagonal conjugation and eigenvector scaling therefore commute with absolute
values of complete mode assignments; no numerical eigenvector is assumed.
-/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFourMass
open CapFiveMass.MatrixBounds

lemma real_roots_sum : lam+mu=FixedPivot.carryB radius := by
  simp only [mu,FixedPivot.carryB,carryB]
  ring
lemma real_roots_product : lam*mu=FixedPivot.carryC radius := by
  have hq := lam_quadratic
  unfold mu FixedPivot.carryC carryA carryB at *
  nlinarith

def embedCarry (v : Fin 3 → ℝ) : State → ℝ := ![v 0,v 1,v 2,0]
def sourceHalf (v : Fin 3 → ℝ) : State → ℝ := halfScale (embedCarry v)
def rationalRaw (theta : ℝ) : State → ℝ :=
  sourceHalf (FixedPivot.carryEigenvector radius theta)

lemma weightedDot_eq_half (theta : ℝ) (v : Fin 3 → ℝ) :
    FixedPivot.carryWeightedDot radius theta v = rationalRaw theta ⬝ᵥ sourceHalf v := by
  rw [rationalRaw,sourceHalf,sourceHalf,halfScale_dot]
  norm_num [FixedPivot.carryWeightedDot,FixedPivot.carryEndpointWeight,
    FixedPivot.carryWeight,FixedPivot.carryEigenvector,embedCarry,Fin.sum_univ_succ,Matrix.cons_val_two]

lemma eigenNorm_eq_energy (theta : ℝ) :
    FixedPivot.carryEigenNorm radius theta = vectorEnergy (rationalRaw theta) := by
  rw [vectorEnergy_eq_dot,rationalRaw,sourceHalf,halfScale_dot]
  norm_num [FixedPivot.carryEigenNorm,FixedPivot.carryWeight,FixedPivot.carryEigenvector,
    embedCarry,Fin.sum_univ_succ,Matrix.cons_val_two]
  ring

lemma rationalRaw_plus : rationalRaw lam=plusRaw := by
  unfold rationalRaw sourceHalf embedCarry plusRaw plusVector
  congr 1

lemma rationalRaw_minus : rationalRaw mu=fun i => (carryB/lam)*minusRaw i := by
  have hl : lam ≠ 0 := ne_of_gt lam_pos
  have hp : lam*mu = -carryA*carryB := by
    have h := real_roots_product
    unfold FixedPivot.carryC carryA carryB at *
    nlinarith
  have he : mu=(carryB/lam)*(-carryA) := by
    field_simp
    nlinarith [hp]
  unfold rationalRaw sourceHalf minusRaw halfScale embedCarry FixedPivot.carryEigenvector minusVector
  funext i
  fin_cases i <;> norm_num [FixedPivot.carryB,Matrix.cons_val_two]
  · change halfWeight 0*carryB=carryB/lam*(halfWeight 0*lam)
    field_simp
  · rw [he]
    ring
  · rw [he]
    ring

lemma energy_scale (c : ℝ) (v : State → ℝ) :
    vectorEnergy (fun i => c*v i)=c^2*vectorEnergy v := by
  simp only [vectorEnergy,mul_pow,Finset.mul_sum]

lemma rationalNorm_plus : FixedPivot.carryEigenNorm radius lam=plusNorm := by
  rw [eigenNorm_eq_energy,rationalRaw_plus]
  rfl
lemma rationalNorm_minus : FixedPivot.carryEigenNorm radius mu=(carryB/lam)^2*minusNorm := by
  rw [eigenNorm_eq_energy,rationalRaw_minus,energy_scale]
  rfl

lemma dot_div_right (x y : State → ℝ) (c : ℝ) :
    x ⬝ᵥ (fun i => y i/c)=(x ⬝ᵥ y)/c := by
  simp only [dotProduct,mul_div_assoc,Finset.sum_div]
lemma dot_div_left (x y : State → ℝ) (c : ℝ) :
    (fun i => x i/c) ⬝ᵥ y=(x ⬝ᵥ y)/c := by
  simp only [dotProduct,div_mul_eq_mul_div,Finset.sum_div]

lemma plus_endpoint_product (start finish : Fin 3 → ℝ) :
    (sourceHalf start ⬝ᵥ qplus)*(qplus ⬝ᵥ sourceHalf finish) =
      FixedPivot.carryWeightedDot radius lam start*FixedPivot.carryWeightedDot radius lam finish/
        FixedPivot.carryEigenNorm radius lam := by
  unfold qplus
  rw [dot_div_right,dot_div_left,div_mul_div_comm,← pow_two,Real.sq_sqrt plusNorm_pos.le]
  rw [weightedDot_eq_half,weightedDot_eq_half,rationalRaw_plus,rationalNorm_plus]
  rw [dotProduct_comm (sourceHalf start) plusRaw]

lemma minus_endpoint_product (start finish : Fin 3 → ℝ) :
    (sourceHalf start ⬝ᵥ qminus)*(qminus ⬝ᵥ sourceHalf finish) =
      FixedPivot.carryWeightedDot radius mu start*FixedPivot.carryWeightedDot radius mu finish/
        FixedPivot.carryEigenNorm radius mu := by
  unfold qminus
  rw [dot_div_right,dot_div_left,div_mul_div_comm,← pow_two,Real.sq_sqrt minusNorm_pos.le]
  rw [weightedDot_eq_half,weightedDot_eq_half,rationalRaw_minus,rationalNorm_minus,
    dot_scale_left,dot_scale_left,dotProduct_comm (sourceHalf start) minusRaw]
  have hs : carryB/lam ≠ 0 := div_ne_zero (ne_of_gt carryB_pos) (ne_of_gt lam_pos)
  field_simp [ne_of_gt carryB_pos,ne_of_gt lam_pos,ne_of_gt minusNorm_pos]
  <;> ring

lemma inverse_norm_coefficient (theta other : ℝ)
    (hb : theta+other=FixedPivot.carryB radius) (hc : theta*other=FixedPivot.carryC radius) :
    (FixedPivot.carryB radius)⁻¹*theta⁻¹*(theta-other)⁻¹=
      (FixedPivot.carryEigenNorm radius theta)⁻¹ := by
  rw [FixedPivot.carryEigenNorm_eq radius theta other hb hc,mul_inv_rev,mul_inv_rev]
  ring

/-- Positive amplitude equality is exact for every edge length n, including
n=0 when the source boundary allows that component. -/
theorem rational_positive_amplitude (n : ℕ) (start finish : Fin 3 → ℝ) :
    FixedPivot.weightedModeAmplitude radius lam mu lam⁻¹ (lam-mu)⁻¹ n start finish =
      lam^n*(sourceHalf start ⬝ᵥ qplus)*(qplus ⬝ᵥ sourceHalf finish) := by
  rw [FixedPivot.weightedModeAmplitude_rank_one radius lam mu
    (FixedPivot.carryB radius)⁻¹ lam⁻¹ (lam-mu)⁻¹ real_roots_sum real_roots_product
    (mul_inv_cancel₀ (ne_of_gt carryB_pos)) n start finish,
    inverse_norm_coefficient lam mu real_roots_sum real_roots_product]
  conv_rhs => rw [mul_assoc,plus_endpoint_product]
  ring

/-- Negative amplitude equality, with the exact sign convention -di used by
all rational source progression theorems. -/
theorem rational_negative_amplitude (n : ℕ) (start finish : Fin 3 → ℝ) :
    FixedPivot.weightedModeAmplitude radius mu lam mu⁻¹ (-(lam-mu)⁻¹) n start finish =
      mu^n*(sourceHalf start ⬝ᵥ qminus)*(qminus ⬝ᵥ sourceHalf finish) := by
  have hb : mu+lam=FixedPivot.carryB radius := by rw [add_comm]; exact real_roots_sum
  have hc : mu*lam=FixedPivot.carryC radius := by rw [mul_comm]; exact real_roots_product
  have hdi : -(lam-mu)⁻¹=(mu-lam)⁻¹ := by rw [show mu-lam=-(lam-mu) by ring,inv_neg]
  rw [hdi,FixedPivot.weightedModeAmplitude_rank_one radius mu lam
    (FixedPivot.carryB radius)⁻¹ mu⁻¹ (mu-lam)⁻¹ hb hc
    (mul_inv_cancel₀ (ne_of_gt carryB_pos)) n start finish,
    inverse_norm_coefficient mu lam hb hc]
  conv_rhs => rw [mul_assoc,minus_endpoint_product]
  ring

end SubmittedGenus.CapFourMass
