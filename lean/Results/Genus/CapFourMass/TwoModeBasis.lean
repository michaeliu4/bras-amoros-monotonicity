import Results.Genus.CapFourMass.CarryModes

/-! A normalized eigenvector in either simple nonzero eigenspace of an exact
two-mode real transfer is a unit scalar multiple of its canonical vector.
Consequently complete projected absolute entries do not depend on signs. -/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.TwoModeBasis
open CapFourMass CapFiveMass.MatrixBounds

lemma unit_eigenvector_multiple (C : Matrix State State ℝ) (u v w : State→ℝ)
    (a b : ℝ) (ha : a≠0) (hab : a≠b)
    (hu : vectorEnergy u=1) (hv : vectorEnergy v=1) (huv : u ⬝ᵥ v=0)
    (hw : vectorEnergy w=1)
    (hC : ∀ x,C*ᵥ x=fun i => a*(u ⬝ᵥ x)*u i+b*(v ⬝ᵥ x)*v i)
    (hwe : C*ᵥ w=fun i => a*w i) :
    ∃ s : ℝ,|s|=1 ∧ w=fun i => s*u i := by
  have hvu : v ⬝ᵥ u=0 := by rw [dotProduct_comm,huv]
  have hvv : v ⬝ᵥ v=1 := by rw [←vectorEnergy_eq_dot,hv]
  have he := (hC w).symm.trans hwe
  have hd := congrArg (fun x : State→ℝ => v ⬝ᵥ x) he
  simp only [dot_add_right,dot_scale_right,hvu,hvv,mul_zero,mul_one,zero_add] at hd
  have hz : (b-a)*(v ⬝ᵥ w)=0 := by nlinarith [hd]
  have hvw : v ⬝ᵥ w=0 := (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hab.symm)
  have hwrep : w=fun i => (u ⬝ᵥ w)*u i := by
    funext i
    have hi:=congrFun he i
    simp only [hvw,mul_zero,zero_mul,add_zero] at hi
    exact mul_left_cancel₀ ha (by simpa only [mul_assoc] using hi.symm)
  have henergy : vectorEnergy w=(u ⬝ᵥ w)^2 := by
    conv_lhs => rw [hwrep]
    simp only [vectorEnergy,mul_pow,←Finset.mul_sum]
    change (u ⬝ᵥ w)^2*vectorEnergy u=(u ⬝ᵥ w)^2
    rw [hu,mul_one]
  refine ⟨u ⬝ᵥ w,?_,hwrep⟩
  have hs := sq_abs (u ⬝ᵥ w)
  have hn := abs_nonneg (u ⬝ᵥ w)
  nlinarith

lemma projected_entry_abs_invariant (A : Matrix State State ℝ)
    (u v x y : State→ℝ) (s t : ℝ) (hs : |s|=1) (ht : |t|=1)
    (hx : x=fun i => s*u i) (hy : y=fun i => t*v i) :
    |x ⬝ᵥ (A*ᵥ y)|=|u ⬝ᵥ (A*ᵥ v)| := by
  rw [hx,hy,matrix_mulVec_scale,dot_scale_left,dot_scale_right]
  simp only [abs_mul,hs,ht,one_mul]

lemma coupled_entry_abs_invariant (A : Matrix State State ℝ)
    (u v x y : State→ℝ) (s t a : ℝ) (hs : |s|=1) (ht : |t|=1)
    (hx : x=fun i => s*u i) (hy : y=fun i => t*v i) :
    |(x ⬝ᵥ (A*ᵥ y))*a|=|(u ⬝ᵥ (A*ᵥ v))*a| := by
  rw [abs_mul,abs_mul,projected_entry_abs_invariant A u v x y s t hs ht hx hy]

end SubmittedGenus.TwoModeBasis
