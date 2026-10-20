import Results.Genus.CapFourMass.GadgetCoordinates

namespace SubmittedGenus.CapFourMass.GadgetLocalSums
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

private def tuple3Equiv (S : Type*) : (Fin 3 → S) ≃ S × S × S where
  toFun x := (x 0,x 1,x 2)
  invFun x := ![x.1,x.2.1,x.2.2]
  left_inv x := by funext i; fin_cases i <;> rfl
  right_inv x := by rcases x with ⟨a,b,c⟩; rfl

private def tuple4Equiv (S : Type*) : (Fin 4 → S) ≃ S × S × S × S where
  toFun x := (x 0,x 1,x 2,x 3)
  invFun x := ![x.1,x.2.1,x.2.2.1,x.2.2.2]
  left_inv x := by funext i; fin_cases i <;> rfl
  right_inv x := by rcases x with ⟨a,b,c,d⟩; rfl

lemma sum_three {S : Type*} [Fintype S] (f : (Fin 3 → S) → ℝ) :
    (∑ x, f x) = ∑ a, ∑ b, ∑ c, f ![a,b,c] := by
  rw [Fintype.sum_equiv (tuple3Equiv S) f (fun t => f ![t.1,t.2.1,t.2.2])
    (by intro x; congr 1; funext i; fin_cases i <;> rfl)]
  simp only [Fintype.sum_prod_type]

lemma sum_four {S : Type*} [Fintype S] (f : (Fin 4 → S) → ℝ) :
    (∑ x, f x) = ∑ a, ∑ b, ∑ c, ∑ d, f ![a,b,c,d] := by
  rw [Fintype.sum_equiv (tuple4Equiv S) f (fun t => f ![t.1,t.2.1,t.2.2.1,t.2.2.2])
    (by intro x; congr 1; funext i; fin_cases i <;> rfl)]
  simp only [Fintype.sum_prod_type]

def letter (x : Fin 5) : ℕ := x.val

def weight {n : ℕ} (z : ℝ) (x : Fin n → Fin 5) : ℝ := ∏ j, z^letter (x j)

def alphabet {n : ℕ} (x : Fin n → Fin 5) : Prop := ∀ j, 1 ≤ letter (x j) ∧ letter (x j) ≤ 3

def allowedThree (x : Fin 3 → Fin 5) : Prop :=
  alphabet x ∧ 3 ≤ letter (x 0)+letter (x 1) ∧ 3 ≤ letter (x 0)+letter (x 2)

def allowedFour (x : Fin 4 → Fin 5) : Prop :=
  alphabet x ∧ 3 ≤ letter (x 0)+letter (x 2) ∧ 3 ≤ letter (x 0)+letter (x 3)

def failureFour (x : Fin 4 → Fin 5) : Prop :=
  letter (x 0)=1 ∧ letter (x 1)=3 ∧
  (2 ≤ letter (x 2) ∧ letter (x 2) ≤ 3) ∧ (2 ≤ letter (x 3) ∧ letter (x 3) ≤ 3)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
lemma allowedThree_sum (z : ℝ) :
    (∑ x : Fin 3 → Fin 5, if allowedThree x then weight z x else 0) =
      LocalWeights.starWeight z := by
  rw [sum_three, LocalWeights.starWeight_eq]
  norm_num [allowedThree,alphabet,weight,letter,Fin.forall_fin_succ,
    Fin.sum_univ_succ,Fin.prod_univ_succ,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail,LocalWeights.a,LocalWeights.b,LocalWeights.s]
  ring

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
lemma allowedFour_sum (z : ℝ) :
    (∑ x : Fin 4 → Fin 5, if allowedFour x then weight z x else 0) =
      LocalWeights.s z * LocalWeights.starWeight z := by
  rw [sum_four, LocalWeights.starWeight_eq]
  norm_num [allowedFour,alphabet,weight,letter,Fin.forall_fin_succ,
    Fin.sum_univ_succ,Fin.prod_univ_succ,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail,LocalWeights.a,LocalWeights.b,LocalWeights.s]
  ring

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
lemma failureFour_sum (z : ℝ) :
    (∑ x : Fin 4 → Fin 5, if failureFour x then weight z x else 0) =
      z*z^3*(LocalWeights.b z)^2 := by
  rw [sum_four]
  norm_num [failureFour,weight,letter,Fin.sum_univ_succ,Fin.prod_univ_succ,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail,LocalWeights.b]
  ring

def failureThreeLeft (x : Fin 3 → Fin 5) : Prop :=
  letter (x 0)=1 ∧ letter (x 1)=3 ∧ 2 ≤ letter (x 2) ∧ letter (x 2) ≤ 3

def failureThreeRight (x : Fin 3 → Fin 5) : Prop :=
  letter (x 0)=1 ∧ letter (x 2)=3 ∧ 2 ≤ letter (x 1) ∧ letter (x 1) ≤ 3

def postponedFour (x : Fin 4 → Fin 5) : Prop := x = ![1,3,2,2]
def postponedThreeLeft (x : Fin 3 → Fin 5) : Prop := x = ![1,3,2]
def postponedThreeRight (x : Fin 3 → Fin 5) : Prop := x = ![1,2,3]

set_option maxRecDepth 4096 in
lemma failureThreeLeft_sum (z : ℝ) :
    (∑ x : Fin 3 → Fin 5, if failureThreeLeft x then weight z x else 0) =
      z*z^3*LocalWeights.b z := by
  rw [sum_three]
  norm_num [failureThreeLeft,weight,letter,Fin.sum_univ_succ,Fin.prod_univ_succ,
    Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,LocalWeights.b]
  ring

set_option maxRecDepth 4096 in
lemma failureThreeRight_sum (z : ℝ) :
    (∑ x : Fin 3 → Fin 5, if failureThreeRight x then weight z x else 0) =
      z*z^3*LocalWeights.b z := by
  rw [sum_three]
  norm_num [failureThreeRight,weight,letter,Fin.sum_univ_succ,Fin.prod_univ_succ,
    Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,LocalWeights.b]
  ring

lemma postponedFour_sum (z : ℝ) :
    (∑ x : Fin 4 → Fin 5, if postponedFour x then weight z x else 0) = z^8 := by
  simp [postponedFour,weight,letter,Fin.prod_univ_succ]
  ring

lemma postponedThreeLeft_sum (z : ℝ) :
    (∑ x : Fin 3 → Fin 5, if postponedThreeLeft x then weight z x else 0) = z^6 := by
  simp [postponedThreeLeft,weight,letter,Fin.prod_univ_succ]
  ring

lemma postponedThreeRight_sum (z : ℝ) :
    (∑ x : Fin 3 → Fin 5, if postponedThreeRight x then weight z x else 0) = z^6 := by
  simp [postponedThreeRight,weight,letter,Fin.prod_univ_succ]
  ring

lemma four_density {z : ℝ} (hz : 0 < z) :
    LocalWeights.epsilon z *
      (∑ x : Fin 4 → Fin 5, if allowedFour x then weight z x else 0) ≤
      ∑ x : Fin 4 → Fin 5, if failureFour x then weight z x else 0 := by
  rw [allowedFour_sum,failureFour_sum]
  have h := LocalWeights.four_failure_ratio hz
  rw [LocalWeights.highWeight_eq] at h
  have hp := mul_pos (LocalWeights.s_pos hz) (LocalWeights.starWeight_pos hz)
  exact le_of_eq ((div_eq_iff (ne_of_gt hp)).mp h).symm

lemma three_left_density {z : ℝ} (hz : 0 < z) :
    LocalWeights.epsilon z *
      (∑ x : Fin 3 → Fin 5, if allowedThree x then weight z x else 0) ≤
      ∑ x : Fin 3 → Fin 5, if failureThreeLeft x then weight z x else 0 := by
  rw [allowedThree_sum,failureThreeLeft_sum]
  have h := LocalWeights.shared_failure_ratio_ge hz
  rw [LocalWeights.highWeight_eq] at h
  exact (le_div_iff₀ (LocalWeights.starWeight_pos hz)).mp h

lemma three_right_density {z : ℝ} (hz : 0 < z) :
    LocalWeights.epsilon z *
      (∑ x : Fin 3 → Fin 5, if allowedThree x then weight z x else 0) ≤
      ∑ x : Fin 3 → Fin 5, if failureThreeRight x then weight z x else 0 := by
  simpa only [failureThreeLeft_sum,failureThreeRight_sum] using three_left_density hz

lemma postponed_four_density {z : ℝ} (hz : 0 < z) :
    LocalWeights.delta z *
      (∑ x : Fin 4 → Fin 5, if allowedFour x then weight z x else 0) ≤
      ∑ x : Fin 4 → Fin 5, if postponedFour x then weight z x else 0 := by
  rw [allowedFour_sum,postponedFour_sum]
  have h := LocalWeights.postponed_four_ratio hz
  have hp := mul_pos (LocalWeights.s_pos hz) (LocalWeights.starWeight_pos hz)
  exact le_of_eq ((div_eq_iff (ne_of_gt hp)).mp h).symm

lemma postponed_three_left_density {z : ℝ} (hz : 0 < z) :
    LocalWeights.delta z *
      (∑ x : Fin 3 → Fin 5, if allowedThree x then weight z x else 0) ≤
      ∑ x : Fin 3 → Fin 5, if postponedThreeLeft x then weight z x else 0 := by
  rw [allowedThree_sum,postponedThreeLeft_sum]
  exact (le_div_iff₀ (LocalWeights.starWeight_pos hz)).mp
    (LocalWeights.postponed_shared_ratio_ge hz)

lemma postponed_three_right_density {z : ℝ} (hz : 0 < z) :
    LocalWeights.delta z *
      (∑ x : Fin 3 → Fin 5, if allowedThree x then weight z x else 0) ≤
      ∑ x : Fin 3 → Fin 5, if postponedThreeRight x then weight z x else 0 := by
  simpa only [postponedThreeLeft_sum,postponedThreeRight_sum] using
    postponed_three_left_density hz

end
end SubmittedGenus.CapFourMass.GadgetLocalSums
