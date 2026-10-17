import Results.Genus.CapFiveMass.Geometric
import Mathlib.Tactic.FieldSimp

/-!
# Scalar incidence compression, including the smallest pivot pair

The strong-incidence lower bound is expressed without truncated natural
subtraction: 2*i+j ≤ v+1. This includes r=1,p=2, where the manuscript
exponent r+p-4 is the integer -1.
-/

noncomputable section
namespace SubmittedGenus.CapFiveMass

private lemma factor_normalize {s a b : ℝ} (hb : b ≠ 0) (u v w : ℕ) :
    s ^ u * a ^ v * b ^ w = b ^ (u + v + w) * (s / b) ^ u * (a / b) ^ v := by
  simp only [pow_add, div_pow]
  field_simp

private lemma target_normalize {s a b x : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hx : x ≠ 0)
    (hxsq : x ^ 2 = a * b) (i j l : ℕ) :
    (s / x * a ^ i * x ^ j * b ^ l) ^ 2 * (a / b) =
      b ^ (2 * (i + j + l)) * (s / b) ^ 2 * (a / b) ^ (2 * i + j) := by
  have hp : (x ^ j) ^ 2 = (a * b) ^ j := by
    rw [← pow_mul, Nat.mul_comm j 2, pow_mul, hxsq]
  simp only [mul_pow, div_pow, hp, hxsq, pow_add, pow_mul]
  field_simp [ha]
  ring

/-- Compression of the squared component product into the exact per-pivot
geometric monomial. u counts free incidences, v=2S+L5, w=2C+L4. -/
lemma incidence_square_compression {s a b x : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hbs : b ≤ s) (hx : 0 < x) (hxsq : x ^ 2 = a * b)
    (u v w i j l : ℕ) (hu : u ≤ 2) (hstrong : 2 * i + j ≤ v + 1)
    (htotal : u + v + w = 2 * (i + j + l)) :
    s ^ u * a ^ v * b ^ w ≤ (s / x * a ^ i * x ^ j * b ^ l) ^ 2 := by
  have hb : 0 < b := ha.trans_le hab
  have hs : 0 < s := hb.trans_le hbs
  have hratio : 0 < a / b := div_pos ha hb
  have hratio1 : a / b ≤ 1 := (div_le_one hb).mpr hab
  have hsratio : 1 ≤ s / b := (one_le_div hb).mpr hbs
  have hu' : (s / b) ^ u ≤ (s / b) ^ 2 := pow_le_pow_right₀ hsratio hu
  have hv' : (a / b) ^ (v + 1) ≤ (a / b) ^ (2 * i + j) :=
    pow_le_pow_of_le_one hratio.le hratio1 hstrong
  have hnorm := factor_normalize (s := s) (a := a) hb.ne' u v w
  rw [htotal] at hnorm
  apply le_of_mul_le_mul_right (a := a / b) ?_ hratio
  rw [hnorm, target_normalize ha.ne' hb.ne' hx.ne' hxsq]
  calc
    b ^ (2 * (i + j + l)) * (s / b) ^ u * (a / b) ^ v * (a / b) =
        b ^ (2 * (i + j + l)) * (s / b) ^ u * (a / b) ^ (v + 1) := by rw [pow_succ]; ring
    _ ≤ b ^ (2 * (i + j + l)) * (s / b) ^ 2 * (a / b) ^ (2 * i + j) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hu' (pow_nonneg hb.le _)) hv'
        (pow_nonneg hratio.le _) (mul_nonneg (pow_nonneg hb.le _) (sq_nonneg _))

/-- Unsquared form used after multiplying path and cycle contractions. -/
lemma incidence_compression {W s a b x : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hbs : b ≤ s) (hx : 0 < x) (hxsq : x ^ 2 = a * b)
    (u v w i j l : ℕ) (hu : u ≤ 2) (hstrong : 2 * i + j ≤ v + 1)
    (htotal : u + v + w = 2 * (i + j + l))
    (hW : W ^ 2 ≤ s ^ u * a ^ v * b ^ w) :
    W ≤ s / x * a ^ i * x ^ j * b ^ l := by
  apply le_of_sq_le_sq (hW.trans (incidence_square_compression ha hab hbs hx hxsq
    u v w i j l hu hstrong htotal))
  have hb : 0 ≤ b := (ha.trans_le hab).le
  have hs : 0 ≤ s := hb.trans hbs
  positivity

/-- Direct specialization to the submitted path/edge/loop incidence counts.
The two identities are exactly 2P=u+L5+L4 and S+C=m-3-P, rewritten
without truncated subtraction. -/
lemma reflection_count_compression {W : ℝ} (P u L5 L4 S C i j l : ℕ)
    (hends : u + L5 + L4 = 2 * P) (hedges : S + C + P = i + j + l)
    (hu : u ≤ 2) (hstrong : 2 * i + j ≤ 2 * S + L5 + 1)
    (hW : W ^ 2 ≤ alphabetMass 5 radius ^ u * strongBound ^ (2 * S + L5) *
      carryBound ^ (2 * C + L4)) :
    radius ^ 10 * W ≤ geometricTerm (i, j, l) := by
  have htotal : u + (2 * S + L5) + (2 * C + L4) = 2 * (i + j + l) := by omega
  have hx : mixedRoot ^ 2 = strongBound * carryBound :=
    Real.sq_sqrt (mul_nonneg norm_bound_order.1.le (norm_bound_order.1.trans norm_bound_order.2.1).le)
  have h := incidence_compression norm_bound_order.1 norm_bound_order.2.1.le alphabet_five_ge_carry
    mixedRoot_pos hx u (2 * S + L5) (2 * C + L4) i j l hu hstrong htotal hW
  have hp := mul_le_mul_of_nonneg_left h (pow_nonneg radius_bounds.1.le 10)
  calc
    radius ^ 10 * W ≤ radius ^ 10 * (alphabetMass 5 radius / mixedRoot *
        strongBound ^ i * mixedRoot ^ j * carryBound ^ l) := hp
    _ = geometricTerm (i, j, l) := by unfold geometricTerm; ring

end SubmittedGenus.CapFiveMass
