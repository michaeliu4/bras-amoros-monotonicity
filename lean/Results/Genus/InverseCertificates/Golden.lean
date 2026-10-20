import Results.Genus.InverseCertificates.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section
namespace SubmittedGenus.InverseCertificates

/-- The radius used throughout the original submitted proof. -/
def q : ℝ := (Real.sqrt 5 - 1) / 2

lemma q_nonneg : 0 ≤ q := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have hp := Real.sqrt_nonneg (5 : ℝ)
  dsimp [q]
  nlinarith

lemma q_relation : q ^ 2 + q = 1 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  dsimp [q]
  nlinarith

lemma q_lower : (3 : ℝ) / 5 < q := by
  have h := q_relation
  have hn := q_nonneg
  by_contra! hbad
  have hh : q * q ≤ (3 / 5 : ℝ) * (3 / 5) :=
    mul_self_le_mul_self hn hbad
  nlinarith

lemma q_upper : q ≤ (309017 : ℝ) / 500000 := by
  have h := q_relation
  have hn := q_nonneg
  by_contra! hbad
  have hh : ((309017 : ℝ) / 500000) * (309017 / 500000) ≤ q * q :=
    mul_self_le_mul_self (by norm_num) hbad.le
  nlinarith

lemma q_lt_one : q < 1 := by linarith [q_upper]

end SubmittedGenus.InverseCertificates
