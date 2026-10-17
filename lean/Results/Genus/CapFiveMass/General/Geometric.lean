import Results.Genus.CapFiveMass.General.Control

/-! Exact three-index geometric sum at every radius and norm bounds satisfying
 the original submitted multiple-five hypotheses. -/

noncomputable section
open scoped BigOperators
namespace SubmittedGenus.CapFiveMass.General

def mixedRoot (H : Control) : ℝ := Real.sqrt (H.a * H.b)
def geometricTerm (H : Control) (q : ℕ × ℕ × ℕ) : ℝ :=
  (H.z ^ 10 * alphabetMass 5 H.z / mixedRoot H) *
    (H.a ^ q.1 * ((mixedRoot H) ^ q.2.1 * H.b ^ q.2.2))
def rootMajorant (H : Control) : ℝ :=
  H.z ^ 10 * alphabetMass 5 H.z /
    (mixedRoot H * (1 - mixedRoot H) * (1 - H.a) * (1 - H.b))

lemma mixedRoot_pos (H : Control) : 0 < mixedRoot H :=
  Real.sqrt_pos.mpr (mul_pos H.a_pos H.b_pos)
lemma mixedRoot_sq (H : Control) : mixedRoot H ^ 2 = H.a * H.b :=
  Real.sq_sqrt (mul_nonneg H.a_pos.le H.b_pos.le)
lemma mixedRoot_lt_one (H : Control) : mixedRoot H < 1 := by
  have hab : H.a * H.b < 1 := by
    calc
      H.a * H.b < 1 * H.b := mul_lt_mul_of_pos_right H.a_lt_one H.b_pos
      _ = H.b := one_mul _
      _ < 1 := H.b_lt_one
  have hs := mixedRoot_sq H
  have hn := mixedRoot_pos H
  nlinarith

lemma geometricTerm_nonneg (H : Control) (q : ℕ × ℕ × ℕ) : 0 ≤ geometricTerm H q := by
  have hs : 0 ≤ alphabetMass 5 H.z := Finset.sum_nonneg fun _ _ => pow_nonneg H.z_pos.le _
  exact mul_nonneg (div_nonneg (mul_nonneg (pow_nonneg H.z_pos.le _) hs) (mixedRoot_pos H).le)
    (mul_nonneg (pow_nonneg H.a_pos.le _) (mul_nonneg (pow_nonneg (mixedRoot_pos H).le _)
      (pow_nonneg H.b_pos.le _)))

lemma geometric_hasSum (H : Control) : HasSum (geometricTerm H) (rootMajorant H) := by
  have ha := hasSum_geometric_of_lt_one H.a_pos.le H.a_lt_one
  have hx := hasSum_geometric_of_lt_one (mixedRoot_pos H).le (mixedRoot_lt_one H)
  have hb := hasSum_geometric_of_lt_one H.b_pos.le H.b_lt_one
  have hxb := hx.mul hb (hx.summable.mul_of_nonneg hb.summable
    (fun _ => pow_nonneg (mixedRoot_pos H).le _)
    (fun _ => pow_nonneg H.b_pos.le _))
  have hall := ha.mul hxb (ha.summable.mul_of_nonneg hxb.summable
    (fun _ => pow_nonneg H.a_pos.le _)
    (fun _ => mul_nonneg (pow_nonneg (mixedRoot_pos H).le _) (pow_nonneg H.b_pos.le _)))
  have h := hall.mul_left (H.z ^ 10 * alphabetMass 5 H.z / mixedRoot H)
  have he : H.z ^ 10 * alphabetMass 5 H.z / mixedRoot H *
      ((1 - H.a)⁻¹ * ((1 - mixedRoot H)⁻¹ * (1 - H.b)⁻¹)) = rootMajorant H := by
    unfold rootMajorant
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [he] at h
  exact h

lemma geometric_summable (H : Control) : Summable (geometricTerm H) := (geometric_hasSum H).summable
lemma geometric_tsum (H : Control) : (∑' q, geometricTerm H q) = rootMajorant H :=
  (geometric_hasSum H).tsum_eq

end SubmittedGenus.CapFiveMass.General
