import Results.Genus.RawGraph.PackedAcceptance.CompressedSignature

/-! Division-free extraction of the first edge threshold from a two-step
matrix. Both masks and both gates remain in the shifted entries. -/
namespace SubmittedGenus.RawGraph.PackedAcceptance.PairMonomialShift
open CompressedSignature
open scoped BigOperators Matrix
variable {R : Type*} [CommSemiring R] {k : ℕ}

/-- Both vertex weights are consumed once. The first compatibility gate
justifies the natural-number subtraction in the exponent. -/
def shiftedPairMatrix (z : R) (a b : Step k) : Matrix (Fin k) (Fin k) R :=
  fun i l => ∑ j,
    if a.mask i then
      if a.bound ≤ i.val+j.val then
        if b.mask j then
          if b.bound ≤ j.val+l.val then z^(i.val+j.val-a.bound) else 0
        else 0
      else 0
    else 0

/-- Exact over every commutative semiring, including nonunits and z=0. -/
theorem pair_factor (z : R) (a b : Step k) :
    stepMatrix z a * stepMatrix z b = z^a.bound • shiftedPairMatrix z a b := by
  ext i l
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul,
    shiftedPairMatrix, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  unfold stepMatrix
  split_ifs <;> try simp_all only [mul_zero, zero_mul]
  rw [← pow_add, ← pow_add, Nat.add_sub_of_le (by assumption)]

lemma scalar_matrix_mul (c d : R) (A B : Matrix (Fin k) (Fin k) R) :
    (c • A) * (d • B) = (c*d) • (A*B) := by
  ext i l
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ac_rfl

/-- Power compression preserves the accumulated exact monomial shift. -/
theorem pair_power_factor (z : R) (a b : Step k) (n : ℕ) :
    (stepMatrix z a * stepMatrix z b)^n =
      z^(a.bound*n) • (shiftedPairMatrix z a b)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, pair_factor, scalar_matrix_mul, ← pow_add]
    simp only [Nat.mul_succ, pow_succ]

#print axioms pair_factor
#print axioms pair_power_factor
end SubmittedGenus.RawGraph.PackedAcceptance.PairMonomialShift
