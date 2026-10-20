import Results.Genus.RawGraph.Fixtures
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Kernel-checkable Kronecker packing

This is the exact integer encoding used by the original packed producer:
one base-2^width digit per polynomial coefficient. The no-carry hypotheses
are explicit and proved before a digit is accepted as a source coefficient.
-/
namespace SubmittedGenus.RawGraph.Packing
open scoped BigOperators

/-- Little-endian coefficient packing into one natural number. -/
def pack {n : ℕ} (base : ℕ) (c : Fin n → ℕ) : ℕ := Nat.ofDigits base (List.ofFn c)

def digit (base packed k : ℕ) : ℕ := packed / base ^ k % base

/-- Exact digit extraction under a sufficient carry-free bound. -/
theorem digit_pack {n base : ℕ} (hb : 0 < base) (c : Fin n → ℕ)
    (hc : ∀ i, c i < base) (k : Fin n) : digit base (pack base c) k.val = c k := by
  unfold digit pack
  have hlist : ∀ v ∈ List.ofFn c, v < base := by
    intro v hv
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
    exact hc i
  rw [Nat.ofDigits_div_pow_eq_ofDigits_drop k.val hb _ hlist,
    Nat.ofDigits_mod_eq_head!]
  have hh : ((List.ofFn c).drop k.val).head! = c k := by
    simp [List.head!_eq_getElem!, List.getElem!_eq_getElem?_getD, List.getElem?_drop,
      List.getElem?_ofFn, k.isLt]
  rw [hh, Nat.mod_eq_of_lt (hc k)]

/-- Arithmetic interpretation of the packed coefficient vector. -/
theorem pack_eq_sum {n : ℕ} (base : ℕ) (c : Fin n → ℕ) :
    pack base c = ∑ i : Fin n, c i * base ^ i.val := by
  induction n with
  | zero => simp [pack]
  | succ n ih =>
    rw [pack, List.ofFn_succ, Nat.ofDigits_cons, Fin.sum_univ_succ]
    change c 0 + base * pack base (fun i : Fin n => c i.succ) = _
    rw [ih, Finset.mul_sum]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- Polynomial evaluation is exactly coefficient packing once the vector
covers the complete support. -/
theorem eval_eq_pack (p : Polynomial ℕ) {n : ℕ} (hn : p.natDegree < n) (base : ℕ) :
    p.eval base = pack base (fun i : Fin n => p.coeff i.val) := by
  rw [pack_eq_sum, Polynomial.eval_eq_sum_range' hn]
  exact (Fin.sum_univ_eq_sum_range _ n).symm

/-- The total coefficient mass is a simple sufficient no-carry bound. -/
theorem coeff_le_eval_one (p : Polynomial ℕ) (k : ℕ) : p.coeff k ≤ p.eval 1 := by
  by_cases hk : k ≤ p.natDegree
  · rw [Polynomial.eval_eq_sum_range]
    have hh := Finset.single_le_sum (s := Finset.range (p.natDegree + 1))
      (f := fun i => p.coeff i * 1 ^ i) (fun i _ => Nat.zero_le _)
      (Finset.mem_range.mpr (by omega : k < p.natDegree + 1))
    simpa using hh
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < k)]
    exact Nat.zero_le _


/-- One large integer multiplication certifies all product coefficients,
provided the declared coefficient bound rules out carries. -/
theorem digit_eval_mul (p q : Polynomial ℕ) {n base : ℕ}
    (hn : (p * q).natDegree < n) (hb : 0 < base)
    (hc : ∀ i : Fin n, (p * q).coeff i.val < base) (k : Fin n) :
    digit base (p.eval base * q.eval base) k.val = (p * q).coeff k.val := by
  rw [← Polynomial.eval_mul, eval_eq_pack _ hn]
  exact digit_pack hb _ hc k

/-- Taking the packed residue discards only coefficients beyond the cutoff. -/
theorem pack_mod_pow {n base : ℕ} (hb : 0 < base) (c : Fin n → ℕ)
    (hc : ∀ i, c i < base) (cutoff : ℕ) :
    pack base c % base ^ cutoff = Nat.ofDigits base ((List.ofFn c).take cutoff) := by
  apply Nat.ofDigits_mod_pow_eq_ofDigits_take cutoff hb
  intro v hv
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
  exact hc i


/-- Modulo a packed cutoff preserves every digit below that cutoff, even for
arbitrary intermediate integers. -/
theorem digit_mod_pow {base packed cutoff k : ℕ} (hk : k < cutoff) :
    digit base (packed % base ^ cutoff) k = digit base packed k := by
  unfold digit
  have he : base ^ cutoff = base ^ k * base ^ (cutoff - k) := by
    rw [← pow_add, Nat.add_sub_of_le hk.le]
  rw [he, Nat.mod_mul_right_div_self]
  exact Nat.mod_mod_of_dvd _ (dvd_pow_self base (by omega))

/-- Exact source coefficient recovery after the producer's multiply-and-mask
step. All arithmetic is ordinary kernel-checked Nat arithmetic. -/
theorem digit_truncated_mul (p q : Polynomial ℕ) {n base cutoff : ℕ}
    (hn : (p * q).natDegree < n) (hb : 0 < base)
    (hc : ∀ i : Fin n, (p * q).coeff i.val < base)
    (k : Fin n) (hk : k.val < cutoff) :
    digit base ((p.eval base % base ^ cutoff * (q.eval base % base ^ cutoff)) %
      base ^ cutoff) k.val = (p * q).coeff k.val := by
  rw [← Nat.mul_mod, digit_mod_pow hk]
  exact digit_eval_mul p q hn hb hc k

/-- The complete checked loop-bearing m=6 fixture coefficient vector. -/
def fixtureCoefficients (k : Fin 18) : ℕ :=
  if k.val = 13 then 2 else if k.val = 14 then 5 else if k.val = 15 then 5
  else if k.val = 16 then 3 else if k.val = 17 then 1 else 0

theorem fixtureCoefficients_source (k : Fin 18) :
    (rawPolynomial 6 1 2 4).coeff k.val = fixtureCoefficients k := by
  rw [LayoutCompiler.sampleLayout_polynomial]
  fin_cases k <;> norm_num [fixtureCoefficients]

theorem fixtureCoefficients_bound (k : Fin 18) : fixtureCoefficients k < 16 := by
  unfold fixtureCoefficients
  split_ifs <;> omega

/-- A single packed integer contains the complete original source fixture. -/
theorem fixture_pack_value : pack 16 fixtureCoefficients = 79186 * 16 ^ 13 := by decide

theorem fixture_packed_coefficients (k : Fin 18) :
    (rawPolynomial 6 1 2 4).coeff k.val = digit 16 (79186 * 16 ^ 13) k.val := by
  rw [fixtureCoefficients_source, ← fixture_pack_value]
  exact (digit_pack (by decide) _ fixtureCoefficients_bound k).symm

/-- A corrupted candidate digit is rejected by kernel arithmetic. -/
theorem fixture_rejects_wrong_coefficient : digit 16 (79186 * 16 ^ 13) 14 ≠ 6 := by decide

end SubmittedGenus.RawGraph.Packing
