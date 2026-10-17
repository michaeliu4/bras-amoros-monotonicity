import Results.Genus.FixedPivot.CarryTransfer
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Exact original mixed denominator

All factors are constructed over integers. The spectral factorization is proved
in every commutative ring containing two roots with the specified sum/product;
it is an algebraic identity, not a numerical eigenvalue approximation.
-/

namespace SubmittedGenus.FixedPivot
open scoped BigOperators

section Ring
variable {R : Type*} [CommRing R]

/-- Original Newton-sum recurrence S0=2, S1=b, S(n+2)=b*S(n+1)-c*Sn. -/
def traceSum (b c : R) : ℕ → R
  | 0 => 2
  | 1 => b
  | n+2 => b*traceSum b c (n+1)-c*traceSum b c n

@[simp] lemma traceSum_zero (b c : R) : traceSum b c 0 = 2 := rfl
@[simp] lemma traceSum_one (b c : R) : traceSum b c 1 = b := rfl
lemma traceSum_rec (b c : R) (n : ℕ) :
    traceSum b c (n+2) = b*traceSum b c (n+1)-c*traceSum b c n := rfl

/-- The recurrence is the exact sum of powers of the two roots. -/
theorem traceSum_eq_powers (lam mu : R) (n : ℕ) :
    traceSum (lam+mu) (lam*mu) n = lam^n+mu^n := by
  induction n using Nat.twoStepInduction with
  | zero => simp; ring
  | one => simp
  | more n ih ih1 =>
    rw [traceSum_rec, ih, ih1]
    simp only [pow_add, pow_one, pow_two]
    ring

lemma traceSum_eq_of_roots (b c lam mu : R) (hb : lam+mu=b) (hc : lam*mu=c) (n : ℕ) :
    traceSum b c n = lam^n+mu^n := by
  rw [← hb, ← hc, traceSum_eq_powers]

/-- The submitted paired factor after setting the progression variable y=1. -/
def mixedPair (z : R) (d j : ℕ) : R :=
  1-(carryC z)^j*traceSum (carryB z) (carryC z) (d-2*j)+(carryC z)^d

/-- Pairing j with d-j is valid without a distinct-root or nonzero-root premise. -/
theorem mixedPair_eq_roots (z lam mu : R) (hb : lam+mu=carryB z)
    (hc : lam*mu=carryC z) (d j : ℕ) (hj : 2*j ≤ d) :
    mixedPair z d j = (1-lam^(d-j)*mu^j)*(1-lam^j*mu^(d-j)) := by
  unfold mixedPair
  rw [traceSum_eq_of_roots _ _ lam mu hb hc, ← hc]
  generalize hn : d-2*j=n
  have h1 : d-j = n+j := by omega
  have h2 : d = n+j+j := by omega
  rw [h1, h2]
  simp only [mul_pow, pow_add]
  ring

/-- A root-product expression containing precisely indices1,...,d-1. -/
def spectralMixed (lam mu : R) (d : ℕ) : R :=
  ∏ j ∈ Finset.range (d-1), (1-lam^(d-(j+1))*mu^(j+1))

/-- Exact integer construction from paired mixed factors and the optional center. -/
def mixedDenominator (z : R) (d : ℕ) : R :=
  (∏ j ∈ Finset.range ((d-1)/2), mixedPair z d (j+1)) *
    (if Even d then 1-(carryC z)^(d/2) else 1)

lemma spectralMixed_odd (lam mu : R) (t : ℕ) :
    spectralMixed lam mu (2*t+1) =
      ∏ j ∈ Finset.range t,
        ((1-lam^(2*t+1-(j+1))*mu^(j+1)) *
         (1-lam^(j+1)*mu^(2*t+1-(j+1)))) := by
  unfold spectralMixed
  rw [show 2*t+1-1=t+t by omega, Finset.prod_range_add]
  rw [← Finset.prod_range_reflect (fun j => 1-lam^(2*t+1-(t+j+1))*mu^(t+j+1)) t]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  have hj' := Finset.mem_range.mp hj
  have h1 : 2*t+1-(t+(t-1-j)+1)=j+1 := by omega
  have h2 : t+(t-1-j)+1=2*t+1-(j+1) := by omega
  rw [h1,h2]

lemma spectralMixed_even (lam mu : R) (t : ℕ) :
    spectralMixed lam mu (2*(t+1)) =
      (∏ j ∈ Finset.range t,
        ((1-lam^(2*(t+1)-(j+1))*mu^(j+1)) *
         (1-lam^(j+1)*mu^(2*(t+1)-(j+1))))) * (1-(lam*mu)^(t+1)) := by
  unfold spectralMixed
  rw [show 2*(t+1)-1=(t+1)+t by omega, Finset.prod_range_add]
  rw [Finset.prod_range_succ]
  rw [← Finset.prod_range_reflect (fun j =>
    1-lam^(2*(t+1)-(t+1+j+1))*mu^(t+1+j+1)) t]
  have hc : 1-lam^(2*(t+1)-(t+1))*mu^(t+1) = 1-(lam*mu)^(t+1) := by
    rw [show 2*(t+1)-(t+1)=t+1 by omega, mul_pow]
  rw [hc, mul_right_comm, ← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  have hj' := Finset.mem_range.mp hj
  have h1 : 2*(t+1)-(t+1+(t-1-j)+1)=j+1 := by omega
  have h2 : t+1+(t-1-j)+1=2*(t+1)-(j+1) := by omega
  rw [h1,h2]

/-- The constructed integer expression is exactly the original spectral R_d. -/
theorem mixedDenominator_eq_spectral (z lam mu : R)
    (hb : lam+mu=carryB z) (hc : lam*mu=carryC z) (d : ℕ) (hd : 0 < d) :
    mixedDenominator z d = spectralMixed lam mu d := by
  rcases Nat.even_or_odd d with he | ho
  · obtain ⟨k,hk⟩ := he
    have hkpos : 0 < k := by omega
    obtain ⟨t,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hkpos)
    have hd' : d=2*(t+1) := by omega
    rw [hd', mixedDenominator, if_pos (even_two_mul _), spectralMixed_even]
    have hdiv : (2*(t+1)-1)/2=t := by omega
    have hdiv' : 2*(t+1)/2=t+1 := by omega
    rw [hdiv,hdiv',← hc]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    exact mixedPair_eq_roots z lam mu hb hc _ _ (by have := Finset.mem_range.mp hj; omega)
  · obtain ⟨t,ht⟩ := ho
    subst d
    rw [mixedDenominator, if_neg (by rw [Nat.even_iff]; omega), spectralMixed_odd]
    have hdiv : (2*t+1-1)/2=t := by omega
    rw [hdiv,mul_one]
    apply Finset.prod_congr rfl
    intro j hj
    exact mixedPair_eq_roots z lam mu hb hc _ _ (by have := Finset.mem_range.mp hj; omega)

variable {S : Type*} [CommRing S]

lemma map_traceSum (f : R →+* S) (b c : R) (n : ℕ) :
    f (traceSum b c n) = traceSum (f b) (f c) n := by
  induction n using Nat.twoStepInduction with
  | zero => exact map_ofNat f 2
  | one => simp
  | more n ih ih1 => simp only [traceSum_rec,map_sub,map_mul,ih,ih1]

lemma map_mixedDenominator (f : R →+* S) (z : R) (d : ℕ) :
    f (mixedDenominator z d) = mixedDenominator (f z) d := by
  simp only [mixedDenominator,map_mul,map_prod]
  congr 1
  · apply Finset.prod_congr rfl
    intro j _
    simp [mixedPair,map_traceSum,carryB,carryC]
  · split_ifs <;> simp [carryC]

/-- Original fixed-factor identity for the odd-gap case. -/
theorem pure_denominator_one (z : R) :
    1-traceSum (carryB z) (carryC z) 1+carryC z =
      (1-z-z^2)*(1+z+z^2) := by
  simp [carryB,carryC]
  ring

/-- Original fixed-factor identity for the even-gap case. -/
theorem pure_denominator_two (z : R) :
    1-traceSum (carryB z) (carryC z) 2+(carryC z)^2 =
      (1-z-z^2)*(1+z+2*z^2+z^3-z^5-z^6) := by
  simp [traceSum,carryB,carryC]
  ring

end Ring

/-- R_d is a polynomial over the integers, using precisely the submitted factors. -/
noncomputable def sourceR (d : ℕ) : Polynomial ℤ := mixedDenominator Polynomial.X d

/-- Every evaluation of the integer polynomial agrees with the algebraic construction. -/
theorem sourceR_eval {R : Type*} [CommRing R] (z : R) (d : ℕ) :
    Polynomial.eval₂ (Int.castRingHom R) z (sourceR d) = mixedDenominator z d := by
  exact (map_mixedDenominator (Polynomial.eval₂RingHom (Int.castRingHom R) z)
    Polynomial.X d).trans (by simp)

end SubmittedGenus.FixedPivot
