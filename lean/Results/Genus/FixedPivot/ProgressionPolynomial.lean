import Results.Genus.FixedPivot.Denominator

/-! The exact integral progression denominator Q_d(y,z), without a fitted recurrence. -/
namespace SubmittedGenus.FixedPivot
open scoped BigOperators
open Polynomial
noncomputable section
section Ring
variable {R : Type*} [CommRing R]

def progressionPair (b c : R) (d j : ℕ) : Polynomial R :=
  1-C (c^j*traceSum b c (d-2*j))*X+C (c^d)*X^2

lemma progressionPair_eq_roots (b c lam mu : R) (hb : lam+mu=b) (hc : lam*mu=c)
    (d j : ℕ) (hj : 2*j≤d) :
    progressionPair b c d j=
      (1-C (lam^(d-j)*mu^j)*X)*(1-C (lam^j*mu^(d-j))*X) := by
  unfold progressionPair
  rw [traceSum_eq_of_roots b c lam mu hb hc,← hc]
  generalize hn : d-2*j=n
  have h1 : d-j=n+j := by omega
  have h2 : d=n+j+j := by omega
  rw [h1,h2]
  simp only [mul_pow,pow_add,map_add,map_mul,map_pow]
  ring

lemma prod_range_pair_even (f : ℕ→R) (t : ℕ) :
    (∏ j ∈ Finset.range (2*t),f j)=∏ j ∈ Finset.range t,f j*f (2*t-1-j) := by
  rw [show 2*t=t+t by omega,Finset.prod_range_add,
    ← Finset.prod_range_reflect (fun j => f (t+j)) t,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  have hh:=Finset.mem_range.mp hj
  congr 2
  omega

lemma prod_range_pair_odd (f : ℕ→R) (t : ℕ) :
    (∏ j ∈ Finset.range (2*t+1),f j)=(∏ j ∈ Finset.range t,f j*f (2*t-j))*f t := by
  rw [show 2*t+1=(t+1)+t by omega,Finset.prod_range_add,Finset.prod_range_succ,
    ← Finset.prod_range_reflect (fun j => f (t+1+j)) t,mul_right_comm,← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  have hh:=Finset.mem_range.mp hj
  congr 2
  omega

/-- Integer-coefficient paired construction from the original Newton sums. -/
def progressionPolynomial (b c : R) (d : ℕ) : Polynomial R :=
  (∏ j ∈ Finset.range ((d+1)/2),progressionPair b c d j)*
    (if Even d then 1-C (c^(d/2))*X else 1)

/-- Exact product over every progression mode, including both pure modes. -/
theorem progressionPolynomial_eq_roots (b c lam mu : R) (hb : lam+mu=b) (hc : lam*mu=c)
    (d : ℕ) :
    progressionPolynomial b c d=∏ j ∈ Finset.range (d+1),(1-C (lam^(d-j)*mu^j)*X) := by
  rcases Nat.even_or_odd d with he | ho
  · obtain ⟨t,ht⟩:=he
    have hd : d=2*t := by omega
    rw [hd]
    rw [progressionPolynomial,if_pos (even_two_mul _),
      show (2*t+1)/2=t by omega,show 2*t/2=t by omega,
      prod_range_pair_odd]
    have hcenter : (1-C (lam^(2*t-t)*mu^t)*X)=(1-C (c^t)*X) := by
      rw [show 2*t-t=t by omega,← mul_pow,hc]
    rw [hcenter]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    have hh:=Finset.mem_range.mp hj
    rw [progressionPair_eq_roots b c lam mu hb hc _ _ (by omega)]
    rw [show 2*t-(2*t-j)=j by omega]
  · obtain ⟨t,ht⟩:=ho
    subst d
    rw [progressionPolynomial,if_neg (by rw [Nat.even_iff]; omega),mul_one,
      show (2*t+1+1)/2=t+1 by omega,show 2*t+1+1=2*(t+1) by omega,
      prod_range_pair_even]
    apply Finset.prod_congr rfl
    intro j hj
    have hh:=Finset.mem_range.mp hj
    rw [progressionPair_eq_roots b c lam mu hb hc _ _ (by omega)]
    rw [show 2*(t+1)-1-j=2*t+1-j by omega,
      show 2*t+1-(2*t+1-j)=j by omega]

end Ring

/-- The original bivariate Q_d belongs to Z[z,y]. -/
def sourceQ (d : ℕ) : Polynomial (Polynomial ℤ) :=
  progressionPolynomial (carryB X) (carryC X) d

end
end SubmittedGenus.FixedPivot
