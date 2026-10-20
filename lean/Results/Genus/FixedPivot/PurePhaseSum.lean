import Results.Genus.FixedPivot.PurePhases
import Results.Genus.FixedPivot.PureDivisor

/-! Finite all-phase sums of the source pure modes, before localization descent. -/
namespace SubmittedGenus.FixedPivot
open scoped BigOperators
noncomputable section
section Ring
variable {R : Type*} [CommRing R]

lemma progression_value (f : ℕ→R) (q : R) (tau : ℕ)
    (hstep : ∀ n,f (n+tau)=q*f n) (n k : ℕ) :
    f (n+tau*k)=q^k*f n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show n+tau*(k+1)=(n+tau*k)+tau by ring,hstep,ih,pow_succ]
    ring

lemma progression_block_sum (f : ℕ→R) (q : R) (tau : ℕ)
    (hstep : ∀ n,f (n+tau)=q*f n) (k : ℕ) :
    (∑ n∈Finset.range (tau*k),f n)=
      (∑ j∈Finset.range k,q^j)*(∑ n∈Finset.range tau,f n) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show tau*(k+1)=tau*k+tau by ring,Finset.sum_range_add,ih,Finset.sum_range_succ,add_mul]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    rw [show tau*k+n=n+tau*k by omega,progression_value f q tau hstep]

def sourcePurePhase (z theta other ti di : R) (r d k : ℕ) : R :=
  canonicalPureContribution z theta other ti di r (r+2*d+1+k) d (by omega)

lemma canonicalPureContribution_congr (z theta other ti di : R) (r d N M : ℕ)
    (hN : d<N) (hM : d<M) (h : N=M) :
    canonicalPureContribution z theta other ti di r N d hN=
      canonicalPureContribution z theta other ti di r M d hM := by
  subst M
  rfl

lemma sourcePurePhase_step (z theta other bi ti di : R)
    (hb : theta+other=carryB z) (hc : theta*other=carryC z) (hbi : carryB z*bi=1)
    (r d : ℕ) (hd : 0<d) (k : ℕ) :
    sourcePurePhase z theta other ti di r d (k+sourceTau d)=
      theta^(sourceTau d)*sourcePurePhase z theta other ti di r d k := by
  unfold sourceTau
  split_ifs with he
  · have hh:=pureContribution_even_step z theta other bi ti di hb hc hbi r (r+2*d+1+k)
      d hd (by omega) (by omega) he
    exact (canonicalPureContribution_congr z theta other ti di r d _ _ _ _ (by omega)).trans hh
  · have ho : Odd d:=Nat.not_even_iff_odd.mp he
    have hh:=pureContribution_odd_step z theta other bi ti di hb hc hbi r (r+2*d+1+k)
      d hd (by omega) (by omega) ho
    simp only [pow_one]
    exact (canonicalPureContribution_congr z theta other ti di r d _ _ _ _ (by omega)).trans hh

/-- The sum over all d original phases contains the correct finite geometric
factor, with tau=1 for odd gaps and tau=2 for even gaps. -/
theorem sourcePurePhase_sum (z theta other bi ti di : R)
    (hb : theta+other=carryB z) (hc : theta*other=carryC z) (hbi : carryB z*bi=1)
    (r d : ℕ) (hd : 0<d) :
    (∑ k∈Finset.range d,sourcePurePhase z theta other ti di r d k)=
      (∑ j∈Finset.range (d/sourceTau d),(theta^(sourceTau d))^j)*
      (∑ k∈Finset.range (sourceTau d),sourcePurePhase z theta other ti di r d k) := by
  have hh:=progression_block_sum (sourcePurePhase z theta other ti di r d)
    (theta^(sourceTau d)) (sourceTau d)
    (sourcePurePhase_step z theta other bi ti di hb hc hbi r d hd) (d/sourceTau d)
  rw [sourceTau_mul_div] at hh
  exact hh

end Ring
end
end SubmittedGenus.FixedPivot
