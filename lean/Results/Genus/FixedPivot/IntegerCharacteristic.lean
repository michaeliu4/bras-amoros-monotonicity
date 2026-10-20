import Results.Genus.FixedPivot.IntegerProgression
import Results.Genus.FixedPivot.ReflectedProduct

/-! Literal integral characteristic polynomial and its actual original source recurrence. -/
namespace SubmittedGenus.FixedPivot
open Polynomial RawGraph
open scoped BigOperators
noncomputable section

lemma sourceQ_coeff_zero (d : ℕ) : (sourceQ d).coeff 0=1 := by
  unfold sourceQ progressionPolynomial
  split_ifs <;> simp [Polynomial.coeff_zero_eq_eval_zero,progressionPair,Polynomial.eval_prod]

lemma sourceP_coeff_top (d : ℕ) : (sourceP d).coeff (d+1)=1 := by
  rw [sourceP_coeff _ _ (le_refl _),Nat.sub_self,sourceQ_coeff_zero]

lemma sourceP_monic (d : ℕ) : (sourceP d).Monic :=
  Polynomial.monic_of_natDegree_le_of_coeff_eq_one (d+1) (sourceP_natDegree_le d) (sourceP_coeff_top d)

lemma sourceP_natDegree (d : ℕ) : (sourceP d).natDegree=d+1 :=
  Polynomial.natDegree_eq_of_le_of_coeff_ne_zero (sourceP_natDegree_le d)
    (by rw [sourceP_coeff_top]; exact one_ne_zero)

section RootIdentity
variable {R : Type*} [CommRing R]

/-- The integral reflected polynomial is exactly the original product of all
characteristic roots after any coefficient specialization containing the roots. -/
theorem sourceP_map_eq_roots (f : Polynomial ℤ→+*R) (lam mu : R)
    (hb : lam+mu=carryB (f X)) (hc : lam*mu=carryC (f X)) (d : ℕ) :
    (sourceP d).map f=∏ j∈Finset.range (d+1),(X-C (lam^(d-j)*mu^j)) := by
  rw [sourceP,← Polynomial.reflect_map,sourceQ,map_progressionPolynomial]
  simp only [carryB,carryC,map_add,map_sub,map_neg,map_pow] at hb hc ⊢
  rw [progressionPolynomial_eq_roots _ _ lam mu hb hc d]
  simpa only [Finset.card_range] using reflect_linearProduct (Finset.range (d+1)) (fun j=>lam^(d-j)*mu^j)

end RootIdentity

/-- Unconditional identification in the already constructed original source
quadratic localization, with no free root hypotheses remaining. -/
theorem sourceP_source_roots (d : ℕ) :
    (sourceP d).map (sourceEmbedding.comp integerPolynomialToRational)=
      ∏ j∈Finset.range (d+1),(X-C (sourceLambda^(d-j)*sourceMu^j)) := by
  apply sourceP_map_eq_roots _ _ _
  · change sourceLambda+sourceMu=carryB (sourceEmbedding (integerPolynomialToRational X))
    rw [show integerPolynomialToRational X=X from Polynomial.map_X _]
    exact source_roots_sum
  · change sourceLambda*sourceMu=carryC (sourceEmbedding (integerPolynomialToRational X))
    rw [show integerPolynomialToRational X=X from Polynomial.map_X _]
    exact source_roots_product


/-- The original scalar recurrence, directly on the integer raw source
polynomials, on every phase and from its first progression term onward. -/
theorem rawPolynomialZ_characteristic_recurrence {r N d : ℕ}
    (hr : 0<r) (hd : 0<d) (hN : d<N) (hbig : r+2*d<N) (n : ℕ) :
    (∑ j∈Finset.range (d+2),(sourceP d).coeff j*
      rawPolynomialZ (r+(N+(n+j)*d)) r (r+d))=0 := by
  let f : ℕ→Polynomial ℤ := fun j=>(sourceQ d).coeff j*
    rawPolynomialZ (r+(N+(n+d+1-j)*d)) r (r+d)
  have hz:=integerProgressionSeries_coeff_zero hr hd hN hbig (n+d+1) (by omega)
  rw [PowerSeries.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hz
  simp only [Polynomial.coeff_coe,integerProgressionSeries,PowerSeries.coeff_mk] at hz
  have hs : (∑ j∈Finset.range (d+2),f j)=0 := by
    calc
      _=∑ j∈Finset.range (n+d+1+1),f j := by
        apply Finset.sum_subset (Finset.range_mono (by omega))
        intro j hj hn
        have hj' : d+1<j := by simp only [Finset.mem_range] at hn; omega
        exact mul_eq_zero_of_left
          (Polynomial.coeff_eq_zero_of_natDegree_lt ((sourceQ_natDegree d).trans_lt hj')) _
      _=0 := hz
  calc
    _=∑ j∈Finset.range (d+2),f (d+2-1-j) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hj' : j≤d+1 := by have:=Finset.mem_range.mp hj; omega
      rw [sourceP_coeff d j hj']
      dsimp only [f]
      rw [show d+2-1-j=d+1-j by omega,show n+d+1-(d+1-j)=n+j by omega]
    _=∑ j∈Finset.range (d+2),f j := Finset.sum_range_reflect f (d+2)
    _=0 := hs

/-- Original parameter spelling: every m0>2p, every n≥0, with d=p-r.
This theorem refers directly to the actual original raw partition polynomials. -/
theorem rawPolynomialZ_recurrence_original {r p m0 : ℕ}
    (hr : 0<r) (hrp : r<p) (hm0 : 2*p<m0) (n : ℕ) :
    (∑ j∈Finset.range (p-r+2),(sourceP (p-r)).coeff j*
      rawPolynomialZ (m0+(n+j)*(p-r)) r p)=0 := by
  have hh:=rawPolynomialZ_characteristic_recurrence (r:=r) (N:=m0-r) (d:=p-r)
    hr (by omega) (by omega) (by omega) n
  have hp : r+(p-r)=p := by omega
  have hm : r+(m0-r)=m0 := by omega
  simpa only [← Nat.add_assoc,hp,hm] using hh

end
end SubmittedGenus.FixedPivot
