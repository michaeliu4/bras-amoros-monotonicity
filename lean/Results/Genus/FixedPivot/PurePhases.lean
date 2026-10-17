import Results.Genus.FixedPivot.CanonicalEndpoints

/-! Exact all-multiplicity pure-mode cancellation mechanism of the submitted proof. -/
namespace SubmittedGenus.FixedPivot
open scoped BigOperators
noncomputable section
section Ring
variable {R : Type*} [CommRing R]

/-- One core contraction, independent of multiplicity and of all port pairings. -/
def canonicalPureCore (z theta : R) (r d : ℕ) (hd : 0<d) : R :=
  ∑ x : Fin (r+d)→Fin 5,
    Polynomial.eval₂ (Nat.castRingHom R) z (stableCoreTerm r (r+d) x)*
    (∏ a ∈ Finset.univ.erase (pivotPort d hd),carryEigenvector z theta (canonicalPortState x a))

/-- The all-theta summand of the actual finite core/tail spectral expansion. -/
def canonicalPureContribution (z theta other ti di : R) (r N d : ℕ) (hN : d<N) : R :=
  ∑ x : Fin (r+d)→Fin 5,
    Polynomial.eval₂ (Nat.castRingHom R) z (stableCoreTerm r (r+d) x)*
    ∏ c : CarryRepresentative N d hN,
      weightedModeAmplitude z theta other ti di (carryTailSize N d hN c-1)
        (fun v => if canonicalStartAllowed x c v then 1 else 0)
        (fun v => if canonicalFinishAllowed x c v then 1 else 0)

/-- This is the paper's pure-contraction identity in rational weighted coordinates. -/
theorem canonicalPureContribution_eq (z theta other bi ti di : R)
    (hb : theta+other=carryB z) (hc : theta*other=carryC z) (hbi : carryB z*bi=1)
    (r N d : ℕ) (hd : 0<d) (hN : d<N) (hbig : 2*d<N) :
    canonicalPureContribution z theta other ti di r N d hN=
      theta^(carrySourceEdgeCount N d)*(bi*ti*di)^(Fintype.card (CarryRepresentative N d hN))*
      (carryB z*(z+theta))*(carryB z*theta)^(carryFixedCount N d hN)*canonicalPureCore z theta r d hd := by
  unfold canonicalPureContribution canonicalPureCore
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : StableCoreAllowed r (r+d) x
  · rw [canonical_pure_component_product z theta other bi ti di hb hc hbi hd hN hbig x hx]
    ring
  · have hz : Polynomial.eval₂ (Nat.castRingHom R) z (stableCoreTerm r (r+d) x)=0 := by
      simp [stableCoreTerm,hx]
    rw [hz,zero_mul,zero_mul,mul_zero]

lemma carryRepresentative_card_phase {N M d : ℕ} (hN : d<N) (hM : d<M)
    (hf : carryFixedCount M d hM=carryFixedCount N d hN) :
    Fintype.card (CarryRepresentative M d hM)=Fintype.card (CarryRepresentative N d hN) := by
  have hn:=carryRepresentative_card_twice N d hN
  have hm:=carryRepresentative_card_twice M d hM
  rw [hf] at hm
  omega

/-- For odd d the actual pure source terms advance geometrically across every
multiplicity, not just along a single residue progression. -/
theorem pureContribution_odd_step (z theta other bi ti di : R)
    (hb : theta+other=carryB z) (hc : theta*other=carryC z) (hbi : carryB z*bi=1)
    (r N d : ℕ) (hd : 0<d) (hN : d<N) (hbig : 2*d<N) (ho : Odd d) :
    canonicalPureContribution z theta other ti di r (N+1) d (by omega)=
      theta*canonicalPureContribution z theta other ti di r N d hN := by
  have hf:=carryFixedCount_odd_step N d hd hN ho
  have he:=carrySourceEdgeCount_odd_step N d hd hbig ho
  have hcard:=carryRepresentative_card_phase hN (show d<N+1 by omega) hf
  rw [canonicalPureContribution_eq z theta other bi ti di hb hc hbi r (N+1) d hd (by omega) (by omega),
    canonicalPureContribution_eq z theta other bi ti di hb hc hbi r N d hd hN hbig,
    hf,hcard,he,pow_succ]
  ring

/-- For even d the two actual parity phases each advance with ratio theta². -/
theorem pureContribution_even_step (z theta other bi ti di : R)
    (hb : theta+other=carryB z) (hc : theta*other=carryC z) (hbi : carryB z*bi=1)
    (r N d : ℕ) (hd : 0<d) (hN : d<N) (hbig : 2*d<N) (heven : Even d) :
    canonicalPureContribution z theta other ti di r (N+2) d (by omega)=
      theta^2*canonicalPureContribution z theta other ti di r N d hN := by
  have hf:=carryFixedCount_parity_step N d hd hN
  have he:=carrySourceEdgeCount_even_step N d hd hbig heven
  have hcard:=carryRepresentative_card_phase hN (show d<N+2 by omega) hf
  rw [canonicalPureContribution_eq z theta other bi ti di hb hc hbi r (N+2) d hd (by omega) (by omega),
    canonicalPureContribution_eq z theta other bi ti di hb hc hbi r N d hd hN hbig,
    hf,hcard,he,pow_add]
  ring

end Ring
end
end SubmittedGenus.FixedPivot
