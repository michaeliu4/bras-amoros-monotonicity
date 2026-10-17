import Results.Genus.FixedPivot.CanonicalSource
import Results.Genus.FixedPivot.IteratedProgression
import Results.Genus.FixedPivot.RecurrenceAlgebra

/-! Structural recurrence derived from the actual original cap-four raw source. -/
namespace SubmittedGenus.FixedPivot
open RawGraph
open scoped BigOperators
noncomputable section
section Progression
variable {r N d : ℕ} (hN : d<N)

lemma canonicalStartAllowed_iterated (k : ℕ) (x : Fin (r+d)→Fin 5)
    (c : CarryRepresentative N d hN) :
    canonicalStartAllowed x (carryRepresentativeIterated N d hN k c)=canonicalStartAllowed x c := rfl

lemma canonicalFinishAllowed_iterated (k : ℕ) (x : Fin (r+d)→Fin 5)
    (c : CarryRepresentative N d hN) :
    canonicalFinishAllowed x (carryRepresentativeIterated N d hN k c)=canonicalFinishAllowed x c := by
  funext v
  unfold canonicalFinishAllowed
  rw [carryRepresentativeIterated_val,portPartner_iterated N d hN]

lemma canonical_finish_boundary (hbig : 2*d<N) (x : Fin (r+d)→Fin 5)
    (c : CarryRepresentative N d hN) {R : Type*} [CommRing R] :
    0<carryTailSize N d hN c-1 ∨
      (if canonicalFinishAllowed x c 2 then (1 : R) else 0)=
      (if canonicalFinishAllowed x c 1 then (1 : R) else 0) := by
  by_cases hf : c.val=portPartner N d hN c.val
  · right
    simp only [canonicalFinishAllowed,if_pos hf]
    norm_num
  · exact Or.inl (carryTailEdges_positive_paired N d hN hbig c hf)

end Progression
section Ring
variable {R : Type*} [CommRing R]
variable {r N d : ℕ} (hr : 0<r) (hd : 0<d) (hN : d<N) (hbig : r+2*d<N)
variable (z lam mu li mi di : R)
variable (hb : lam+mu=carryB z) (hc : lam*mu=carryC z)
variable (hli : lam*li=1) (hmi : mu*mi=1) (hdi : (lam-mu)*di=1)

def canonicalModeAmplitude (theta other ti deltaInv : R)
    (x : Fin (r+d)→Fin 5) (c : CarryRepresentative N d hN) : R :=
  weightedModeAmplitude z theta other ti deltaInv (carryTailSize N d hN c-1)
    (fun v => if canonicalStartAllowed x c v then 1 else 0)
    (fun v => if canonicalFinishAllowed x c v then 1 else 0)

include hr hd hN hbig hb hc hli hmi hdi in
/-- Actual word partitions on a progression are exact finite products of their
two source modes, not a recurrence fitted or assumed for those partitions. -/
theorem rawPolynomial_progression_modes (k : ℕ) :
    Polynomial.eval₂ (Nat.castRingHom R) z (rawPolynomial (r+(N+k*d)) r (r+d) 4)=
      ∑ x : Fin (r+d)→Fin 5,
        Polynomial.eval₂ (Nat.castRingHom R) z (stableCoreTerm r (r+d) x)*
        ∏ c : CarryRepresentative N d hN,
          (canonicalModeAmplitude hN z lam mu li di x c*(lam^(carryPortArity N d hN c))^k+
           canonicalModeAmplitude hN z mu lam mi (-di) x c*(mu^(carryPortArity N d hN c))^k) := by
  rw [rawPolynomial_eval_eq_canonical_kernels hr hd (show d<N+k*d by omega) (by omega)]
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  rw [← (carryRepresentativeIterated N d hN k).prod_comp]
  apply Finset.prod_congr rfl
  intro c _
  rw [carryTailEdges_iterated N d hN (by omega)]
  simp only [canonicalStartAllowed_iterated,canonicalFinishAllowed_iterated]
  exact weightedCarryKernel_progression z lam mu li mi di hb hc hli hmi hdi _ _ k _ _
    (canonical_finish_boundary hN (by omega) x c)

include hr hd hN hbig hb hc hli hmi hdi in
/-- The submitted degree-(d+1) factored shift recurrence, now proved for the
actual original rawPolynomial on every source progression and at k=0. -/
theorem rawPolynomial_structural_recurrence (n : ℕ) :
    applyAnnihilator (fullModeRoots lam mu d)
      (fun k => Polynomial.eval₂ (Nat.castRingHom R) z
        (rawPolynomial (r+(N+k*d)) r (r+d) 4)) n=0 := by
  have he : (fun k => Polynomial.eval₂ (Nat.castRingHom R) z
      (rawPolynomial (r+(N+k*d)) r (r+d) 4))=
      fun k => ∑ x : Fin (r+d)→Fin 5,
        Polynomial.eval₂ (Nat.castRingHom R) z (stableCoreTerm r (r+d) x)*
        ∏ c : CarryRepresentative N d hN,
          (canonicalModeAmplitude hN z lam mu li di x c*(lam^(carryPortArity N d hN c))^k+
           canonicalModeAmplitude hN z mu lam mi (-di) x c*(mu^(carryPortArity N d hN c))^k) := by
    funext k
    exact rawPolynomial_progression_modes hr hd hN hbig z lam mu li mi di hb hc hli hmi hdi k
  rw [he]
  exact finiteCoreMode_recurrence lam mu (carryPortArity N d hN)
    (carry_port_arity_sum N d hN) _ _ _ n

end Ring
end
end SubmittedGenus.FixedPivot
