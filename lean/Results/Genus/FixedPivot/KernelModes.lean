import Results.Genus.FixedPivot.Projector

/-! Exact rational two-mode decomposition for every source boundary kernel. -/
namespace SubmittedGenus.FixedPivot
open scoped BigOperators
section Ring
variable {R : Type*} [CommRing R]

lemma carryPower_projectors_positive (z lam mu li mi di : R)
    (hb : lam+mu=carryB z) (hc : lam*mu=carryC z)
    (hli : lam*li=1) (hmi : mu*mi=1) (hdi : (lam-mu)*di=1)
    (n : ℕ) (v : Fin 3→R) (i : Fin 3) :
    carryPower z (n+1) v i=
      lam^(n+1)*carryProjector z lam mu li di v i+
      mu^(n+1)*carryProjector z mu lam mi (-di) v i := by
  have hmode : modeRight z lam di (carryStep z v)=modeLeft z lam (-di) (carryStep z v) := by
    funext j
    unfold modeRight modeLeft
    ring
  rw [carryPower_positive_modes z lam mu di hb hc hdi n]
  simp only
  rw [hmode,← carryProjector_positive z lam mu li di hli v i,
    ← carryProjector_positive z mu lam mi (-di) hmi v i]
  simp only [pow_succ]
  ring

/-- Zero-length is valid exactly for the free/loop invariant boundaries; arbitrary
port-to-port boundaries use the source's positive path length. -/
theorem carryPower_projectors (z lam mu li mi di : R)
    (hb : lam+mu=carryB z) (hc : lam*mu=carryC z)
    (hli : lam*li=1) (hmi : mu*mi=1) (hdi : (lam-mu)*di=1)
    (n : ℕ) (v : Fin 3→R) (hboundary : 0<n ∨ v 2=v 1) (i : Fin 3) :
    carryPower z n v i=
      lam^n*carryProjector z lam mu li di v i+
      mu^n*carryProjector z mu lam mi (-di) v i := by
  cases n with
  | succ n => exact carryPower_projectors_positive z lam mu li mi di hb hc hli hmi hdi n v i
  | zero =>
    have hv : v 2=v 1 := hboundary.resolve_left (by omega)
    have hmode : modeRight z lam di v=modeLeft z lam (-di) v := by
      funext j
      unfold modeRight modeLeft
      ring
    rw [carryPower_modes z lam mu di hb hc hdi 0 v hv]
    simp only
    rw [hmode,← carryProjector_invariant z lam mu li di hb hc hli v hv,
      ← carryProjector_invariant z mu lam mi (-di) (by rw [add_comm]; exact hb)
        (by rw [mul_comm]; exact hc) hmi v hv]

/-- The source kernel with one full vertex weight per physical vertex. -/
def weightedCarryKernel (z : R) (n : ℕ) (start finish : Fin 3→R) : R :=
  ∑ i : Fin 3,carryWeight z i*start i*carryPower z n finish i

def weightedModeAmplitude (z theta other ti di : R) (n : ℕ)
    (start finish : Fin 3→R) : R :=
  ∑ i : Fin 3,carryWeight z i*start i*(theta^n*carryProjector z theta other ti di finish i)

/-- Exact m↦m+kd kernel variation at every source phase k≥0. -/
theorem weightedCarryKernel_progression (z lam mu li mi di : R)
    (hb : lam+mu=carryB z) (hc : lam*mu=carryC z)
    (hli : lam*li=1) (hmi : mu*mi=1) (hdi : (lam-mu)*di=1)
    (n a k : ℕ) (start finish : Fin 3→R) (hboundary : 0<n ∨ finish 2=finish 1) :
    weightedCarryKernel z (n+a*k) start finish=
      weightedModeAmplitude z lam mu li di n start finish*(lam^a)^k+
      weightedModeAmplitude z mu lam mi (-di) n start finish*(mu^a)^k := by
  unfold weightedCarryKernel weightedModeAmplitude
  rw [Finset.sum_mul,Finset.sum_mul,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [carryPower_projectors z lam mu li mi di hb hc hli hmi hdi (n+a*k) finish
    (by rcases hboundary with h | h; exact Or.inl (by omega); exact Or.inr h)]
  simp only [pow_add,pow_mul]
  ring

/-- Pure amplitudes factor into the two weighted endpoints, independently of pairing. -/
theorem weightedModeAmplitude_rank_one (z theta other bi ti di : R)
    (hb : theta+other=carryB z) (hc : theta*other=carryC z)
    (hbi : carryB z*bi=1) (n : ℕ) (start finish : Fin 3→R) :
    weightedModeAmplitude z theta other ti di n start finish=
      theta^n*(bi*ti*di)*carryWeightedDot z theta start*carryWeightedDot z theta finish := by
  unfold weightedModeAmplitude
  change _ = theta^n*(bi*ti*di)*(∑ i : Fin 3,carryWeight z i*carryEigenvector z theta i*start i)*carryWeightedDot z theta finish
  rw [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [carryProjector_rank_one z theta other bi ti di hb hc hbi]
  ring

end Ring
end SubmittedGenus.FixedPivot
