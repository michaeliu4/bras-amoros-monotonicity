import Results.Genus.FixedPivot.RankOne
import Results.Genus.FixedPivot.Localization

/-! Denominator-controlled rational projectors, including both endpoint degeneracies. -/
namespace SubmittedGenus.FixedPivot
section Ring
variable {R : Type*} [CommRing R]

def carryProjector (z theta other ti di : R) (v : Fin 3 → R) : Fin 3 → R :=
  fun i => ti*di*(carryStep z (carryStep z v) i-other*carryStep z v i)

lemma carryProjector_positive (z theta other ti di : R)
    (hti : theta*ti=1) (v : Fin 3 → R) (i : Fin 3) :
    theta*carryProjector z theta other ti di v i=modeLeft z other di (carryStep z v) i := by
  unfold carryProjector modeLeft
  calc
    _ = (theta*ti)*(di*(carryStep z (carryStep z v) i-other*carryStep z v i)) := by ring
    _ = _ := by rw [hti,one_mul]

lemma carryProjector_invariant (z theta other ti di : R)
    (hb : theta+other=carryB z) (hc : theta*other=carryC z)
    (hti : theta*ti=1) (v : Fin 3 → R) (hv : v 2=v 1) :
    carryProjector z theta other ti di v=modeLeft z other di v := by
  funext i
  unfold carryProjector modeLeft
  rw [carryStep_second_order z v hv]
  simp only
  rw [← hb,← hc]
  calc
    _ = (theta*ti)*(di*(carryStep z v i-other*v i)) := by ring
    _ = _ := by rw [hti,one_mul]

/-- Rank one with exactly the b, theta and discriminant inverse factors. -/
theorem carryProjector_rank_one (z theta other bi ti di : R)
    (hb : theta+other=carryB z) (hc : theta*other=carryC z)
    (hbi : carryB z*bi=1) (v : Fin 3 → R) (i : Fin 3) :
    carryProjector z theta other ti di v i=
      (bi*ti*di)*carryEigenvector z theta i*carryWeightedDot z theta v := by
  have hh:=carryStep_rank_one_numerator z theta other hb hc v i
  unfold carryProjector
  calc
    _ = (carryB z*bi)*(ti*di*(carryStep z (carryStep z v) i-other*carryStep z v i)) := by rw [hbi,one_mul]
    _ = (bi*ti*di)*(carryB z*(carryStep z (carryStep z v) i-other*carryStep z v i)) := by ring
    _ = _ := by rw [hh]; ring

/-- The rank-one formula remains exact for the zero-edge free-to-loop component. -/
theorem loop_rank_one_modes (z lam mu bi li mi di : R)
    (hb : lam+mu=carryB z) (hc : lam*mu=carryC z)
    (hbi : carryB z*bi=1) (hli : lam*li=1) (hmi : mu*mi=1)
    (hdi : (lam-mu)*di=1) (n : ℕ) (i : Fin 3) :
    carryPower z n loopTerminal i=
      lam^n*((bi*li*di)*carryEigenvector z lam i*(carryB z*lam))+
      mu^n*((bi*mi*(-di))*carryEigenvector z mu i*(carryB z*mu)) := by
  have hswap : (mu-lam)*(-di)=1 := by linear_combination hdi
  have hmode : modeRight z lam di loopTerminal=modeLeft z lam (-di) loopTerminal := by
    funext j
    unfold modeRight modeLeft
    ring
  rw [loopTerminal_modes z lam mu di hb hc hdi n]
  simp only
  rw [hmode,← carryProjector_invariant z lam mu li di hb hc hli loopTerminal rfl,
    ← carryProjector_invariant z mu lam mi (-di) (by rw [add_comm]; exact hb)
      (by rw [mul_comm]; exact hc) hmi loopTerminal rfl]
  rw [carryProjector_rank_one z lam mu bi li di hb hc hbi,
    carryProjector_rank_one z mu lam bi mi (-di) (by rw [add_comm]; exact hb)
      (by rw [mul_comm]; exact hc) hbi,
    loop_endpoint_factor,loop_endpoint_factor]

end Ring

noncomputable section Source
open Polynomial

lemma local_b_unit : IsUnit (localMap (carryB (X : Polynomial ℚ))) := by
  apply IsLocalization.Away.isUnit_of_dvd sourceLocalizationDenominator
  refine dvd_trans ?_ (dvd_mul_right sourceC sourceDelta)
  refine ⟨-X,?_⟩
  unfold sourceC carryC carryB
  ring

/-- The rank-one normalization introduces no denominator outside the manuscript's A. -/
theorem source_rank_one_denominators :
    IsUnit (localMap (carryB (X : Polynomial ℚ))) ∧
    IsUnit (carryRoot (localMap (carryB (X : Polynomial ℚ))) (localMap sourceC)) ∧
    IsUnit (carryRoot (localMap (carryB (X : Polynomial ℚ))) (localMap sourceC)-
      carryConjugate (localMap (carryB (X : Polynomial ℚ))) (localMap sourceC)) :=
  ⟨local_b_unit,source_spectral_units⟩

end Source
end SubmittedGenus.FixedPivot
