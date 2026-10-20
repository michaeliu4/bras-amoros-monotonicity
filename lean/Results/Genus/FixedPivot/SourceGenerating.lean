import Results.Genus.FixedPivot.SourceRecurrence
import Results.Genus.FixedPivot.ProgressionPolynomial
import Results.Genus.FixedPivot.ProgressionNumerator

/-! Source-exact rational generating series in the formal multiplicity-progression variable. -/
namespace SubmittedGenus.FixedPivot
open RawGraph
open scoped BigOperators
noncomputable section
section Ring
variable {R : Type*} [CommRing R]
variable {r N d : ℕ} (hr : 0<r) (hd : 0<d) (hN : d<N) (hbig : r+2*d<N)
variable (z lam mu li mi di : R)
variable (hb : lam+mu=carryB z) (hc : lam*mu=carryC z)
variable (hli : lam*li=1) (hmi : mu*mi=1) (hdi : (lam-mu)*di=1)

abbrev SourceModeAssignment (r N d : ℕ) (hN : d<N) :=
  (Fin (r+d)→Fin 5)×(CarryRepresentative N d hN→Bool)

def sourceModeIndex (choice : CarryRepresentative N d hN→Bool) : Fin (d+1) :=
  ⟨mixedModeDegree (carryPortArity N d hN) choice,by
    have hh:=modeDegrees_sum (carryPortArity N d hN) choice
    rw [carry_port_arity_sum] at hh
    exact Nat.lt_succ_of_le ((Nat.le_add_left (mixedModeDegree (carryPortArity N d hN) choice)
      (pureModeDegree (carryPortArity N d hN) choice)).trans_eq hh)⟩

def sourceModeCoefficient (pair : SourceModeAssignment r N d hN) : R :=
  Polynomial.eval₂ (Nat.castRingHom R) z (stableCoreTerm r (r+d) pair.1)*
    (∏ c : CarryRepresentative N d hN,
      if pair.2 c then canonicalModeAmplitude hN z mu lam mi (-di) pair.1 c
      else canonicalModeAmplitude hN z lam mu li di pair.1 c)

def sourceProgressionSeries : PowerSeries R :=
  PowerSeries.mk (fun k => Polynomial.eval₂ (Nat.castRingHom R) z
    (rawPolynomial (r+(N+k*d)) r (r+d) 4))

def sourceRates (lam mu : R) (d : ℕ) : Fin (d+1)→R := fun j => lam^(d-j.val)*mu^j.val

include hr hd hN hbig hb hc hli hmi hdi in
lemma sourceProgressionSeries_modes :
    sourceProgressionSeries (r := r) (N := N) (d := d) z=
      finiteModeSeries (sourceRates lam mu d) (sourceModeCoefficient (r := r) hN z lam mu li mi di)
        (fun pair => sourceModeIndex hN pair.2) := by
  apply PowerSeries.ext
  intro k
  simp only [sourceProgressionSeries,finiteModeSeries,PowerSeries.coeff_mk]
  rw [rawPolynomial_progression_modes hr hd hN hbig z lam mu li mi di hb hc hli hmi hdi,
    finiteCoreMode_expansion]
  apply Finset.sum_congr rfl
  intro pair _
  change _=sourceModeCoefficient (r := r) hN z lam mu li mi di pair*
    (lam^(d-mixedModeDegree (carryPortArity N d hN) pair.2)*
      mu^(mixedModeDegree (carryPortArity N d hN) pair.2))^k
  rw [(modeRate_source_index lam mu (carryPortArity N d hN)
    (carry_port_arity_sum N d hN) pair.2).2]
  rfl

include hb hc in
lemma sourceRates_denominator :
    modeDenominator (sourceRates lam mu d)=progressionPolynomial (carryB z) (carryC z) d := by
  rw [progressionPolynomial_eq_roots _ _ lam mu hb hc]
  unfold modeDenominator sourceRates linearModeDenominator
  exact Fin.prod_univ_eq_prod_range (fun j => 1-Polynomial.C (lam^(d-j)*mu^j)*Polynomial.X) (d+1)

include hr hd hN hbig hb hc hli hmi hdi in
/-- Every actual source progression has its original degree≤d numerator in y.
The series is formal; no numerical or asymptotic summation hypothesis is used. -/
theorem sourceProgressionSeries_rational :
    ∃ A : Polynomial R,A.natDegree≤d ∧
      (progressionPolynomial (carryB z) (carryC z) d : PowerSeries R)*
        sourceProgressionSeries (r := r) (N := N) (d := d) z=(A : PowerSeries R) := by
  let rates:=sourceRates lam mu d
  let coeff:=sourceModeCoefficient (r := r) hN z lam mu li mi di
  let index:=fun pair : SourceModeAssignment r N d hN => sourceModeIndex hN pair.2
  refine ⟨modeNumerator rates coeff index,modeNumerator_natDegree rates coeff index,?_⟩
  rw [sourceProgressionSeries_modes hr hd hN hbig z lam mu li mi di hb hc hli hmi hdi,
    ← sourceRates_denominator z lam mu hb hc]
  exact finiteModeSeries_rational rates coeff index

end Ring
end
end SubmittedGenus.FixedPivot
