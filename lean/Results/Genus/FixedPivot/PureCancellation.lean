import Results.Genus.FixedPivot.SourceNumeratorModes
import Results.Genus.FixedPivot.ModeNumeratorSplit
import Results.Genus.FixedPivot.PurePhaseSum
import Results.Genus.FixedPivot.LocalizedGeometric

/-! Finite signed all-phase cancellation inside the original quadratic localization. -/
namespace SubmittedGenus.FixedPivot
open Polynomial
open scoped BigOperators
noncomputable section

def sourceMixedRatesProduct (d : ℕ) : SourceQuadratic :=
  ∏ j∈(Finset.univ.erase (0 : Fin (d+1))).erase (Fin.last d),
    (1-sourceRates sourceLambda sourceMu d j)

lemma source_phase_numerator_split {r d : ℕ} (hr : 0<r) (hd : 0<d) (k : ℕ) :
    ∃ M : SourceQuadratic,
      sourceEmbedding (phaseInitialNumerator r (r+d) d (k+1))=
        sourceMixedRatesProduct d*((1-sourceMu^d)*
          sourcePurePhase sourceZ sourceLambda sourceMu sourceLambdaInverse sourceDifferenceInverse r d k+
          (1-sourceLambda^d)*sourcePurePhase sourceZ sourceMu sourceLambda sourceMuInverse
            (-sourceDifferenceInverse) r d k)+
        (1-sourceLambda^d)*(1-sourceMu^d)*M := by
  rw [phaseInitialNumerator_modes hr hd]
  obtain ⟨M,hM⟩:=modeNumerator_eval_one_split hd (sourceRates sourceLambda sourceMu d)
    (sourceModeCoefficient (r := r) (show d<r+2*d+1+k by omega) sourceZ sourceLambda sourceMu
      sourceLambdaInverse sourceMuInverse sourceDifferenceInverse)
    (fun pair => sourceModeIndex (show d<r+2*d+1+k by omega) pair.2)
  refine ⟨M,?_⟩
  rw [sourceModeCoefficient_zero,sourceModeCoefficient_last] at hM
  simpa only [phaseModeNumerator,sourceMixedRatesProduct,sourcePurePhase,sourceRates,Fin.val_last,Fin.val_zero,Nat.sub_self,Nat.sub_zero,pow_zero,
    mul_one,one_mul] using hM

lemma phase_geometric_factor (theta : SourceQuadratic) (d : ℕ) :
    1-theta^d=(∑ j∈Finset.range (d/sourceTau d),(theta^(sourceTau d))^j)*
      (1-theta^(sourceTau d)) := by
  have hh:=geom_sum_mul_neg (theta^(sourceTau d)) (d/sourceTau d)
  rw [← pow_mul,sourceTau_mul_div] at hh
  exact hh.symm

/-- The sum of the actual pure endpoint numerators has the complete L_d factor,
including both parity phases and every repeated root multiplicity. -/
theorem source_pure_phase_cancellation (r d : ℕ) (hd : 0<d) :
    sourceEmbedding (sourceL d) ∣
      (1-sourceMu^d)*(∑ k∈Finset.range d,
        sourcePurePhase sourceZ sourceLambda sourceMu sourceLambdaInverse sourceDifferenceInverse r d k)+
      (1-sourceLambda^d)*(∑ k∈Finset.range d,
        sourcePurePhase sourceZ sourceMu sourceLambda sourceMuInverse (-sourceDifferenceInverse) r d k) := by
  have hp:=sourcePurePhase_sum sourceZ sourceLambda sourceMu sourceBInverse sourceLambdaInverse
    sourceDifferenceInverse source_roots_sum source_roots_product source_b_inverse r d hd
  have hm:=sourcePurePhase_sum sourceZ sourceMu sourceLambda sourceBInverse sourceMuInverse
    (-sourceDifferenceInverse) (by rw [add_comm]; exact source_roots_sum)
    (by rw [mul_comm]; exact source_roots_product) source_b_inverse r d hd
  rw [hp,hm,source_L_geometric,phase_geometric_factor sourceMu d,phase_geometric_factor sourceLambda d]
  refine ⟨(1-sourceMu^(sourceTau d))*(∑ k∈Finset.range (sourceTau d),
      sourcePurePhase sourceZ sourceLambda sourceMu sourceLambdaInverse sourceDifferenceInverse r d k)+
    (1-sourceLambda^(sourceTau d))*(∑ k∈Finset.range (sourceTau d),
      sourcePurePhase sourceZ sourceMu sourceLambda sourceMuInverse (-sourceDifferenceInverse) r d k),?_⟩
  ring

end
end SubmittedGenus.FixedPivot
