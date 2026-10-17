import Results.Genus.CapFourMass.GenuineSource
import Results.Genus.CapFourMass.SourceMixed
import Results.Genus.CapFourMass.NormalizedFeedback

/-! Actual genuine population to the original short/contracted-long master sum. -/
noncomputable section
open scoped BigOperators
namespace SubmittedGenus.CapFourMass.GenuineSource
open OriginalPopulations
attribute [local instance] Classical.propDecidable

lemma validPartition_eq_bounded (q : PivotParameters) (z : ℝ) :
    rawPartition q z = ∑ x : Fin (q.m-1) → Fin 5,
      if RawGraph.SourceModel.Admissible q.r q.p 4 (RawGraph.boundedWord x) ∧
        KunzWord.Valid (RawGraph.boundedWord x)
      then z ^ RawGraph.genus (RawGraph.boundedWord x) else 0 := by
  classical
  let P (x : Fin (q.m-1) → Fin 5) :=
    RawGraph.RawAdmissible q.r q.p 4 (RawGraph.boundedWord x) ∧ KunzWord.Valid (RawGraph.boundedWord x)
  calc
    rawPartition q z = ∑ x : {x : Fin (q.m-1) → Fin 5 // P x},
        z ^ RawGraph.genus (RawGraph.boundedWord x.val) :=
      ((boundedValidEquiv q).sum_comp
        (fun x : ValidFourWord q => z ^ RawGraph.genus x.val)).symm
    _ = ∑ x : Fin (q.m-1) → Fin 5, if P x then z ^ RawGraph.genus (RawGraph.boundedWord x) else 0 := by
      change (∑ x : {x : Fin (q.m-1) → Fin 5 // P x},
        (fun x => z ^ RawGraph.genus (RawGraph.boundedWord x)) x.val) = _
      rw [← Finset.sum_subtype (Finset.univ.filter P) (by simp)
        (fun x => z ^ RawGraph.genus (RawGraph.boundedWord x)), Finset.sum_filter]
    _ = _ := by simp only [P, RawGraph.SourceModel.raw_iff_compiled]

def masterTerm (q : PivotParameters) : ℝ :=
  if h : q.m ≤ 2*q.p then
    Polynomial.eval₂ (Nat.castRingHom ℝ) radius (RawGraph.rawPolynomial q.m q.r q.p 4)
  else feedbackT^(feedbackExponent q.r q.p)*feedbackBeta^(feedbackCount q.m q.p)*
    (sourcePure q.r (q.m-q.r) (q.p-q.r) (by have := q.valid; unfold RawGraph.Parameters at this; omega) +
     sourceMixed q.r (q.m-q.r) (q.p-q.r) (by have := q.valid; unfold RawGraph.Parameters at this; omega))

lemma validPartition_le_raw (q : PivotParameters) {z : ℝ} (hz : 0 ≤ z) :
    rawPartition q z ≤ Polynomial.eval₂ (Nat.castRingHom ℝ) z (RawGraph.rawPolynomial q.m q.r q.p 4) := by
  rw [validPartition_eq_bounded, LocalPartitions.raw_partition_eval]
  simp_rw [← LocalPartitions.genus_weight]
  apply Finset.sum_le_sum
  intro x hx
  split_ifs <;> simp_all <;> positivity

lemma validPartition_le_master (q : PivotParameters) : rawPartition q radius ≤ masterTerm q := by
  have hp := q.valid
  rcases hp with ⟨hr, hrp, hpm, ha⟩
  unfold masterTerm
  split_ifs with hm
  · exact validPartition_le_raw q radius_pos.le
  · rw [validPartition_eq_bounded]
    have hc := ActualContraction.valid_partition_bound hr hrp radius_pos (m := q.m)
    have hs := rawPolynomial_le_source_pure_mixed (r := q.r) (N := q.m-q.r)
      (d := q.p-q.r) (by omega) (by omega) (by omega) (by omega)
    have he1 : q.r+(q.m-q.r)=q.m := by omega
    have he2 : q.r+(q.p-q.r)=q.p := by omega
    rw [he1,he2] at hs
    have hnon : 0 ≤ feedbackT^(feedbackExponent q.r q.p)*feedbackBeta^(feedbackCount q.m q.p) := by
      apply mul_nonneg
      · exact pow_nonneg (div_nonneg feedbackGamma_bounds.1.le feedbackBeta_bounds.1.le) _
      · exact pow_nonneg feedbackBeta_bounds.1.le _
    have hc' : (∑ x : Fin (q.m-1) → Fin 5,
      if RawGraph.SourceModel.Admissible q.r q.p 4 (RawGraph.boundedWord x) ∧
        KunzWord.Valid (RawGraph.boundedWord x)
      then radius ^ RawGraph.genus (RawGraph.boundedWord x) else 0) ≤
      feedbackT^(feedbackExponent q.r q.p)*feedbackBeta^(feedbackCount q.m q.p)*
      Polynomial.eval₂ (Nat.castRingHom ℝ) radius (RawGraph.rawPolynomial q.m q.r q.p 4) := by
      simpa only [feedbackT,feedbackGamma,feedbackBeta,feedbackExponent,feedbackCount,mul_comm] using hc
    exact hc'.trans (mul_le_mul_of_nonneg_left hs hnon)

/-- Summability is required explicitly; divergent tsum defaults cannot prove a mass bound. -/
theorem genuine_mass_le_master (hs : Summable masterTerm) :
    Summable (fun g => (countFour g : ℝ)*radius^g) ∧ massFour radius ≤ ∑' q, masterTerm q := by
  have hv := hs.of_nonneg_of_le (rawPartition_nonneg radius_pos.le) validPartition_le_master
  have hg := genuine_mass_le_raw radius_pos.le hv
  exact ⟨hg.1, hg.2.trans (hv.tsum_le_tsum validPartition_le_master hs)⟩

#print axioms genuine_mass_le_master
end SubmittedGenus.CapFourMass.GenuineSource
