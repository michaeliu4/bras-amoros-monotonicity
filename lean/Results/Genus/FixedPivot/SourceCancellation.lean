import Results.Genus.FixedPivot.PureCancellation
import Results.Genus.FixedPivot.GenusAssembly
import Results.Genus.FixedPivot.InitialDenominator

/-! Source-exact localized cancellation and polynomial descent of the original numerator. -/
namespace SubmittedGenus.FixedPivot
open Polynomial
open scoped BigOperators
noncomputable section

lemma source_L_dvd_E (d : ℕ) : sourceEmbedding (sourceL d) ∣ sourceEmbedding (sourceE d) :=
  map_dvd sourceEmbedding (sourceL_dvd d)

lemma source_initial_denominator_dvd (d : ℕ) (hd : 0<d) :
    sourceEmbedding (sourceL d) ∣
      sourceEmbedding (Polynomial.eval (1 : Polynomial ℚ) (rationalSourceQ d)) := by
  rw [rationalSourceQ_eval_one hd,map_mul]
  exact dvd_mul_of_dvd_left (source_L_dvd_E d) _

lemma source_phase_sum_dvd {r d : ℕ} (hr : 0<r) (hd : 0<d) :
    sourceEmbedding (sourceL d) ∣
      ∑ k∈Finset.range d,sourceEmbedding (phaseInitialNumerator r (r+d) d (k+1)) := by
  choose M hM using source_phase_numerator_split hr hd
  simp_rw [hM]
  rw [Finset.sum_add_distrib]
  simp_rw [← Finset.mul_sum]
  rw [Finset.sum_add_distrib]
  simp_rw [← Finset.mul_sum]
  apply dvd_add
  · exact dvd_mul_of_dvd_right (source_pure_phase_cancellation r d hd) _
  · rw [← source_E_roots]
    exact dvd_mul_of_dvd_left (source_L_dvd_E d) _

lemma source_all_phases_dvd {r d : ℕ} (hr : 0<r) (hd : 0<d) :
    sourceEmbedding (sourceL d) ∣
      sourceEmbedding (∑ s∈Finset.Icc 1 d,phaseInitialNumerator r (r+d) d s) := by
  rw [map_sum,← sum_fin_succ_eq_Icc (fun s => sourceEmbedding (phaseInitialNumerator r (r+d) d s)) d]
  rw [show (∑ s : Fin d,sourceEmbedding (phaseInitialNumerator r (r+d) d (s.val+1)))=
      ∑ k∈Finset.range d,sourceEmbedding (phaseInitialNumerator r (r+d) d (k+1)) from
    Fin.sum_univ_eq_sum_range (fun s => sourceEmbedding (phaseInitialNumerator r (r+d) d (s+1))) d]
  exact source_phase_sum_dvd hr hd

/-- All actual initial-data terms, including the finite prefix, have the full
cancelled divisor in the exact original quadratic localization. -/
theorem source_initial_numerator_localized {r d : ℕ} (hr : 0<r) (hd : 0<d) :
    sourceEmbedding (sourceL d) ∣ sourceEmbedding (originalInitialNumerator r (r+d) d) := by
  rw [originalInitialNumerator,map_add,map_mul]
  apply dvd_add
  · exact dvd_mul_of_dvd_right (source_initial_denominator_dvd d hd) _
  · exact source_all_phases_dvd hr hd

lemma source_divisibility_descends (N L : Polynomial ℚ)
    (hc : IsCoprime L sourceLocalizationDenominator)
    (h : sourceEmbedding L ∣ sourceEmbedding N) : L ∣ N := by
  obtain ⟨q,hq⟩:=h
  apply source_localization_divisibility N L hc
  refine ⟨q.re,?_⟩
  have hh:=congrArg QuadraticAlgebra.re hq
  simpa [sourceEmbedding,QuadraticAlgebra.re_mul] using hh

/-- Actual polynomial divisibility, with no supplied numerator representation,
localization membership or cancellation hypothesis. -/
theorem originalInitialNumerator_divisible {r d : ℕ} (hr : 0<r) (hd : 0<d) :
    sourceL d ∣ originalInitialNumerator r (r+d) d :=
  source_divisibility_descends _ _ (sourceL_coprime hd) (source_initial_numerator_localized hr hd)

end
end SubmittedGenus.FixedPivot
