import Results.Genus.FixedPivot.CorrectedIdentity

/-! The original finite-prefix mass bound, without evaluating the divergent complete F at q. -/
namespace SubmittedGenus.FixedPivot
open Polynomial WeightedSeries InverseCertificates
open scoped BigOperators
noncomputable section

def rawPolynomialReal (m r p : ℕ) : Polynomial ℝ :=
  (RawGraph.rawPolynomial m r p 4).map (Nat.castRingHom ℝ)

def sourceRawMass (m r p : ℕ) : ℝ :=
  Polynomial.eval₂ (Nat.castRingHom ℝ) q (RawGraph.rawPolynomial m r p 4)

lemma rawPolynomialReal_coeff_nonneg (m r p g : ℕ) : 0≤(rawPolynomialReal m r p).coeff g := by
  simp [rawPolynomialReal]

lemma rawPolynomialReal_coeff_zero {m r p g : ℕ} (h : g<m+5) :
    (rawPolynomialReal m r p).coeff g=0 := by
  simp only [rawPolynomialReal,Polynomial.coeff_map]
  rw [RawGraph.SignedCounterexample.coeff_zero_of_multiplicity h,map_zero]

lemma rawPolynomialReal_norm (m r p : ℕ) :
    polynomialNorm q (rawPolynomialReal m r p)=sourceRawMass m r p := by
  rw [polynomialNorm_eq_eval _ (rawPolynomialReal_coeff_nonneg m r p)]
  exact Polynomial.eval_map _ _

lemma fixedPivotSeriesReal_coeff (r p g : ℕ) :
    PowerSeries.coeff g (fixedPivotSeriesReal r p)=
      ∑ m∈Finset.range (g+1),(rawPolynomialReal m r p).coeff g := by
  simp [fixedPivotSeriesReal,fixedPivotSeriesQ_coeff,rawPolynomialQ,rawPolynomialReal]

lemma fixedPivotSeriesReal_coeff_nonneg (r p g : ℕ) :
    0≤PowerSeries.coeff g (fixedPivotSeriesReal r p) := by
  rw [fixedPivotSeriesReal_coeff]
  exact Finset.sum_nonneg (fun m _ => rawPolynomialReal_coeff_nonneg m r p g)

lemma fixedPivotSeriesReal_coeff_range (r p g M : ℕ) (hg : g<M+5) :
    PowerSeries.coeff g (fixedPivotSeriesReal r p)=
      ∑ m∈Finset.range M,(rawPolynomialReal m r p).coeff g := by
  rw [fixedPivotSeriesReal_coeff]
  by_cases h : g+1≤M
  · apply Finset.sum_subset (Finset.range_mono h)
    intro m hm hn
    apply rawPolynomialReal_coeff_zero
    simp only [Finset.mem_range] at *
    omega
  · symm
    apply Finset.sum_subset (Finset.range_mono (by omega : M≤g+1))
    intro m hm hn
    apply rawPolynomialReal_coeff_zero
    simp only [Finset.mem_range] at *
    omega

lemma rawPolynomialReal_zero {m r p : ℕ} (hm : m≤p) : rawPolynomialReal m r p=0 := by
  unfold rawPolynomialReal
  rw [RawGraph.rawPolynomial_invalid (by unfold RawGraph.Parameters; omega),Polynomial.map_zero]

/-- Fewer than N multiplicities contribute through genus N; each contributes
at most its finite graph mass at q. This is the original finite-prefix argument. -/
theorem fixedPivotSeriesReal_prefix_bound (r p N : ℕ) (B : ℝ)
    (hB : ∀ m,p<m → sourceRawMass m r p≤B) :
    prefixNorm q (fun n => PowerSeries.coeff n (fixedPivotSeriesReal r p)) (N+1)≤(N : ℝ)*B := by
  have hBn : 0≤B := (weightedNorm_nonneg q_nonneg _).trans
    ((rawPolynomialReal_norm (p+1) r p).trans_le (hB (p+1) (by omega)))
  have hmass (m : ℕ) : polynomialNorm q (rawPolynomialReal m r p)≤B := by
    by_cases hm : p<m
    · rw [rawPolynomialReal_norm]
      exact hB m hm
    · rw [rawPolynomialReal_zero (by omega)]
      simpa [polynomialNorm,weightedNorm,absWeightedTerm] using hBn
  have hpref (m : ℕ) :
      ∑ g∈Finset.range (N+1),(rawPolynomialReal m r p).coeff g*q^g≤B := by
    have hh:=(polynomial_summable q (rawPolynomialReal m r p)).prefixNorm_le q_nonneg (N+1)
    simp only [prefixNorm,absWeightedTerm,abs_of_nonneg (rawPolynomialReal_coeff_nonneg m r p _)] at hh
    exact hh.trans (hmass m)
  unfold prefixNorm absWeightedTerm
  simp only [abs_of_nonneg (fixedPivotSeriesReal_coeff_nonneg r p _)]
  calc
    _=∑ g∈Finset.range (N+1),∑ m∈Finset.range N,(rawPolynomialReal m r p).coeff g*q^g := by
      apply Finset.sum_congr rfl
      intro g hg
      rw [fixedPivotSeriesReal_coeff_range r p g N (by have:=Finset.mem_range.mp hg; omega),Finset.sum_mul]
    _=∑ m∈Finset.range N,∑ g∈Finset.range (N+1),(rawPolynomialReal m r p).coeff g*q^g :=
      Finset.sum_comm
    _≤∑ _m∈Finset.range N,B := Finset.sum_le_sum (fun m _ => hpref m)
    _=(N : ℝ)*B := by simp

end
end SubmittedGenus.FixedPivot
