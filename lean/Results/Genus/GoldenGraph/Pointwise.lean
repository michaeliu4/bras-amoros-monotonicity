import Results.Genus.GoldenGraph.ComponentBounds
import Results.Genus.GoldenSpectral.GapBudget
import Results.Genus.FixedPivot.OriginalBounds

/-! Original uniform graph-value and fixed-pivot coefficient bounds at q. -/
namespace SubmittedGenus.GoldenGraph.Source
open RawGraph RawGraph.SourceModel RawGraph.Topology
open CapFourMass.ActualComponent GoldenSpectral
open scoped BigOperators
noncomputable section

def strongExponent (r p : ℕ) : ℕ := (r-1)/2+(p-1)/2-(if p=2*r then 0 else 1)
def restrictedExponent (r p : ℕ) : ℕ := (p-1)/2-r

/-- The literal submitted graph-value multiplier, retaining the integer gap
exponent when p−r<16. -/
def uniformRawBound (r p : ℕ) : ℝ :=
  pathInflation^3*radius^8*alphabetMass*strongBound^(strongExponent r p+2*restrictedExponent r p)*
    gapDecay^(((p-r : ℕ) : ℤ)-16)

lemma uniformRawBound_nonneg (r p : ℕ) : 0≤uniformRawBound r p := by
  unfold uniformRawBound
  apply mul_nonneg
  · exact mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg pathInflation_pos.le _)
      (pow_nonneg radius_pos.le _)) (by linarith [alphabetMass_gt_one])) (pow_nonneg strongBound_pos.le _)
  · exact (zpow_pos gapDecay_pos _).le

/-- Submitted Proposition raw:pointwise for the actual source polynomial,
for all m>p, without a graph-mass or recurrence premise. -/
theorem raw_eval_le_uniform {m r p : ℕ} (hp : Parameters m r p 4) :
    Polynomial.eval₂ (Nat.castRingHom ℝ) radius (rawPolynomial m r p 4)≤uniformRawBound r p := by
  have hb:=sourceBoundaryMass_le hp
  have hk:=pow_le_pow_right₀ pathInflation_one_le (source_path_count_le_three hp)
  have hj:=paid_count_original_gap_bound (p-r) (sourcePaidRunCount hp) (source_paid_run_count_lower hp)
  have he:=mul_le_mul hb hk (pow_nonneg pathInflation_pos.le _) (by linarith [alphabetMass_gt_one])
  have hR:=pow_nonneg strongBound_pos.le (totalStrongLength m r p+2*totalRestrictedLength m r p)
  have he':=mul_le_mul (mul_le_mul_of_nonneg_right he hR) hj
    (pow_nonneg paidCost_pos.le _) (mul_nonneg (mul_nonneg (by linarith [alphabetMass_gt_one])
      (pow_nonneg pathInflation_pos.le _)) hR)
  have h:= (raw_eval_le_paid_product hp).trans (mul_le_mul_of_nonneg_left he' (pow_nonneg radius_pos.le 8))
  rw [total_strong_formula hp,total_restricted_formula hp] at h
  exact h.trans_eq (by unfold uniformRawBound strongExponent restrictedExponent; ring)

/-- Discharges the sole actual graph-mass premise of the completed submitted
signed numerator and inverse-certificate argument. -/
theorem sourceRawMass_le_uniform {r p m : ℕ} (hr : 0<r) (hrp : r<p) (hm : p<m) :
    FixedPivot.sourceRawMass m r p≤uniformRawBound r p := by
  exact raw_eval_le_uniform ⟨hr,hrp,hm,Or.inl rfl⟩

/-- Original coefficient multiplier for every actual fixed-pivot coefficient. -/
theorem fixedPivotCoeff_le_uniform {r p : ℕ} (hr : 0<r) (hrp : r<p) (g : ℕ) :
    (RawGraph.SignedCounterexample.fixedPivotCoeff r p g : ℝ)≤
      945*(3*(p-r)^2+7*p+6 : ℕ)*uniformRawBound r p*(Nat.fib g : ℝ) :=
  FixedPivot.original_fixedPivot_coefficient_bound hr hrp (uniformRawBound r p)
    (fun _ hm => sourceRawMass_le_uniform hr hrp hm) g

end
end SubmittedGenus.GoldenGraph.Source
