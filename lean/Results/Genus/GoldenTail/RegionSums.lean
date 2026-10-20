import Results.Genus.GoldenTail.PivotRegions

/-! Complete finite pivot-row bounds, using the original two geometric regions. -/
namespace SubmittedGenus.GoldenTail
open GoldenSpectral GoldenGraph.Source
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

local notation "R₀" => GoldenSpectral.strongBound
local notation "χ₀" => GoldenSpectral.gapDecay
local notation "t₀" => GoldenSpectral.tiltBound

lemma low_region_sum (p : ℕ) :
    (∑ r ∈ Finset.Ico 1 ((p-1)/2+1),pivotCharge r p)≤lowPrefactor p/(1-lowRatio) := by
  have hinj : Set.InjOn (fun r : ℕ => (p-1)/2-r) (Finset.Ico 1 ((p-1)/2+1)) := by
    intro r hr s hs he
    dsimp only at he
    have hr':=(Finset.mem_Ico.mp hr).2
    have hs':=(Finset.mem_Ico.mp hs).2
    omega
  calc
    _≤∑ r ∈ Finset.Ico 1 ((p-1)/2+1),lowPrefactor p*lowRatio^((p-1)/2-r) := by
      apply Finset.sum_le_sum
      intro r hr
      exact pivotCharge_low r p (by have:=(Finset.mem_Ico.mp hr).2; omega)
    _=lowPrefactor p*∑ r ∈ Finset.Ico 1 ((p-1)/2+1),lowRatio^((p-1)/2-r) :=
      (Finset.mul_sum _ _ _).symm
    _≤lowPrefactor p*(1-lowRatio)⁻¹ := mul_le_mul_of_nonneg_left
      (sum_geometric_injective _ _ hinj lowRatio_pos.le lowRatio_lt_one) (lowPrefactor_nonneg p)
    _=_ := (div_eq_mul_inv _ _).symm

lemma high_region_sum (p : ℕ) :
    (∑ r ∈ Finset.Ico ((p-1)/2+1) p,pivotCharge r p)≤highPrefactor p/(t₀/χ₀-1) := by
  have hinj : Set.InjOn (fun r : ℕ => p-r-1) (Finset.Ico ((p-1)/2+1) p) := by
    intro r hr s hs he
    dsimp only at he
    have hr':=(Finset.mem_Ico.mp hr).2
    have hs':=(Finset.mem_Ico.mp hs).2
    omega
  have hratio : highRatio*(1-highRatio)⁻¹=(t₀/χ₀-1)⁻¹ := by
    norm_num [highRatio,tiltBound,gapDecay]
  calc
    _≤∑ r ∈ Finset.Ico ((p-1)/2+1) p,highPrefactor p*highRatio^(p-r) := by
      apply Finset.sum_le_sum
      intro r hr
      exact pivotCharge_high r p (by have:=(Finset.mem_Ico.mp hr).1; omega)
        (Finset.mem_Ico.mp hr).2.le
    _=highPrefactor p*highRatio*∑ r ∈ Finset.Ico ((p-1)/2+1) p,highRatio^(p-r-1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      have he : p-r=p-r-1+1 := by have:=(Finset.mem_Ico.mp hr).2; omega
      conv_lhs => rw [he,pow_succ]
      ring
    _≤highPrefactor p*highRatio*(1-highRatio)⁻¹ := mul_le_mul_of_nonneg_left
      (sum_geometric_injective _ _ hinj highRatio_pos.le highRatio_lt_one)
      (mul_nonneg (highPrefactor_nonneg p) highRatio_pos.le)
    _=highPrefactor p/(t₀/χ₀-1) := by
      rw [mul_assoc,hratio]
      exact (div_eq_mul_inv _ _).symm

def pivotRegionBound (p : ℕ) : ℝ := lowPrefactor p/(1-lowRatio)+highPrefactor p/(t₀/χ₀-1)

/-- The entire original inner pivot sum is bounded, including an empty low
or high region and without extending any source multiplicity range. -/
theorem pivotCharge_sum_le (p : ℕ) (hp : 1≤p) :
    (∑ r ∈ Finset.Ico 1 p,pivotCharge r p)≤pivotRegionBound p := by
  rw [← Finset.sum_Ico_consecutive (fun r => pivotCharge r p)
    (show 1≤(p-1)/2+1 by omega) (show (p-1)/2+1≤p by omega)]
  exact add_le_add (low_region_sum p) (high_region_sum p)

lemma pivotRegionBound_nonneg (p : ℕ) : 0≤pivotRegionBound p := by
  unfold pivotRegionBound
  apply add_nonneg
  · exact div_nonneg (lowPrefactor_nonneg p) (sub_pos.mpr lowRatio_lt_one).le
  · exact div_nonneg (highPrefactor_nonneg p) (by norm_num [tiltBound,gapDecay])

end
end SubmittedGenus.GoldenTail
