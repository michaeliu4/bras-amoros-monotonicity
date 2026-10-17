import Results.Genus.GoldenTail.RegionSums
import Results.Genus.GoldenTail.Numeric

/-! Actual signed coefficient multipliers and the original positive prefactor. -/
namespace SubmittedGenus.GoldenTail
open GoldenSpectral GoldenGraph.Source InverseCertificates
open scoped BigOperators
noncomputable section

local notation "R₀" => GoldenSpectral.strongBound
local notation "χ₀" => GoldenSpectral.gapDecay
local notation "t₀" => GoldenSpectral.tiltBound

def coefficientMultiplier (r p : ℕ) : ℝ :=
  945*(3*(p-r)^2+7*p+6 : ℕ)*uniformRawBound r p

def coefficientPrefactor : ℝ :=
  945*radius^8*alphabetMass*pathInflation^3/χ₀^16

def upperPrefactor : ℝ :=
  945*(qUpper : ℝ)^8*(s4Upper : ℝ)*pathInflation^3/χ₀^16

def pivotPolynomial (p : ℕ) : ℝ := 3*(p : ℝ)^2+7*p+6

def rowMajorant (p : ℕ) : ℝ := pivotPolynomial p*pivotRegionBound p

lemma coefficientPrefactor_nonneg : 0≤coefficientPrefactor := by
  unfold coefficientPrefactor
  have hq:=radius_pos
  have hk:=pathInflation_pos
  have ha:=alphabetMass_gt_one
  have hc:=gapDecay_pos
  positivity

lemma coefficientMultiplier_nonneg (r p : ℕ) : 0≤coefficientMultiplier r p := by
  exact mul_nonneg (by positivity) (uniformRawBound_nonneg r p)

lemma pivotPolynomial_nonneg (p : ℕ) : 0≤pivotPolynomial p := by unfold pivotPolynomial; positivity
lemma rowMajorant_nonneg (p : ℕ) : 0≤rowMajorant p :=
  mul_nonneg (pivotPolynomial_nonneg p) (pivotRegionBound_nonneg p)

lemma coefficientMultiplier_eq (r p : ℕ) :
    coefficientMultiplier r p=coefficientPrefactor*(3*((p-r : ℕ) : ℝ)^2+7*p+6)*pivotCharge r p := by
  unfold coefficientMultiplier coefficientPrefactor uniformRawBound pivotCharge
  rw [zpow_sub₀ (ne_of_gt gapDecay_pos)]
  simp only [zpow_natCast,zpow_ofNat]
  push_cast
  ring

lemma coefficientMultiplier_le (r p : ℕ) :
    coefficientMultiplier r p≤coefficientPrefactor*pivotPolynomial p*pivotCharge r p := by
  rw [coefficientMultiplier_eq]
  have hd : ((p-r : ℕ) : ℝ)≤(p : ℝ) := by exact_mod_cast Nat.sub_le p r
  have hs:=pow_le_pow_left₀ (by positivity : 0≤((p-r : ℕ) : ℝ)) hd 2
  have hpoly : 3*((p-r : ℕ) : ℝ)^2+7*p+6≤pivotPolynomial p := by unfold pivotPolynomial; nlinarith
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpoly coefficientPrefactor_nonneg)
    (pivotCharge_nonneg r p)

lemma coefficientMultiplier_row (p : ℕ) (hp : 1≤p) :
    (∑ r ∈ Finset.Ico 1 p,coefficientMultiplier r p)≤coefficientPrefactor*rowMajorant p := by
  calc
    _≤∑ r ∈ Finset.Ico 1 p,coefficientPrefactor*pivotPolynomial p*pivotCharge r p :=
      Finset.sum_le_sum (fun r _ => coefficientMultiplier_le r p)
    _=coefficientPrefactor*pivotPolynomial p*∑ r ∈ Finset.Ico 1 p,pivotCharge r p :=
      (Finset.mul_sum _ _ _).symm
    _≤coefficientPrefactor*pivotPolynomial p*pivotRegionBound p :=
      mul_le_mul_of_nonneg_left (pivotCharge_sum_le p hp)
        (mul_nonneg coefficientPrefactor_nonneg (pivotPolynomial_nonneg p))
    _=_ := mul_assoc _ _ _

lemma alphabetMass_le_upper : alphabetMass≤(s4Upper : ℝ) := by
  have hq : radius≤(qUpper : ℝ) := q_le_qUpper
  have hh : alphabetMass≤∑ i : State,(qUpper : ℝ)^(i.val+1) := by
    apply Finset.sum_le_sum
    intro i _
    exact pow_le_pow_left₀ radius_pos.le hq _
  have he : (∑ i : State,(qUpper : ℝ)^(i.val+1))=(s4Upper : ℝ) := by
    simp only [s4Upper,Rat.cast_add,Rat.cast_pow]
    norm_num [Fin.sum_univ_succ]
    ring
  exact hh.trans_eq he

lemma coefficientPrefactor_le_upper : coefficientPrefactor≤upperPrefactor := by
  unfold coefficientPrefactor upperPrefactor
  have hq : radius^8≤(qUpper : ℝ)^8 := pow_le_pow_left₀ radius_pos.le q_le_qUpper 8
  have he:=mul_le_mul (mul_le_mul_of_nonneg_left hq (by norm_num : (0:ℝ)≤945)) alphabetMass_le_upper
    (by linarith [alphabetMass_gt_one]) (by positivity : 0≤945*(qUpper : ℝ)^8)
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right he (pow_nonneg pathInflation_pos.le _))
    (pow_nonneg gapDecay_pos.le _)

end
end SubmittedGenus.GoldenTail
