import Results.Genus.GoldenGraph.Pointwise
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-! Original two-region geometric bound for the omitted pivot sum. -/
namespace SubmittedGenus.GoldenTail
open GoldenSpectral GoldenGraph.Source
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

local notation "R₀" => GoldenSpectral.strongBound
local notation "χ₀" => GoldenSpectral.gapDecay
local notation "t₀" => GoldenSpectral.tiltBound

lemma tilt_pos : 0<t₀ := by norm_num [tiltBound]
lemma tilt_lt_one : t₀<1 := by norm_num [tiltBound]
lemma strong_le_tilt_sq : R₀≤t₀^2 := by norm_num [strongBound,tiltBound]
lemma gap_lt_tilt : χ₀<t₀ := by norm_num [gapDecay,tiltBound]

def lowRatio : ℝ := R₀^2*χ₀/t₀
def highRatio : ℝ := χ₀/t₀
lemma lowRatio_pos : 0<lowRatio := by norm_num [lowRatio,strongBound,gapDecay,tiltBound]
lemma lowRatio_lt_one : lowRatio<1 := by norm_num [lowRatio,strongBound,gapDecay,tiltBound]
lemma highRatio_pos : 0<highRatio := div_pos gapDecay_pos tilt_pos
lemma highRatio_lt_one : highRatio<1 := (div_lt_one tilt_pos).mpr gap_lt_tilt

lemma sum_geometric_injective {I : Type*} (s : Finset I) (f : I→ℕ) (hf : Set.InjOn f s)
    {a : ℝ} (ha : 0≤a) (ha1 : a<1) :
    (∑ i ∈ s,a^(f i))≤(1-a)⁻¹ := by
  classical
  have hs:=hasSum_geometric_of_lt_one ha ha1
  calc
    _=∑ n ∈ s.image f,a^n := (Finset.sum_image hf).symm
    _≤∑' n : ℕ,a^n := hs.summable.sum_le_tsum _ (fun n _ => pow_nonneg ha n)
    _=_ := hs.tsum_eq

lemma floor_tilt_bound (r : ℕ) : R₀^((r-1)/2)*t₀^2≤t₀^r := by
  have h:=pow_le_pow_left₀ strongBound_pos.le strong_le_tilt_sq ((r-1)/2)
  rw [← pow_mul] at h
  have hh:=mul_le_mul_of_nonneg_right h (sq_nonneg t₀)
  rw [← pow_add] at hh
  exact hh.trans (pow_le_pow_of_le_one tilt_pos.le tilt_lt_one.le (by omega))

/-- Replacing the pivot-deletion indicator by one only enlarges the bound. -/
lemma strongExponent_bound (r p : ℕ) :
    R₀^(strongExponent r p)≤R₀^((p-1)/2)*t₀^r/(R₀*t₀^2) := by
  have hn : (r-1)/2+(p-1)/2≤strongExponent r p+1 := by
    unfold strongExponent
    split_ifs <;> omega
  have h:=pow_le_pow_of_le_one strongBound_pos.le strongBound_lt_one.le hn
  rw [pow_succ,pow_add] at h
  have hh:=mul_le_mul_of_nonneg_right h (sq_nonneg t₀)
  have ht:=mul_le_mul_of_nonneg_right (floor_tilt_bound r) (pow_nonneg strongBound_pos.le ((p-1)/2))
  apply (le_div_iff₀ (mul_pos strongBound_pos (pow_pos tilt_pos 2))).mpr
  calc
    R₀^strongExponent r p*(R₀*t₀^2)≤(R₀^((r-1)/2)*R₀^((p-1)/2))*t₀^2 := by
      simpa only [mul_assoc] using hh
    _=(R₀^((r-1)/2)*t₀^2)*R₀^((p-1)/2) := by ring
    _≤t₀^r*R₀^((p-1)/2) := ht
    _=_ := mul_comm _ _

def pivotCharge (r p : ℕ) : ℝ :=
  R₀^(strongExponent r p+2*restrictedExponent r p)*χ₀^(p-r)

lemma pivotCharge_nonneg (r p : ℕ) : 0≤pivotCharge r p :=
  mul_nonneg (pow_nonneg strongBound_pos.le _) (pow_nonneg gapDecay_pos.le _)

lemma pivotCharge_le_floor (r p : ℕ) :
    pivotCharge r p≤(R₀^((p-1)/2)*t₀^r/(R₀*t₀^2))*
      R₀^(2*((p-1)/2-r))*χ₀^(p-r) := by
  unfold pivotCharge restrictedExponent
  rw [pow_add]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (strongExponent_bound r p) (pow_nonneg strongBound_pos.le _)) (pow_nonneg gapDecay_pos.le _)


def lowPrefactor (p : ℕ) : ℝ :=
  χ₀^(p-(p-1)/2)*(R₀*t₀)^((p-1)/2)/(R₀*t₀^2)

def highPrefactor (p : ℕ) : ℝ := R₀^((p-1)/2)*t₀^p/(R₀*t₀^2)

lemma lowPrefactor_nonneg (p : ℕ) : 0≤lowPrefactor p := by
  unfold lowPrefactor
  exact div_nonneg (mul_nonneg (pow_nonneg gapDecay_pos.le _)
    (pow_nonneg (mul_nonneg strongBound_pos.le tilt_pos.le) _))
    (mul_nonneg strongBound_pos.le (sq_nonneg _))

lemma highPrefactor_nonneg (p : ℕ) : 0≤highPrefactor p := by
  unfold highPrefactor
  exact div_nonneg (mul_nonneg (pow_nonneg strongBound_pos.le _) (pow_nonneg tilt_pos.le _))
    (mul_nonneg strongBound_pos.le (sq_nonneg _))

lemma low_region_identity (r J p : ℕ) (hrJ : r≤J) (hJp : J≤p) :
    (R₀^J*t₀^r/(R₀*t₀^2))*R₀^(2*(J-r))*χ₀^(p-r)=
      (χ₀^(p-J)*(R₀*t₀)^J/(R₀*t₀^2))*lowRatio^(J-r) := by
  obtain ⟨h,rfl⟩ : ∃ h,J=r+h := ⟨J-r,by omega⟩
  obtain ⟨s,rfl⟩ : ∃ s,p=r+h+s := ⟨p-(r+h),by omega⟩
  have hs : r+h+s-r=h+s := by omega
  have hs' : r+h+s-(r+h)=s := by omega
  simp only [Nat.add_sub_cancel_left,hs,hs',lowRatio,pow_add,mul_pow,pow_mul,div_pow]
  field_simp [ne_of_gt tilt_pos,ne_of_gt strongBound_pos]

lemma high_region_identity (r J p : ℕ) (hrp : r≤p) :
    R₀^J*t₀^r/(R₀*t₀^2)*χ₀^(p-r)=
      (R₀^J*t₀^p/(R₀*t₀^2))*highRatio^(p-r) := by
  obtain ⟨h,rfl⟩ : ∃ h,p=r+h := ⟨p-r,by omega⟩
  simp only [Nat.add_sub_cancel_left,highRatio,pow_add,div_pow]
  field_simp [ne_of_gt tilt_pos,ne_of_gt strongBound_pos]

lemma pivotCharge_low (r p : ℕ) (hr : r≤(p-1)/2) :
    pivotCharge r p≤lowPrefactor p*lowRatio^((p-1)/2-r) :=
  (pivotCharge_le_floor r p).trans_eq (low_region_identity r ((p-1)/2) p hr (by omega))

lemma pivotCharge_high (r p : ℕ) (hr : (p-1)/2<r) (hrp : r≤p) :
    pivotCharge r p≤highPrefactor p*highRatio^(p-r) := by
  have h:=pivotCharge_le_floor r p
  rw [Nat.sub_eq_zero_of_le hr.le,mul_zero,pow_zero,mul_one] at h
  exact h.trans_eq (high_region_identity r ((p-1)/2) p hrp)

end
end SubmittedGenus.GoldenTail
