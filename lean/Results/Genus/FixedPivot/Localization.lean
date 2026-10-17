import Results.Genus.FixedPivot.QuadraticModes
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.RingTheory.Coprime.Basic

/-!
# The exact original denominator localization
A=Q[z,(c Delta)^-1] is constructed explicitly. Both spectral inverses live in
its quadratic algebra, and localization divisibility descends with every root
multiplicity whenever the stated polynomial coprimality has been established.
-/
noncomputable section
namespace SubmittedGenus.FixedPivot
open Polynomial

def sourceC : Polynomial ℚ := carryC X
def sourceDelta : Polynomial ℚ := carryDiscriminant (carryB X) (carryC X)
def sourceLocalizationDenominator : Polynomial ℚ := sourceC*sourceDelta

abbrev SourceLocalization := Localization.Away sourceLocalizationDenominator

def localMap : Polynomial ℚ →+* SourceLocalization := algebraMap _ _

lemma sourceLocalizationDenominator_ne_zero : sourceLocalizationDenominator ≠ 0 := by
  intro h
  have hh:=congrArg (Polynomial.eval (1 : ℚ)) h
  norm_num [sourceLocalizationDenominator,sourceC,sourceDelta,
    carryDiscriminant,carryB,carryC] at hh

lemma localMap_injective : Function.Injective localMap := by
  apply IsLocalization.injective (M := Submonoid.powers sourceLocalizationDenominator)
  rintro p ⟨n,rfl⟩
  exact mem_nonZeroDivisors_of_ne_zero (pow_ne_zero n sourceLocalizationDenominator_ne_zero)

instance : CharZero SourceLocalization where
  cast_injective := by
    intro n m h
    apply Nat.cast_injective (R := Polynomial ℚ)
    apply localMap_injective
    simpa only [map_natCast] using h

lemma local_c_unit : IsUnit (localMap sourceC) :=
  IsLocalization.Away.isUnit_of_dvd sourceLocalizationDenominator (dvd_mul_right _ _)

lemma local_delta_unit : IsUnit (localMap sourceDelta) :=
  IsLocalization.Away.isUnit_of_dvd sourceLocalizationDenominator (dvd_mul_left _ _)

lemma local_z_unit : IsUnit (localMap (X : Polynomial ℚ)) := by
  apply IsLocalization.Away.isUnit_of_dvd sourceLocalizationDenominator
  refine dvd_trans ?_ (dvd_mul_right sourceC sourceDelta)
  refine ⟨-X^2-X^3, ?_⟩
  unfold sourceC carryC
  ring

abbrev SourceQuadratic := CarryAlgebra (localMap (carryB (X : Polynomial ℚ))) (localMap sourceC)

/-- The source root and root-difference denominators are units in exactly A[lambda]. -/
theorem source_spectral_units :
    IsUnit (carryRoot (localMap (carryB (X : Polynomial ℚ))) (localMap sourceC)) ∧
    IsUnit (carryRoot (localMap (carryB (X : Polynomial ℚ))) (localMap sourceC)-
      carryConjugate (localMap (carryB (X : Polynomial ℚ))) (localMap sourceC)) := by
  refine ⟨carryRoot_isUnit _ _ local_c_unit, carryRoot_difference_isUnit _ _ ?_⟩
  have hh : carryDiscriminant (localMap (carryB (X : Polynomial ℚ))) (localMap sourceC)=
      localMap sourceDelta := by simp only [sourceDelta,sourceC,carryDiscriminant,map_sub,map_pow,map_mul,map_ofNat]
  rw [hh]
  exact local_delta_unit

/-- Conjugation invariants are precisely the original localization coefficient ring. -/
theorem source_fixed_ring (x : SourceQuadratic) :
    star x=x ↔ ∃ r : SourceLocalization, algebraMap SourceLocalization SourceQuadratic r=x :=
  carryAlgebra_fixed_iff x

/-- Clearing only powers of the original cDelta cannot hide a polynomial divisor
coprime to cDelta. No simplicity, squarefreeness, or R_d-coprimality is required. -/
theorem source_localization_divisibility (N L : Polynomial ℚ)
    (hcop : IsCoprime L sourceLocalizationDenominator)
    (hlocal : ∃ f : SourceLocalization, localMap N=localMap L*f) : L ∣ N := by
  obtain ⟨f,hf⟩ := hlocal
  obtain ⟨k,G,hG⟩ := IsLocalization.Away.surj sourceLocalizationDenominator f
  change f*localMap sourceLocalizationDenominator^k=localMap G at hG
  have he : N*sourceLocalizationDenominator^k=L*G := by
    apply localMap_injective
    rw [map_mul,map_pow,hf,mul_assoc]
    change localMap L*(f*localMap sourceLocalizationDenominator^k)=localMap (L*G)
    rw [hG,map_mul]
  have hd : L ∣ N*sourceLocalizationDenominator^k := by rw [he]; exact dvd_mul_right _ _
  exact hcop.pow_right.dvd_of_dvd_mul_right hd

end SubmittedGenus.FixedPivot
