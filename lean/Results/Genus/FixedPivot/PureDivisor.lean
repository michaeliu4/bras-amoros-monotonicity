import Results.Genus.FixedPivot.Coprimality
import Mathlib.Algebra.Ring.GeomSum

/-! Exact polynomial construction of the original cancelled divisor L_d=E_d/E_tau. -/
noncomputable section
namespace SubmittedGenus.FixedPivot
open scoped BigOperators QuadraticAlgebra
open Polynomial

abbrev PolynomialCarryAlgebra := CarryAlgebra (carryB (X : Polynomial ℚ)) (carryC X)

def polynomialRoot : PolynomialCarryAlgebra := carryRoot _ _
def polynomialConjugate : PolynomialCarryAlgebra := carryConjugate _ _

lemma polynomial_roots_sum :
    polynomialRoot+polynomialConjugate=carryB (algebraMap (Polynomial ℚ) PolynomialCarryAlgebra X) := by
  rw [polynomialRoot,polynomialConjugate,carry_roots_sum]
  change (algebraMap (Polynomial ℚ) PolynomialCarryAlgebra) (X^2+X^3)=
    (algebraMap (Polynomial ℚ) PolynomialCarryAlgebra X)^2+
    (algebraMap (Polynomial ℚ) PolynomialCarryAlgebra X)^3
  simp only [map_add,map_pow]

lemma polynomial_roots_product :
    polynomialRoot*polynomialConjugate=carryC (algebraMap (Polynomial ℚ) PolynomialCarryAlgebra X) := by
  rw [polynomialRoot,polynomialConjugate,carry_roots_product]
  change (algebraMap (Polynomial ℚ) PolynomialCarryAlgebra) (-X^3-X^4)=
    -(algebraMap (Polynomial ℚ) PolynomialCarryAlgebra X)^3-
    (algebraMap (Polynomial ℚ) PolynomialCarryAlgebra X)^4
  simp only [map_sub,map_neg,map_pow]

lemma polynomialRoot_star : star polynomialRoot=polynomialConjugate := rfl
lemma polynomialConjugate_star : star polynomialConjugate=polynomialRoot := star_star _

lemma sourceE_root_factor (d : ℕ) :
    algebraMap (Polynomial ℚ) PolynomialCarryAlgebra (sourceE d)=
      (1-polynomialRoot^d)*(1-polynomialConjugate^d) := by
  rw [sourceE,map_pureDenominator]
  exact pureDenominator_roots _ _ _ polynomial_roots_sum polynomial_roots_product d

/-- Product of the two finite geometric sums, without choosing a rational-function quotient. -/
def pureGeometricProduct (tau k : ℕ) : PolynomialCarryAlgebra :=
  (∑ i ∈ Finset.range k, (polynomialRoot^tau)^i)*
    (∑ i ∈ Finset.range k, (polynomialConjugate^tau)^i)

lemma pureGeometricProduct_fixed (tau k : ℕ) :
    star (pureGeometricProduct tau k)=pureGeometricProduct tau k := by
  simp only [pureGeometricProduct,star_mul,star_sum,star_pow,
    polynomialRoot_star,polynomialConjugate_star]

/-- The exact base polynomial descended from this symmetric product. -/
def pureQuotient (tau k : ℕ) : Polynomial ℚ := (pureGeometricProduct tau k).re

lemma pureQuotient_map (tau k : ℕ) :
    algebraMap (Polynomial ℚ) PolynomialCarryAlgebra (pureQuotient tau k)=
      pureGeometricProduct tau k := by
  obtain ⟨p,hp⟩ := (carryAlgebra_fixed_iff (pureGeometricProduct tau k)).1
    (pureGeometricProduct_fixed tau k)
  unfold pureQuotient
  rw [← hp]
  simp

/-- E_(tau*k)=E_tau times the original finite geometric quotient, exactly in Q[z]. -/
theorem sourceE_mul_pureQuotient (tau k : ℕ) :
    sourceE (tau*k)=sourceE tau*pureQuotient tau k := by
  apply QuadraticAlgebra.C_injective (a := -carryC (X : Polynomial ℚ)) (b := carryB X)
  change algebraMap (Polynomial ℚ) PolynomialCarryAlgebra (sourceE (tau*k))=
    algebraMap (Polynomial ℚ) PolynomialCarryAlgebra (sourceE tau*pureQuotient tau k)
  rw [map_mul,sourceE_root_factor,sourceE_root_factor,pureQuotient_map,pureGeometricProduct]
  have h1:=geom_sum_mul_neg (polynomialRoot^tau) k
  have h2:=geom_sum_mul_neg (polynomialConjugate^tau) k
  rw [← pow_mul] at h1 h2
  calc
    _ = ((∑ i ∈ Finset.range k, (polynomialRoot^tau)^i)*(1-polynomialRoot^tau))*
        ((∑ i ∈ Finset.range k, (polynomialConjugate^tau)^i)*(1-polynomialConjugate^tau)) := by
      rw [h1,h2]
    _ = _ := by ring

/-- The explicit quotient divides the actual source E_d. -/
lemma pureQuotient_dvd (tau k : ℕ) : pureQuotient tau k ∣ sourceE (tau*k) := by
  rw [sourceE_mul_pureQuotient]
  exact dvd_mul_left _ _

/-- The actual original L_d always inherits the proved source coprimality. -/
theorem pureQuotient_coprime {tau k : ℕ} (hd : 0<tau*k) :
    IsCoprime (pureQuotient tau k) sourceLocalizationDenominator :=
  sourceE_divisor_coprime hd (pureQuotient_dvd tau k)

/-- The paper's parity-dependent tau. -/
def sourceTau (d : ℕ) : ℕ := if Even d then 2 else 1

lemma sourceTau_dvd (d : ℕ) : sourceTau d ∣ d := by
  unfold sourceTau
  split_ifs with he
  · exact he.two_dvd
  · exact one_dvd d

lemma sourceTau_mul_div (d : ℕ) : sourceTau d*(d/sourceTau d)=d :=
  Nat.mul_div_cancel' (sourceTau_dvd d)

/-- Original L_d with an exact polynomial witness, not assumed rational division. -/
def sourceL (d : ℕ) : Polynomial ℚ := pureQuotient (sourceTau d) (d/sourceTau d)

theorem sourceE_factor_sourceL (d : ℕ) : sourceE d=sourceE (sourceTau d)*sourceL d := by
  conv_lhs => rw [← sourceTau_mul_div d]
  exact sourceE_mul_pureQuotient _ _

theorem sourceL_dvd (d : ℕ) : sourceL d ∣ sourceE d := by
  rw [sourceE_factor_sourceL]
  exact dvd_mul_left _ _

theorem sourceL_coprime {d : ℕ} (hd : 0<d) : IsCoprime (sourceL d) sourceLocalizationDenominator :=
  sourceE_divisor_coprime hd (sourceL_dvd d)

end SubmittedGenus.FixedPivot
