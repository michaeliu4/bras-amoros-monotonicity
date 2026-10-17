import Results.Genus.FixedPivot.SourceAlgebra

/-! Base change of the exact polynomial geometric quotient into the original localization. -/
namespace SubmittedGenus.FixedPivot
open Polynomial
open scoped BigOperators
noncomputable section

def sourceScalarExtension : PolynomialCarryAlgebra→+*SourceQuadratic where
  toFun x := ⟨localMap x.re,localMap x.im⟩
  map_one' := by
    change (⟨localMap 1,localMap 0⟩ : SourceQuadratic)=1
    simp only [map_one,map_zero]
    rfl
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp
  map_mul' x y := by
    apply QuadraticAlgebra.ext
    · change localMap (x.re*y.re+(-carryC (X : Polynomial ℚ))*x.im*y.im)=
        localMap x.re*localMap y.re+(-localMap sourceC)*localMap x.im*localMap y.im
      simp only [map_add,map_mul,map_neg]
      rfl
    · change localMap (x.re*y.im+x.im*y.re+carryB (X : Polynomial ℚ)*x.im*y.im)=
        localMap x.re*localMap y.im+localMap x.im*localMap y.re+
          localMap (carryB (X : Polynomial ℚ))*localMap x.im*localMap y.im
      simp only [map_add,map_mul]

lemma sourceScalarExtension_scalar (p : Polynomial ℚ) :
    sourceScalarExtension (algebraMap (Polynomial ℚ) PolynomialCarryAlgebra p)=sourceEmbedding p := by
  ext <;> simp [sourceScalarExtension,sourceEmbedding]

lemma sourceScalarExtension_root : sourceScalarExtension polynomialRoot=sourceLambda := by
  ext <;> simp [sourceScalarExtension,polynomialRoot,sourceLambda,carryRoot]

lemma sourceScalarExtension_conjugate : sourceScalarExtension polynomialConjugate=sourceMu := by
  ext <;> simp [sourceScalarExtension,polynomialConjugate,sourceMu,carryConjugate,carryRoot]

lemma source_pureQuotient (tau k : ℕ) :
    sourceEmbedding (pureQuotient tau k)=
      (∑ i∈Finset.range k,(sourceLambda^tau)^i)*(∑ i∈Finset.range k,(sourceMu^tau)^i) := by
  have hh:=congrArg sourceScalarExtension (pureQuotient_map tau k)
  rw [sourceScalarExtension_scalar] at hh
  simp only [pureGeometricProduct,map_mul,map_sum,map_pow,
    sourceScalarExtension_root,sourceScalarExtension_conjugate] at hh
  exact hh

lemma source_L_geometric (d : ℕ) :
    sourceEmbedding (sourceL d)=
      (∑ i∈Finset.range (d/sourceTau d),(sourceLambda^(sourceTau d))^i)*
      (∑ i∈Finset.range (d/sourceTau d),(sourceMu^(sourceTau d))^i) :=
  source_pureQuotient _ _

def sourceBInverse : SourceQuadratic :=
  algebraMap SourceLocalization SourceQuadratic (↑local_b_unit.unit⁻¹ : SourceLocalization)

lemma source_b_inverse : carryB sourceZ*sourceBInverse=1 := by
  have hb : carryB sourceZ=(algebraMap SourceLocalization SourceQuadratic)
      (localMap (carryB (X : Polynomial ℚ))) := by
    change carryB (sourceEmbedding X)=sourceEmbedding (carryB X)
    simp only [carryB,map_add,map_pow]
  rw [hb,sourceBInverse,← map_mul]
  rw [local_b_unit.mul_val_inv,map_one]

lemma source_E_roots (d : ℕ) : sourceEmbedding (sourceE d)=
    (1-sourceLambda^d)*(1-sourceMu^d) := by
  rw [sourceE,map_pureDenominator]
  exact pureDenominator_roots sourceZ sourceLambda sourceMu source_roots_sum source_roots_product d

end
end SubmittedGenus.FixedPivot
