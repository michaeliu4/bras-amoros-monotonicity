import Results.Genus.FixedPivot.SourceGenerating
import Results.Genus.FixedPivot.Projector
import Results.Genus.FixedPivot.InitialNumerator

/-! Explicit source-localized roots and injective polynomial embedding for rationality descent. -/
namespace SubmittedGenus.FixedPivot
open Polynomial
noncomputable section

def sourceEmbedding : Polynomial ℚ→+*SourceQuadratic :=
  (algebraMap SourceLocalization SourceQuadratic).comp localMap

lemma sourceEmbedding_injective : Function.Injective sourceEmbedding := by
  exact QuadraticAlgebra.C_injective.comp localMap_injective

def sourceZ : SourceQuadratic := sourceEmbedding X
def sourceLambda : SourceQuadratic := carryRoot (localMap (carryB (X : Polynomial ℚ))) (localMap sourceC)
def sourceMu : SourceQuadratic := carryConjugate (localMap (carryB (X : Polynomial ℚ))) (localMap sourceC)

def localCInverse : SourceLocalization := ↑local_c_unit.unit⁻¹
def localDeltaInverse : SourceLocalization := ↑local_delta_unit.unit⁻¹

def sourceLambdaInverse : SourceQuadratic :=
  carryRootInverse (localMap (carryB (X : Polynomial ℚ))) (localMap sourceC) localCInverse

def sourceMuInverse : SourceQuadratic := sourceLambda*algebraMap SourceLocalization SourceQuadratic localCInverse

def sourceDifferenceInverse : SourceQuadratic :=
  carryDifferenceInverse (localMap (carryB (X : Polynomial ℚ))) (localMap sourceC) localDeltaInverse

lemma source_roots_sum : sourceLambda+sourceMu=carryB sourceZ := by
  rw [sourceLambda,sourceMu,carry_roots_sum]
  change sourceEmbedding (carryB (X : Polynomial ℚ))=carryB (sourceEmbedding X)
  simp only [carryB,map_add,map_pow]

lemma source_roots_product : sourceLambda*sourceMu=carryC sourceZ := by
  rw [sourceLambda,sourceMu,carry_roots_product]
  change sourceEmbedding (carryC (X : Polynomial ℚ))=carryC (sourceEmbedding X)
  simp only [carryC,map_sub,map_neg,map_pow]

lemma source_lambda_inverse : sourceLambda*sourceLambdaInverse=1 :=
  carryRoot_mul_inverse _ _ _ local_c_unit.mul_val_inv

lemma source_mu_inverse : sourceMu*sourceMuInverse=1 := by
  unfold sourceMuInverse
  rw [← mul_assoc,mul_comm sourceMu sourceLambda,sourceLambda,sourceMu,carry_roots_product,
    ← map_mul,show localMap sourceC*localCInverse=1 from local_c_unit.mul_val_inv,map_one]

lemma source_difference_inverse : (sourceLambda-sourceMu)*sourceDifferenceInverse=1 := by
  apply carryDifference_mul_inverse
  have he : carryDiscriminant (localMap (carryB (X : Polynomial ℚ))) (localMap sourceC)=localMap sourceDelta := by
    simp only [sourceDelta,sourceC,carryDiscriminant,map_sub,map_pow,map_mul,map_ofNat]
  rw [he]
  exact local_delta_unit.mul_val_inv

lemma hom_natPolynomial {R : Type*} [CommRing R] (f : Polynomial ℚ→+*R) (p : Polynomial ℕ) :
    f (p.map (Nat.castRingHom ℚ))=Polynomial.eval₂ (Nat.castRingHom R) (f X) p := by
  induction p using Polynomial.induction_on' with
  | add p q ih ih' => simp only [Polynomial.map_add,map_add,eval₂_add,ih,ih']
  | monomial n a => simp [Polynomial.C_mul_X_pow_eq_monomial.symm,map_mul,map_pow]

lemma source_rawPolynomialQ (m r p : ℕ) :
    sourceEmbedding (rawPolynomialQ m r p)=
      Polynomial.eval₂ (Nat.castRingHom SourceQuadratic) sourceZ (RawGraph.rawPolynomial m r p 4) :=
  hom_natPolynomial sourceEmbedding _

end
end SubmittedGenus.FixedPivot
