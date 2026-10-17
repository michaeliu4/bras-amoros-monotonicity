import Results.Genus.FixedPivot.Localization
import Results.Genus.FixedPivot.Denominator
import Mathlib.Algebra.Polynomial.SpecificDegree

/-!
# Original cDelta coprimality
The nontrivial discriminant roots are handled in the exact rational quadratic
field with z²+z+4=0. The repeated carry root -2z has algebraic norm16, hence no
positive power equals1. This is the manuscript's modulus-four argument in
exact algebraic form, with no floating evaluation or simple-root assumption.
-/
noncomputable section
namespace SubmittedGenus.FixedPivot
open Polynomial
open scoped QuadraticAlgebra

section Ring
variable {R : Type*} [CommRing R]

def pureDenominator (z : R) (d : ℕ) : R :=
  1-traceSum (carryB z) (carryC z) d+(carryC z)^d

lemma pureDenominator_roots (z lam mu : R) (hb : lam+mu=carryB z)
    (hc : lam*mu=carryC z) (d : ℕ) :
    pureDenominator z d=(1-lam^d)*(1-mu^d) := by
  unfold pureDenominator
  rw [traceSum_eq_of_roots _ _ lam mu hb hc,← hc,mul_pow]
  ring

lemma map_pureDenominator {S : Type*} [CommRing S] (f : R →+* S) (z : R) (d : ℕ) :
    f (pureDenominator z d)=pureDenominator (f z) d := by
  simp [pureDenominator,map_traceSum,carryB,carryC]

end Ring

def sourceE (d : ℕ) : Polynomial ℚ := pureDenominator X d

def discriminantQuadratic : Polynomial ℚ := X^2+X+4

lemma discriminantQuadratic_irreducible : Irreducible discriminantQuadratic := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · have hd : discriminantQuadratic.natDegree=2 := by
      unfold discriminantQuadratic
      compute_degree!
    norm_num [hd]
  · intro z hz
    change Polynomial.eval z discriminantQuadratic=0 at hz
    simp [discriminantQuadratic] at hz
    nlinarith [sq_nonneg (2*z+1)]

abbrev DiscriminantField := QuadraticAlgebra ℚ (-4) (-1)

instance : Fact (∀ r : ℚ, r^2≠(-4)+(-1)*r) := ⟨by
  intro r hr
  nlinarith [sq_nonneg (2*r+1)]⟩

def discriminantRoot : DiscriminantField := QuadraticAlgebra.omega

def repeatedCarryRoot : DiscriminantField := -2*discriminantRoot

lemma discriminantRoot_equation : discriminantRoot^2+discriminantRoot+4=0 := by
  ext <;> norm_num [discriminantRoot,QuadraticAlgebra.omega,pow_two]

lemma repeatedCarryRoot_sum : repeatedCarryRoot+repeatedCarryRoot=carryB discriminantRoot := by
  ext <;> norm_num [repeatedCarryRoot,discriminantRoot,QuadraticAlgebra.omega,carryB,pow_succ]

lemma repeatedCarryRoot_product : repeatedCarryRoot*repeatedCarryRoot=carryC discriminantRoot := by
  ext <;> norm_num [repeatedCarryRoot,discriminantRoot,QuadraticAlgebra.omega,carryC,pow_succ]

lemma repeatedCarryRoot_norm : QuadraticAlgebra.norm repeatedCarryRoot=(16 : ℚ) := by
  norm_num [QuadraticAlgebra.norm_def,repeatedCarryRoot,discriminantRoot,QuadraticAlgebra.omega]

lemma repeatedCarryRoot_pow_ne_one {d : ℕ} (hd : 0<d) : repeatedCarryRoot^d≠1 := by
  intro he
  have hn:=congrArg QuadraticAlgebra.norm he
  rw [map_pow,repeatedCarryRoot_norm,map_one] at hn
  have hp : (1 : ℚ)<16^d := one_lt_pow₀ (by norm_num) (by omega)
  linarith

lemma sourceE_at_discriminant (d : ℕ) :
    Polynomial.eval₂ (algebraMap ℚ DiscriminantField) discriminantRoot (sourceE d)=
      (1-repeatedCarryRoot^d)^2 := by
  have hm:=map_pureDenominator (Polynomial.eval₂RingHom (algebraMap ℚ DiscriminantField)
    discriminantRoot) (X : Polynomial ℚ) d
  change Polynomial.eval₂ (algebraMap ℚ DiscriminantField) discriminantRoot (sourceE d)=_ at hm
  simp only [Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X] at hm
  rw [hm,pureDenominator_roots discriminantRoot repeatedCarryRoot repeatedCarryRoot
    repeatedCarryRoot_sum repeatedCarryRoot_product]
  ring

lemma sourceE_at_discriminant_ne_zero {d : ℕ} (hd : 0<d) :
    Polynomial.eval₂ (algebraMap ℚ DiscriminantField) discriminantRoot (sourceE d)≠0 := by
  rw [sourceE_at_discriminant]
  exact pow_ne_zero 2 (sub_ne_zero.mpr (Ne.symm (repeatedCarryRoot_pow_ne_one hd)))

/-- E_d does not vanish at either nontrivial discriminant root. -/
theorem sourceE_coprime_quadratic {d : ℕ} (hd : 0<d) :
    IsCoprime (sourceE d) discriminantQuadratic := by
  rcases discriminantQuadratic_irreducible.isCoprime_or_dvd (sourceE d) with h | h
  · exact h.symm
  · exfalso
    apply sourceE_at_discriminant_ne_zero hd
    apply Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero _ _ h
    simpa [discriminantQuadratic] using discriminantRoot_equation

lemma traceSum_zero_succ {R : Type*} [CommRing R] (n : ℕ) :
    traceSum (0 : R) 0 (n+1)=0 := by
  cases n with
  | zero => rfl
  | succ n => simp [traceSum_rec]

lemma sourceE_eval (z : ℚ) (d : ℕ) : (sourceE d).eval z=pureDenominator z d := by
  exact (map_pureDenominator (Polynomial.evalRingHom z) (X : Polynomial ℚ) d).trans (by simp)

lemma sourceE_zero {d : ℕ} (hd : 0<d) : (sourceE d).eval 0=1 := by
  obtain ⟨n,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
  rw [sourceE_eval,pureDenominator]
  simp [carryB,carryC,traceSum_zero_succ]

lemma sourceE_neg_one {d : ℕ} (hd : 0<d) : (sourceE d).eval (-1)=1 := by
  obtain ⟨n,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
  rw [sourceE_eval,pureDenominator]
  norm_num [carryB,carryC,traceSum_zero_succ]

lemma sourceE_coprime_X {d : ℕ} (hd : 0<d) : IsCoprime (sourceE d) X := by
  rcases (Polynomial.irreducible_X (R := ℚ)).isCoprime_or_dvd (sourceE d) with h | h
  · exact h.symm
  · have he:=Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero (RingHom.id ℚ) (0 : ℚ) h (by simp)
    change (sourceE d).eval 0=0 at he
    rw [sourceE_zero hd] at he
    norm_num at he

lemma sourceE_coprime_X_add_one {d : ℕ} (hd : 0<d) : IsCoprime (sourceE d) (X+1) := by
  have hirr : Irreducible ((X : Polynomial ℚ)+1) := by
    simpa using Polynomial.irreducible_X_sub_C (-1 : ℚ)
  rcases hirr.isCoprime_or_dvd (sourceE d) with h | h
  · exact h.symm
  · have he:=Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero (RingHom.id ℚ) (-1 : ℚ) h (by simp)
    change (sourceE d).eval (-1)=0 at he
    rw [sourceE_neg_one hd] at he
    norm_num at he

/-- Original source E_d is coprime to every factor of cDelta, with no simple-root premise. -/
theorem sourceE_coprime_localization {d : ℕ} (hd : 0<d) :
    IsCoprime (sourceE d) sourceLocalizationDenominator := by
  have hprod : IsCoprime (sourceE d)
      ((X : Polynomial ℚ)^6*(X+1)^2*discriminantQuadratic) :=
    ((sourceE_coprime_X hd).pow_right.mul_right
      (sourceE_coprime_X_add_one hd).pow_right).mul_right (sourceE_coprime_quadratic hd)
  change IsCoprime (sourceE d) (carryC (X : Polynomial ℚ)*
    carryDiscriminant (carryB X) (carryC X))
  rw [carry_localization_denominator]
  have he : -(X : Polynomial ℚ)^6*(X+1)^2*(X^2+X+4)=
      -(X^6*(X+1)^2*discriminantQuadratic) := by unfold discriminantQuadratic; ring
  rw [he,IsCoprime.neg_right_iff]
  exact hprod

/-- Any polynomial L_d dividing the exact E_d inherits the required coprimality. -/
theorem sourceE_divisor_coprime {d : ℕ} (hd : 0<d) {L : Polynomial ℚ}
    (hL : L ∣ sourceE d) : IsCoprime L sourceLocalizationDenominator :=
  (sourceE_coprime_localization hd).of_isCoprime_of_dvd_left hL

/-- The paper's cancellation descent now consumes proved source coprimality. -/
theorem source_cancel_localized_divisor {d : ℕ} (hd : 0<d) (N L : Polynomial ℚ)
    (hL : L ∣ sourceE d)
    (hlocal : ∃ f : SourceLocalization, localMap N=localMap L*f) : L ∣ N :=
  source_localization_divisibility N L (sourceE_divisor_coprime hd hL) hlocal

end SubmittedGenus.FixedPivot
