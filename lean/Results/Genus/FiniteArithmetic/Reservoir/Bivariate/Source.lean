import Results.Genus.FiniteArithmetic.Reservoir.FailureOperator
import Mathlib.Algebra.Polynomial.Roots

namespace SubmittedGenus.FiniteArithmetic.Reservoir.Bivariate
open PowerSeries
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Weight is the outer power-series degree; physical mark distance is the
independent polynomial variable. Each exact weight has finitely many marks. -/
def markedSource {C : Type} (F : OriginalReservoir.PrefixFamily C) :
    PowerSeries (Polynomial ℤ) :=
  PowerSeries.mk (fun n => ∑ p : OriginalReservoir.PrefixOccurrence F n,
    (Polynomial.X : Polynomial ℤ)^p.distance)

/-- Evaluation of the independent distance variable at an integer. -/
def evalAt (k : ℤ) : PowerSeries (Polynomial ℤ) →+* PowerSeries ℤ :=
  PowerSeries.map (Polynomial.evalRingHom k)

/-- Embed a series independent of the mark variable. -/
def lift : PowerSeries ℤ →+* PowerSeries (Polynomial ℤ) :=
  PowerSeries.map Polynomial.C

@[simp] theorem evalAt_lift (k : ℤ) (a : PowerSeries ℤ) : evalAt k (lift a)=a := by
  apply PowerSeries.ext
  intro n
  simp [evalAt,lift]

@[simp] theorem evalAt_X (k : ℤ) : evalAt k (X : PowerSeries (Polynomial ℤ))=X := by
  simp [evalAt]

@[simp] theorem evalAt_markVariable (k : ℤ) :
    evalAt k (PowerSeries.C Polynomial.X)=PowerSeries.C k := by
  simp [evalAt]

theorem gradedTransform_C (a : ℕ → ℤ) :
    gradedTransform (fun n => PowerSeries.C (a n))=PowerSeries.mk a := by
  apply PowerSeries.ext
  intro g
  rw [gradedTransform_coeff,PowerSeries.coeff_mk]
  rw [Finset.sum_eq_single ⟨g,by omega⟩]
  · simp
  · intro b hb hne
    have hn : g-b.val≠0 := by
      have : b.val≠g := by intro h; exact hne (Fin.ext h)
      have := b.isLt
      omega
    rw [PowerSeries.coeff_C]
    exact if_neg hn
  · simp

theorem evalAt_markedSource {C : Type} (F : OriginalReservoir.PrefixFamily C) (k : ℤ) :
    evalAt k (markedSource F)=markedPrefixSeries F (PowerSeries.C k) := by
  unfold markedPrefixSeries
  have h (n : ℕ) :
      (∑ p : OriginalReservoir.PrefixOccurrence F n, (PowerSeries.C k)^p.distance) =
      PowerSeries.C (∑ p : OriginalReservoir.PrefixOccurrence F n, k^p.distance) := by
    simp
  simp_rw [h]
  rw [gradedTransform_C]
  apply PowerSeries.ext
  intro n
  simp [evalAt,markedSource]

/-- A polynomial-valued formal series is determined by all natural-number
specializations of its polynomial variable. No analytic evaluation is used. -/
theorem ext_nat_eval {a b : PowerSeries (Polynomial ℤ)}
    (h : ∀ k : ℕ, evalAt (k : ℤ) a=evalAt (k : ℤ) b) : a=b := by
  apply PowerSeries.ext
  intro n
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective (Nat.cast_injective (R := ℤ))).mono
  rintro _ ⟨k,rfl⟩
  exact congrArg (PowerSeries.coeff n) (h k)

#print axioms evalAt_markedSource
#print axioms ext_nat_eval
end
end SubmittedGenus.FiniteArithmetic.Reservoir.Bivariate
