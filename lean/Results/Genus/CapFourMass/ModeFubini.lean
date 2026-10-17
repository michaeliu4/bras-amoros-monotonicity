import Results.Genus.CapFourMass.LocalPartitions

/-! Finite component regrouping, with each core sum taken before absolute value.
Actual source-to-component identifications must be supplied as explicit equalities
and equivalences; a signed total-partition equality alone is insufficient. -/
namespace SubmittedGenus.CapFourMass.ModeFubini
open scoped BigOperators
noncomputable section
variable {C : Type*} [Fintype C] {X B : C→Type*}
variable [∀c,Fintype (X c)] [∀c,Fintype (B c)]
attribute [local instance] Classical.propDecidable Classical.decEq

def coefficient (W : (c:C)→X c→B c→ℝ) (b : (c:C)→B c) : ℝ :=
  ∑x : (c:C)→X c,∏c,W c (x c) (b c)

theorem coefficient_factor (W : (c:C)→X c→B c→ℝ) (b : (c:C)→B c) :
    coefficient W b=∏c,∑x:X c,W c x (b c) := by
  unfold coefficient
  exact (Fintype.prod_sum (fun c x => W c x (b c))).symm

/-- The absolute value surrounds each completed core contraction. -/
theorem absolute_factor (W : (c:C)→X c→B c→ℝ) :
    (∑b : (c:C)→B c,|coefficient W b|)=
      ∏c,∑b:B c,|∑x:X c,W c x b| := by
  simp_rw [coefficient_factor,Finset.abs_prod]
  exact (Fintype.prod_sum (fun c b => |∑x:X c,W c x b|)).symm

theorem scalar_absolute_factor (W : (c:C)→X c→B c→ℝ) (t : ℝ) (ht : 0≤t) :
    (∑b : (c:C)→B c,|t*coefficient W b|)=
      t*(∏c,∑b:B c,|∑x:X c,W c x b|) := by
  simp_rw [abs_mul,abs_of_nonneg ht]
  rw [←Finset.mul_sum,absolute_factor]

section Transport
variable {U V : Type*} [Fintype U] [Fintype V]

theorem transported_coefficient (eX : U≃((c:C)→X c)) (eB : V≃((c:C)→B c))
    (W : (c:C)→X c→B c→ℝ) (w : U→V→ℝ)
    (hfactor : ∀x b,w x b=∏c,W c (eX x c) (eB b c)) (b : V) :
    (∑x:U,w x b)=coefficient W (eB b) := by
  simp_rw [hfactor]
  exact eX.sum_comp (fun x => ∏c,W c (x c) (eB b c))

/-- Explicit product-coordinate equivalences transport the source expression;
there is no exchange of absolute value with the inner core sum. -/
theorem transported_absolute_factor (eX : U≃((c:C)→X c)) (eB : V≃((c:C)→B c))
    (W : (c:C)→X c→B c→ℝ) (w : U→V→ℝ)
    (hfactor : ∀x b,w x b=∏c,W c (eX x c) (eB b c)) :
    (∑b:V,|∑x:U,w x b|)=∏c,∑b:B c,|∑x:X c,W c x b| := by
  simp_rw [transported_coefficient eX eB W w hfactor]
  rw [eB.sum_comp (fun b => |coefficient W b|)]
  exact absolute_factor W

theorem transported_scalar_absolute_factor
    (eX : U≃((c:C)→X c)) (eB : V≃((c:C)→B c))
    (W : (c:C)→X c→B c→ℝ) (w : U→V→ℝ)
    (hfactor : ∀x b,w x b=∏c,W c (eX x c) (eB b c)) (t : ℝ) (ht : 0≤t) :
    (∑b:V,|t*(∑x:U,w x b)|)=t*(∏c,∑b:B c,|∑x:X c,W c x b|) := by
  simp_rw [abs_mul,abs_of_nonneg ht]
  rw [←Finset.mul_sum,transported_absolute_factor eX eB W w hfactor]

/-- The two fixed maximum-four pivots contribute their one common z^8 weight. -/
theorem transported_pivot_absolute_factor
    (eX : U≃((c:C)→X c)) (eB : V≃((c:C)→B c))
    (W : (c:C)→X c→B c→ℝ) (w : U→V→ℝ)
    (hfactor : ∀x b,w x b=∏c,W c (eX x c) (eB b c)) (z : ℝ) :
    (∑b:V,|z^8*(∑x:U,w x b)|)=z^8*(∏c,∑b:B c,|∑x:X c,W c x b|) := by
  exact transported_scalar_absolute_factor eX eB W w hfactor (z^8) (by positivity)
end Transport

#print axioms transported_pivot_absolute_factor
end
end SubmittedGenus.CapFourMass.ModeFubini
