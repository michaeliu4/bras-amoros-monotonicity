import Results.Genus.FiniteArithmetic.Reservoir.MassEvaluation

namespace SubmittedGenus.FiniteArithmetic.Analytic

open PowerSeries
noncomputable section

/-- A proved nonnegative series, its convergence, and its exact real value. -/
structure PositiveEval (r : ℝ) (f : PowerSeries ℤ) (x : ℝ) : Prop where
  summable : SummableAt r f
  nonnegative : ∀ n, 0 ≤ coeff n f
  value : massAt r f = x

theorem PositiveEval.norm {r x : ℝ} {f : PowerSeries ℤ} (h : PositiveEval r f x) : normAt r f=x :=
  (massAt_eq_normAt h.nonnegative).symm.trans h.value

theorem PositiveEval.add {r x y : ℝ} {f g : PowerSeries ℤ} (hr : 0 ≤ r)
    (h : PositiveEval r f x) (k : PositiveEval r g y) : PositiveEval r (f+g) (x+y) where
  summable := (add_bound hr ⟨h.summable,h.norm.le⟩ ⟨k.summable,k.norm.le⟩).1
  nonnegative n := by rw [map_add]; exact add_nonneg (h.nonnegative n) (k.nonnegative n)
  value := by rw [massAt_add hr h.summable k.summable,h.value,k.value]

theorem PositiveEval.mul {r x y : ℝ} {f g : PowerSeries ℤ} (hr : 0 ≤ r)
    (h : PositiveEval r f x) (k : PositiveEval r g y) : PositiveEval r (f*g) (x*y) where
  summable := (mul_bound hr ⟨h.summable,h.norm.le⟩ ⟨k.summable,k.norm.le⟩).1
  nonnegative n := by
    rw [coeff_mul]
    exact Finset.sum_nonneg (fun p _ => mul_nonneg (h.nonnegative p.1) (k.nonnegative p.2))
  value := by rw [massAt_mul hr h.summable k.summable,h.value,k.value]

theorem positiveEval_xpow (r : ℝ) (k : ℕ) : PositiveEval r ((X : PowerSeries ℤ)^k) (r^k) where
  summable := (xpow_bound r k).1
  nonnegative n := by simp only [coeff_X_pow]; split_ifs <;> norm_num
  value := massAt_xpow r k

theorem positiveEval_one (r : ℝ) : PositiveEval r (1 : PowerSeries ℤ) 1 := by
  simpa using positiveEval_xpow r 0

theorem positiveEval_nat (r : ℝ) (k : ℕ) : PositiveEval r (k : PowerSeries ℤ) (k : ℝ) where
  summable := by simpa using (monomial_bound r (k : ℤ) 0).1
  nonnegative n := by
    have he : (k : PowerSeries ℤ) = C (k : ℤ) * X^0 := by simp
    rw [he, coeff_C_mul_X_pow]
    split_ifs <;> positivity
  value := by simpa using massAt_monomial r (k : ℤ) 0

theorem PositiveEval.pow {r x : ℝ} {f : PowerSeries ℤ} (hr : 0 ≤ r)
    (h : PositiveEval r f x) (k : ℕ) : PositiveEval r (f^k) (x^k) := by
  induction k with
  | zero => simpa using positiveEval_one r
  | succ k ih => simpa only [pow_succ] using ih.mul hr h

/-- Convergence comes from a strict evaluated denominator bound; it is never
an extra assumption about the rational source being evaluated. -/
theorem PositiveEval.geometric {r x y : ℝ} {a b f : PowerSeries ℤ} (hr : 0 ≤ r)
    (ha : PositiveEval r a x) (hb : PositiveEval r b y) (hy : y<1)
    (he : (1-b)*f=a) (hf : ∀ n, 0 ≤ coeff n f) : PositiveEval r f (x/(1-y)) := by
  have hs := geometric_bound hr ⟨ha.summable,ha.norm.le⟩ ⟨hb.summable,hb.norm.le⟩ hy he
  refine ⟨hs.1,hf,?_⟩
  have hv := massAt_recurrence hr ha.summable hb.summable hs.1 he
  rw [ha.value,hb.value] at hv
  apply (eq_div_iff (by linarith : 1-y≠0)).mpr
  nlinarith

theorem positiveEval_sum {I : Type} (r : ℝ) (hr : 0≤r) (s : Finset I)
    (f : I→PowerSeries ℤ) (x : I→ℝ) (h : ∀ i∈s,PositiveEval r (f i) (x i)) :
    PositiveEval r (∑ i∈s,f i) (∑ i∈s,x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using positiveEval_nat r 0
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha,Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add hr
      (ih (fun i hi=>h i (Finset.mem_insert_of_mem hi)))

#print axioms PositiveEval.geometric
end
end SubmittedGenus.FiniteArithmetic.Analytic
