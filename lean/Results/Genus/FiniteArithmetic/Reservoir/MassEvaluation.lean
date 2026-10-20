import Results.Genus.FiniteArithmetic.PolynomialBounds

namespace SubmittedGenus.FiniteArithmetic.Analytic

open PowerSeries
noncomputable section

/-- Evaluation is used as an algebraic operation only with explicit absolute
convergence hypotheses in the laws below. -/
def massAt (r : ℝ) (f : PowerSeries ℤ) : ℝ := ∑' n, realCoeff f n * r^n

theorem massAt_eq_normAt {r : ℝ} {f : PowerSeries ℤ} (hf : ∀ n, 0 ≤ coeff n f) :
    massAt r f = normAt r f := by
  apply tsum_congr
  intro n
  have hn : 0 ≤ realCoeff f n := by unfold realCoeff; exact_mod_cast hf n
  simp only [WeightedSeries.absWeightedTerm, abs_of_nonneg hn]

theorem massAt_add {r : ℝ} (hr : 0 ≤ r) {a b : PowerSeries ℤ}
    (ha : SummableAt r a) (hb : SummableAt r b) :
    massAt r (a+b) = massAt r a + massAt r b := by
  unfold massAt
  simp only [realCoeff_add, add_mul]
  exact (ha.summable hr).tsum_add (hb.summable hr)

theorem massAt_neg (r : ℝ) (a : PowerSeries ℤ) : massAt r (-a) = -massAt r a := by
  simp only [massAt, realCoeff, map_neg, Int.cast_neg, neg_mul, tsum_neg]

theorem summableAt_neg {r : ℝ} {a : PowerSeries ℤ} (ha : SummableAt r a) : SummableAt r (-a) := by
  change Summable (fun n => |realCoeff (-a) n| * r^n)
  change Summable (fun n => |realCoeff a n| * r^n) at ha
  simpa only [realCoeff, map_neg, Int.cast_neg, abs_neg] using ha

theorem massAt_sub {r : ℝ} (hr : 0 ≤ r) {a b : PowerSeries ℤ}
    (ha : SummableAt r a) (hb : SummableAt r b) :
    massAt r (a-b) = massAt r a - massAt r b := by
  rw [sub_eq_add_neg, massAt_add hr ha (summableAt_neg hb), massAt_neg, sub_eq_add_neg]

theorem massAt_mul {r : ℝ} (hr : 0 ≤ r) {a b : PowerSeries ℤ}
    (ha : SummableAt r a) (hb : SummableAt r b) :
    massAt r (a*b) = massAt r a * massAt r b := by
  unfold massAt
  rw [realCoeff_mul]
  exact WeightedSeries.weighted_tsum_convolution ha hb hr

@[simp] theorem massAt_monomial (r : ℝ) (c : ℤ) (k : ℕ) :
    massAt r (C c * X^k) = (c : ℝ)*r^k := by
  unfold massAt
  have he : (fun n => realCoeff (C c * X^k) n * r^n) =
      fun n => if n=k then (c : ℝ)*r^k else 0 := by
    funext n
    simp only [realCoeff, coeff_C_mul_X_pow]
    split_ifs with h
    · subst n; rfl
    · simp
  rw [he]
  simp

@[simp] theorem massAt_xpow (r : ℝ) (k : ℕ) : massAt r ((X : PowerSeries ℤ)^k) = r^k := by
  simpa using massAt_monomial r 1 k

@[simp] theorem massAt_one (r : ℝ) : massAt r (1 : PowerSeries ℤ)=1 := by
  simpa using massAt_xpow r 0

/-- Convergent source recurrence, evaluated without interpreting a divergent
formal geometric expression as an analytic sum. -/
theorem massAt_recurrence {r : ℝ} (hr : 0 ≤ r) {a b f : PowerSeries ℤ}
    (ha : SummableAt r a) (hb : SummableAt r b) (hf : SummableAt r f)
    (he : (1-b)*f=a) : (1-massAt r b)*massAt r f = massAt r a := by
  have hs : SummableAt r (1-b) :=
    (add_bound hr (one_bound r) ⟨summableAt_neg hb, le_refl (normAt r (-b))⟩).1
  have h := congrArg (massAt r) he
  rw [massAt_mul hr hs hf, massAt_sub hr (one_bound r).1 hb, massAt_one] at h
  exact h

theorem SummableAt.add {r : ℝ} {a b : PowerSeries ℤ} (ha : SummableAt r a) (hb : SummableAt r b)
    (hr : 0≤r) : SummableAt r (a+b) :=
  (add_bound hr ⟨ha,le_refl (normAt r a)⟩ ⟨hb,le_refl (normAt r b)⟩).1

theorem SummableAt.sub {r : ℝ} {a b : PowerSeries ℤ} (ha : SummableAt r a) (hb : SummableAt r b)
    (hr : 0≤r) : SummableAt r (a-b) := by
  rw [sub_eq_add_neg]
  exact ha.add (summableAt_neg hb) hr

theorem SummableAt.mul {r : ℝ} {a b : PowerSeries ℤ} (ha : SummableAt r a) (hb : SummableAt r b)
    (hr : 0≤r) : SummableAt r (a*b) :=
  (mul_bound hr ⟨ha,le_refl (normAt r a)⟩ ⟨hb,le_refl (normAt r b)⟩).1

#print axioms massAt_mul
#print axioms massAt_recurrence
end
end SubmittedGenus.FiniteArithmetic.Analytic
