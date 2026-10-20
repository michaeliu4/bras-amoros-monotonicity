import Results.Genus.FiniteArithmetic.Reservoir.PositiveEvaluation
import Results.Genus.FiniteArithmetic.Reservoir.ErrorSeries
import Results.Genus.Injection.ReservoirSources.FailureTails

namespace SubmittedGenus.FiniteArithmetic.Reservoir

open PowerSeries Analytic
noncomputable section
set_option maxHeartbeats 2000000

/-- The original nonbinary-reservoir evaluation radius. -/
def radius : ℝ := 5/8
def uValueAt : ℝ := radius^2+radius^3
def sValueAt : ℝ := radius+radius^2+radius^3
def cValueAt : ℝ := radius+radius^2
def vValueAt : ℝ := uValueAt*sValueAt

theorem radius_nonneg : 0 ≤ radius := by norm_num [radius]
theorem u_evaluates : PositiveEval radius u uValueAt :=
  (positiveEval_xpow radius 2).add radius_nonneg (positiveEval_xpow radius 3)
theorem s_evaluates : PositiveEval radius s sValueAt := by
  have hx : PositiveEval radius (X : PowerSeries ℤ) radius := by simpa using positiveEval_xpow radius 1
  exact (hx.add radius_nonneg (positiveEval_xpow radius 2)).add radius_nonneg (positiveEval_xpow radius 3)
theorem c_evaluates : PositiveEval radius c cValueAt := by
  have hx : PositiveEval radius (X : PowerSeries ℤ) radius := by simpa using positiveEval_xpow radius 1
  exact hx.add radius_nonneg (positiveEval_xpow radius 2)
theorem v_evaluates : PositiveEval radius v vValueAt := u_evaluates.mul radius_nonneg s_evaluates

theorem unit_decoration_evaluates : PositiveEval radius unitDecoration.series 1 := by
  rw [unitDecoration_series]; exact positiveEval_one radius
theorem binary_decoration_evaluates : PositiveEval radius binaryDecoration.series cValueAt := by
  rw [binaryDecoration_series]; exact c_evaluates

theorem word_evaluates (A : LocallyFinite.Alphabet) {b : PowerSeries ℤ} {x : ℝ}
    (he : LocallyFinite.letterSeries A=b) (hb : PositiveEval radius b x) (hx : x<1) :
    PositiveEval radius (LocallyFinite.wordSeries A) (1/(1-x)) := by
  apply (positiveEval_one radius).geometric radius_nonneg hb hx
  · simpa only [he] using LocallyFinite.wordSeries_identity A
  · intro n; simp only [LocallyFinite.coeff_wordSeries]; positivity

theorem u_t_small (t : ℝ) (ht : t=1 ∨ t=cValueAt) (k : ℕ) (hk : k≤2) :
    uValueAt*t^k<1 := by
  interval_cases k <;> rcases ht with rfl | rfl <;> norm_num [uValueAt,cValueAt,radius]
theorem v_t_small (t : ℝ) (ht : t=1 ∨ t=cValueAt) (k : ℕ) (hk : k≤2) :
    vValueAt*t^k<1 := by
  interval_cases k <;> rcases ht with rfl | rfl <;> norm_num [uValueAt,sValueAt,vValueAt,cValueAt,radius]
theorem uu_t_small (t : ℝ) (ht : t=1 ∨ t=cValueAt) (k : ℕ) (hk : k≤2) :
    uValueAt^2*t^k<1 := by
  interval_cases k <;> rcases ht with rfl | rfl <;> norm_num [uValueAt,cValueAt,radius]

theorem wU_evaluates (D : Decoration) (t : ℝ) (hD : PositiveEval radius D.series t)
    (ht : t=1 ∨ t=cValueAt) (k : ℕ) (hk : k≤2) :
    PositiveEval radius (wU D k) (1/(1-uValueAt*t^k)) :=
  word_evaluates (decoratedU D k) (decoratedU_letters D k)
    (u_evaluates.mul radius_nonneg (hD.pow radius_nonneg k)) (u_t_small t ht k hk)
theorem wUV_evaluates (D : Decoration) (t : ℝ) (hD : PositiveEval radius D.series t)
    (ht : t=1 ∨ t=cValueAt) (k : ℕ) (hk : k≤2) :
    PositiveEval radius (wUV D k) (1/(1-vValueAt*t^k)) :=
  word_evaluates (decoratedUV D k) (decoratedUV_letters D k)
    (v_evaluates.mul radius_nonneg (hD.pow radius_nonneg k)) (v_t_small t ht k hk)
theorem wUU_evaluates (D : Decoration) (t : ℝ) (hD : PositiveEval radius D.series t)
    (ht : t=1 ∨ t=cValueAt) (k : ℕ) (hk : k≤2) :
    PositiveEval radius (wUU D k) (1/(1-uValueAt^2*t^k)) :=
  word_evaluates (decoratedUU D k) (decoratedUU_letters D k)
    ((u_evaluates.pow radius_nonneg 2).mul radius_nonneg (hD.pow radius_nonneg k)) (uu_t_small t ht k hk)

def safeValue : ℝ := radius^3*(1+uValueAt)/(1-vValueAt)
def earlyValue : ℝ := radius^6/(1-uValueAt^2)/(1-uValueAt)

theorem safe_evaluates : PositiveEval radius safeSeries safeValue := by
  exact ((positiveEval_xpow radius 3).mul radius_nonneg
    ((positiveEval_one radius).add radius_nonneg u_evaluates)).geometric radius_nonneg
    v_evaluates (by norm_num [vValueAt,uValueAt,sValueAt,radius]) safeSeries_identity
    (by intro n; rw [safeSeries_coeff]; positivity)

theorem early_evaluates : PositiveEval radius earlySeries earlyValue := by
  have hu := word_evaluates uAlphabet u_letters u_evaluates (by norm_num [uValueAt,radius])
  have huu := word_evaluates uuAlphabet uu_letters (u_evaluates.pow radius_nonneg 2)
    (by norm_num [uValueAt,radius])
  rw [earlySeries_factorization]
  simpa only [earlyValue, div_eq_mul_inv, one_mul] using
    ((positiveEval_xpow radius 6).mul radius_nonneg huu).mul radius_nonneg hu

def safeMarkedValue (t : ℝ) : ℝ := safeValue +
  radius^6*t*(1+uValueAt)*uValueAt/(1-vValueAt)/(1-vValueAt*t) +
  radius^6*t^2*(1+uValueAt)*sValueAt/(1-vValueAt*t)/(1-vValueAt*t^2) +
  radius^6*t/(1-vValueAt*t^2)
def earlyMarkedValue (t : ℝ) : ℝ := earlyValue +
  radius^9*t/(1-uValueAt^2)/(1-uValueAt)/(1-uValueAt*t) +
  radius^9*t^2*uValueAt/(1-uValueAt^2)/(1-uValueAt^2*t)/(1-uValueAt*t) +
  radius^9*t^4*uValueAt/(1-uValueAt^2*t)/(1-uValueAt^2*t^2)/(1-uValueAt*t)

theorem safeMarked_evaluates (D : Decoration) (t : ℝ) (hD : PositiveEval radius D.series t)
    (ht : t=1 ∨ t=cValueAt) : PositiveEval radius (safeMarkedSeries D) (safeMarkedValue t) := by
  have h0 := wUV_evaluates D t hD ht 0 (by omega)
  have h1 := wUV_evaluates D t hD ht 1 (by omega)
  have h2 := wUV_evaluates D t hD ht 2 (by omega)
  have ho := (positiveEval_one radius).add radius_nonneg u_evaluates
  have hv := (((((positiveEval_xpow radius 6).mul radius_nonneg hD).mul radius_nonneg ho).mul
    radius_nonneg u_evaluates).mul radius_nonneg h0).mul radius_nonneg h1
  have hu := (((((positiveEval_xpow radius 6).mul radius_nonneg (hD.pow radius_nonneg 2)).mul
    radius_nonneg ho).mul radius_nonneg s_evaluates).mul radius_nonneg h1).mul radius_nonneg h2
  have hl := ((positiveEval_xpow radius 6).mul radius_nonneg hD).mul radius_nonneg h2
  rw [safeMarkedSeries_factorization]
  simpa only [safeMarkedValue,pow_zero,pow_one,mul_one,div_eq_mul_inv,one_mul] using
    ((safe_evaluates.add radius_nonneg hv).add radius_nonneg hu).add radius_nonneg hl

theorem earlyMarked_evaluates (D : Decoration) (t : ℝ) (hD : PositiveEval radius D.series t)
    (ht : t=1 ∨ t=cValueAt) : PositiveEval radius (earlyMarkedSeries D) (earlyMarkedValue t) := by
  have hU0 := wU_evaluates D t hD ht 0 (by omega)
  have hU1 := wU_evaluates D t hD ht 1 (by omega)
  have h0 := wUU_evaluates D t hD ht 0 (by omega)
  have h1 := wUU_evaluates D t hD ht 1 (by omega)
  have h2 := wUU_evaluates D t hD ht 2 (by omega)
  have hs := ((((positiveEval_xpow radius 9).mul radius_nonneg hD).mul radius_nonneg h0).mul
    radius_nonneg hU0).mul radius_nonneg hU1
  have hm := (((((positiveEval_xpow radius 9).mul radius_nonneg (hD.pow radius_nonneg 2)).mul
    radius_nonneg u_evaluates).mul radius_nonneg h0).mul radius_nonneg h1).mul radius_nonneg hU1
  have hf := (((((positiveEval_xpow radius 9).mul radius_nonneg (hD.pow radius_nonneg 4)).mul
    radius_nonneg u_evaluates).mul radius_nonneg h1).mul radius_nonneg h2).mul radius_nonneg hU1
  rw [earlyMarkedSeries_factorization]
  simpa only [earlyMarkedValue,pow_zero,pow_one,mul_one,div_eq_mul_inv,one_mul] using
    ((early_evaluates.add radius_nonneg hs).add radius_nonneg hm).add radius_nonneg hf

#print axioms safeMarked_evaluates
#print axioms earlyMarked_evaluates
end
end SubmittedGenus.FiniteArithmetic.Reservoir
