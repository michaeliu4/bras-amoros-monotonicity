import Results.Genus.FiniteArithmetic.Reservoir.DecoratedWords
import Results.Genus.FiniteArithmetic.Reservoir.MarkedWeights

namespace SubmittedGenus.FiniteArithmetic.Reservoir

open PowerSeries
open scoped BigOperators
set_option synthInstance.maxSize 3000

abbrev VAtoms := Graded.Atoms vValue
abbrev OptionalUAtoms := Graded.Atoms optionalWeight
noncomputable instance vAtomsFintype (g : ℕ) : Fintype (VAtoms g) := Fintype.ofFinite _
noncomputable instance optionalUAtomsFintype (g : ℕ) : Fintype (OptionalUAtoms g) := Fintype.ofFinite _

theorem vAtoms_series : Graded.series VAtoms = s := by
  change Graded.atomSeries vValue = s
  rw [Graded.atomSeries_eq_sum]
  simp only [Fin.sum_univ_succ]
  norm_num [vValue,s]
  ring

theorem uAtoms_series : Graded.series UAtoms = u := by
  change Graded.atomSeries uValue = u
  rw [Graded.atomSeries_eq_sum]
  simp only [Fin.sum_univ_succ]
  norm_num [uValue,u]

theorem optionalUAtoms_series : Graded.series OptionalUAtoms = 1+u := by
  change Graded.atomSeries optionalWeight = 1+u
  rw [Graded.atomSeries_eq_sum]
  simp only [Fintype.sum_option, Fin.sum_univ_succ]
  norm_num [optionalWeight,uValue,u]

abbrev DWU (D : Decoration) (k : ℕ) := LocallyFinite.Words (decoratedU D k)
abbrev DWUV (D : Decoration) (k : ℕ) := LocallyFinite.Words (decoratedUV D k)
abbrev DWUU (D : Decoration) (k : ℕ) := LocallyFinite.Words (decoratedUU D k)
noncomputable def wU (D : Decoration) (k : ℕ) := LocallyFinite.wordSeries (decoratedU D k)
noncomputable def wUV (D : Decoration) (k : ℕ) := LocallyFinite.wordSeries (decoratedUV D k)
noncomputable def wUU (D : Decoration) (k : ℕ) := LocallyFinite.wordSeries (decoratedUU D k)

theorem wU_identity (D : Decoration) (k : ℕ) : (1-u*D.series^k)*wU D k=1 := by
  have h := LocallyFinite.wordSeries_identity (decoratedU D k)
  simpa only [decoratedU_letters, wU] using h

theorem wUV_identity (D : Decoration) (k : ℕ) : (1-v*D.series^k)*wUV D k=1 := by
  have h := LocallyFinite.wordSeries_identity (decoratedUV D k)
  simpa only [decoratedUV_letters, wUV] using h

theorem wUU_identity (D : Decoration) (k : ℕ) : (1-u^2*D.series^k)*wUU D k=1 := by
  have h := LocallyFinite.wordSeries_identity (decoratedUU D k)
  simpa only [decoratedUU_letters, wUU] using h

/-- Each distance unit receives one independent decoration. The three
nonterminal branches retain the distinguished pair mate and both word pieces. -/
abbrev SafeVSource (D : Decoration) := Graded.Shift 6
  (Graded.Product (D.Atoms 1) (Graded.Product OptionalUAtoms
    (Graded.Product UAtoms (Graded.Product (DWUV D 0) (DWUV D 1)))))
abbrev SafeUSource (D : Decoration) := Graded.Shift 6
  (Graded.Product (D.Atoms 2) (Graded.Product OptionalUAtoms
    (Graded.Product VAtoms (Graded.Product (DWUV D 1) (DWUV D 2)))))
abbrev SafeLeadingSource (D : Decoration) := Graded.Shift 6
  (Graded.Product (D.Atoms 1) (DWUV D 2))
abbrev SafeMarkedSource (D : Decoration) := Graded.Sum SafeSource
  (Graded.Sum (SafeVSource D) (Graded.Sum (SafeUSource D) (SafeLeadingSource D)))

abbrev EarlySuffixSource (D : Decoration) := Graded.Shift 9
  (Graded.Product (D.Atoms 1) (Graded.Product (DWUU D 0)
    (Graded.Product (DWU D 0) (DWU D 1))))
abbrev EarlySecondSource (D : Decoration) := Graded.Shift 9
  (Graded.Product (D.Atoms 2) (Graded.Product UAtoms (Graded.Product (DWUU D 0)
    (Graded.Product (DWUU D 1) (DWU D 1)))))
abbrev EarlyFirstSource (D : Decoration) := Graded.Shift 9
  (Graded.Product (D.Atoms 4) (Graded.Product UAtoms (Graded.Product (DWUU D 1)
    (Graded.Product (DWUU D 2) (DWU D 1)))))
abbrev EarlyMarkedSource (D : Decoration) := Graded.Sum EarlySource
  (Graded.Sum (EarlySuffixSource D) (Graded.Sum (EarlySecondSource D) (EarlyFirstSource D)))

noncomputable def safeMarkedSeries (D : Decoration) : PowerSeries ℤ := Graded.series (SafeMarkedSource D)
noncomputable def earlyMarkedSeries (D : Decoration) : PowerSeries ℤ := Graded.series (EarlyMarkedSource D)

theorem safeMarkedSeries_factorization (D : Decoration) :
    safeMarkedSeries D = safeSeries +
      X^6*D.series*(1+u)*u*wUV D 0*wUV D 1 +
      X^6*D.series^2*(1+u)*s*wUV D 1*wUV D 2 +
      X^6*D.series*wUV D 2 := by
  unfold safeMarkedSeries SafeMarkedSource SafeVSource SafeUSource SafeLeadingSource
  simp only [Graded.sum_series, Graded.shift_series, Graded.product_series,
    Decoration.atoms_series, optionalUAtoms_series, uAtoms_series, vAtoms_series]
  rw [safeSeries_factorization]
  dsimp only [wUV, LocallyFinite.wordSeries, LocallyFinite.wordCount, Graded.series]
  ring

theorem earlyMarkedSeries_factorization (D : Decoration) :
    earlyMarkedSeries D = earlySeries +
      X^9*D.series*wUU D 0*wU D 0*wU D 1 +
      X^9*D.series^2*u*wUU D 0*wUU D 1*wU D 1 +
      X^9*D.series^4*u*wUU D 1*wUU D 2*wU D 1 := by
  unfold earlyMarkedSeries EarlyMarkedSource EarlySuffixSource EarlySecondSource EarlyFirstSource
  simp only [Graded.sum_series, Graded.shift_series, Graded.product_series,
    Decoration.atoms_series, uAtoms_series]
  rw [earlySeries_factorization]
  dsimp only [wUV, wU, wUU, LocallyFinite.wordSeries, LocallyFinite.wordCount, Graded.series]
  ring

/-- Cleared form of the original displayed F_s(z,t), valid for either
zero-weight unit decorations or independently chosen binary decorations. -/
theorem safeMarkedSeries_identity (D : Decoration) :
    (1-v)*(1-v*D.series)*(1-v*D.series^2)*safeMarkedSeries D =
      X^3*(1+u)*(1-v*D.series)*(1-v*D.series^2) +
      X^6*u*(1+u)*D.series*(1-v*D.series^2) +
      X^6*D.series*(1+s*D.series)*(1-v) := by
  have h0 := wUV_identity D 0
  have h1 := wUV_identity D 1
  have h2 := wUV_identity D 2
  simp only [pow_zero, mul_one] at h0
  simp only [pow_one] at h1
  rw [safeMarkedSeries_factorization]
  calc
    _ = (1-v*D.series)*(1-v*D.series^2)*((1-v)*safeSeries) +
      X^6*D.series*(1+u)*u*(1-v*D.series^2)*((1-v)*wUV D 0)*((1-v*D.series)*wUV D 1) +
      X^6*D.series^2*(1+u)*s*(1-v)*((1-v*D.series)*wUV D 1)*((1-v*D.series^2)*wUV D 2) +
      X^6*D.series*(1-v)*(1-v*D.series)*((1-v*D.series^2)*wUV D 2) := by ring
    _ = _ := by rw [safeSeries_identity,h0,h1,h2]; unfold v; ring

/-- Cleared form of all three nonterminal terms of original F_e(z,t). -/
theorem earlyMarkedSeries_identity (D : Decoration) :
    (1-u)*(1-u^2)*(1-u*D.series)*(1-u^2*D.series)*(1-u^2*D.series^2)*earlyMarkedSeries D =
      X^6*(1-u*D.series)*(1-u^2*D.series)*(1-u^2*D.series^2) +
      X^9*D.series*(1-u^2*D.series)*(1-u^2*D.series^2) +
      X^9*u*D.series^2*(1-u)*(1-u^2*D.series^2) +
      X^9*u*D.series^4*(1-u)*(1-u^2) := by
  have hU0 := wU_identity D 0
  have hU1 := wU_identity D 1
  have h0 := wUU_identity D 0
  have h1 := wUU_identity D 1
  have h2 := wUU_identity D 2
  simp only [pow_zero, mul_one] at hU0 h0
  simp only [pow_one] at hU1 h1
  rw [earlyMarkedSeries_factorization]
  calc
    _ = (1-u*D.series)*(1-u^2*D.series)*(1-u^2*D.series^2)*(((1-u)*(1-u^2))*earlySeries) +
      X^9*D.series*(1-u^2*D.series)*(1-u^2*D.series^2)*((1-u^2)*wUU D 0)*((1-u)*wU D 0)*((1-u*D.series)*wU D 1) +
      X^9*D.series^2*u*(1-u)*(1-u^2*D.series^2)*((1-u^2)*wUU D 0)*((1-u^2*D.series)*wUU D 1)*((1-u*D.series)*wU D 1) +
      X^9*D.series^4*u*(1-u)*(1-u^2)*((1-u^2*D.series)*wUU D 1)*((1-u^2*D.series^2)*wUU D 2)*((1-u*D.series)*wU D 1) := by ring
    _ = _ := by rw [earlySeries_identity,hU0,hU1,h0,h1,h2]; ring

#print axioms safeMarkedSeries_identity
#print axioms earlyMarkedSeries_identity
end SubmittedGenus.FiniteArithmetic.Reservoir
