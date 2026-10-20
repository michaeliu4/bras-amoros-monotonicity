import Results.Genus.FiniteArithmetic.Reservoir.PrefixCode

namespace SubmittedGenus.FiniteArithmetic.Reservoir

open PowerSeries
open scoped BigOperators
set_option synthInstance.maxSize 1000

/-- A finite positive alphabet as a locally finite actual word source. -/
def finiteAlphabet {A : Type} [Fintype A] (w : A → ℕ) (hw : ∀ a, 0 < w a) :
    LocallyFinite.Alphabet where
  Letter := A
  weight := w
  positive := hw
  finiteBelow n := inferInstance

theorem finiteAlphabet_letters {A : Type} [Fintype A] (w : A → ℕ) (hw : ∀ a, 0 < w a) :
    LocallyFinite.letterSeries (finiteAlphabet w hw) = ∑ a : A, (X : PowerSeries ℤ)^w a := by
  letI : ∀ n, Fintype (Graded.Atoms w n) :=
    fun n => LocallyFinite.lettersFintype (finiteAlphabet w hw) n
  exact Graded.atomSeries_eq_sum w

abbrev uAlphabet := finiteAlphabet uValue (by intro a; dsimp [uValue]; omega)
abbrev vAlphabet := finiteAlphabet vValue (by intro a; dsimp [vValue]; omega)
abbrev uvAlphabet := finiteAlphabet (fun p : U × V => uValue p.1 + vValue p.2)
  (by intro p; dsimp [uValue, vValue]; omega)
abbrev uuAlphabet := finiteAlphabet (fun p : U × U => uValue p.1 + uValue p.2)
  (by intro p; dsimp [uValue]; omega)

noncomputable def u : PowerSeries ℤ := X^2 + X^3
noncomputable def s : PowerSeries ℤ := X + X^2 + X^3
noncomputable def c : PowerSeries ℤ := X + X^2
noncomputable def v : PowerSeries ℤ := u * s

theorem u_letters : LocallyFinite.letterSeries uAlphabet = u := by
  rw [finiteAlphabet_letters]
  simp only [Fin.sum_univ_succ]
  norm_num [uValue, u]

theorem v_letters : LocallyFinite.letterSeries vAlphabet = s := by
  rw [finiteAlphabet_letters]
  simp only [Fin.sum_univ_succ]
  norm_num [vValue, s]
  ring

theorem uv_letters : LocallyFinite.letterSeries uvAlphabet = v := by
  rw [finiteAlphabet_letters]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_succ]
  norm_num [uValue, vValue, u, s, v]
  ring

theorem uu_letters : LocallyFinite.letterSeries uuAlphabet = u^2 := by
  rw [finiteAlphabet_letters]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_succ]
  norm_num [uValue, u]
  ring

abbrev UWords := LocallyFinite.Words uAlphabet
abbrev UVWords := LocallyFinite.Words uvAlphabet
abbrev UUWords := LocallyFinite.Words uuAlphabet
abbrev UAtoms := Graded.Atoms uValue
noncomputable instance uAtomsFintype (g : ℕ) : Fintype (UAtoms g) := Fintype.ofFinite _

/-- Exact finite sources for the two physical safe-prefix forms. -/
abbrev SafeBody := Graded.Sum UVWords (Graded.Product UAtoms UVWords)
abbrev SafeSource := Graded.Shift 3 SafeBody

/-- Exact finite source for U^h 1 U^h 2 U^k 3, with independent paired U blocks. -/
abbrev EarlySource := Graded.Shift 6 (Graded.Product UUWords UWords)

noncomputable def safeSeries : PowerSeries ℤ := Graded.series SafeSource
noncomputable def earlySeries : PowerSeries ℤ := Graded.series EarlySource

@[simp] theorem safeSeries_coeff (g : ℕ) :
    coeff g safeSeries = (Fintype.card (SafeSource g) : ℤ) := Graded.coeff_series _ _
@[simp] theorem earlySeries_coeff (g : ℕ) :
    coeff g earlySeries = (Fintype.card (EarlySource g) : ℤ) := Graded.coeff_series _ _

theorem safeSeries_factorization : safeSeries = (X : PowerSeries ℤ)^3 *
    (1 + u) * LocallyFinite.wordSeries uvAlphabet := by
  unfold safeSeries SafeSource SafeBody
  rw [Graded.shift_series, Graded.sum_series UVWords (Graded.Product UAtoms UVWords),
    Graded.product_series UAtoms UVWords]
  have ha : Graded.series UAtoms = u := by
    change Graded.atomSeries uValue = u
    rw [Graded.atomSeries_eq_sum]
    simp only [Fin.sum_univ_succ]
    norm_num [uValue, u]
  rw [ha]
  change X^3 * (LocallyFinite.wordSeries uvAlphabet + u * LocallyFinite.wordSeries uvAlphabet) = _
  ring

theorem earlySeries_factorization : earlySeries = (X : PowerSeries ℤ)^6 *
    LocallyFinite.wordSeries uuAlphabet * LocallyFinite.wordSeries uAlphabet := by
  unfold earlySeries EarlySource
  rw [Graded.shift_series, Graded.product_series]
  change X^6 * (LocallyFinite.wordSeries uuAlphabet * LocallyFinite.wordSeries uAlphabet) = _
  ring

/-- Original submitted C_s, proved from actual finite prefix codes. -/
theorem safeSeries_identity : (1 - v) * safeSeries = (X : PowerSeries ℤ)^3 * (1 + u) := by
  have h := LocallyFinite.wordSeries_identity uvAlphabet
  rw [uv_letters] at h
  rw [safeSeries_factorization]
  calc
    _ = X^3 * (1 + u) * ((1 - v) * LocallyFinite.wordSeries uvAlphabet) := by ring
    _ = _ := by rw [h, mul_one]

/-- Original submitted C_e, with its two independently chosen equal U blocks. -/
theorem earlySeries_identity : ((1 - u) * (1 - u^2)) * earlySeries = (X : PowerSeries ℤ)^6 := by
  have hu := LocallyFinite.wordSeries_identity uAlphabet
  have huu := LocallyFinite.wordSeries_identity uuAlphabet
  rw [u_letters] at hu
  rw [uu_letters] at huu
  rw [earlySeries_factorization]
  calc
    _ = X^6 * ((1 - u^2) * LocallyFinite.wordSeries uuAlphabet) *
      ((1 - u) * LocallyFinite.wordSeries uAlphabet) := by ring
    _ = _ := by rw [hu, huu]; ring

#print axioms safeSeries_identity
#print axioms earlySeries_identity

end SubmittedGenus.FiniteArithmetic.Reservoir
