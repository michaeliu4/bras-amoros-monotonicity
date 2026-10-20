import Results.Genus.FiniteArithmetic.Reservoir.BinaryLength

namespace SubmittedGenus.FiniteArithmetic.Reservoir

open PowerSeries
open scoped BigOperators

/-- A finite decoration may have zero weight (the specialization t=1).
The underlying letter remains positive, so decorated words stay locally finite. -/
structure Decoration where
  Letter : Type
  finite : Fintype Letter
  weight : Letter → ℕ

attribute [instance] Decoration.finite

abbrev Decoration.Atoms (D : Decoration) (k : ℕ) :=
  Graded.Atoms (fun f : Fin k → D.Letter => ∑ i, D.weight (f i))

noncomputable instance decorationAtomsFintype (D : Decoration) (k g : ℕ) :
    Fintype (D.Atoms k g) := Fintype.ofFinite _

noncomputable def Decoration.series (D : Decoration) : PowerSeries ℤ :=
  ∑ a : D.Letter, X^(D.weight a)

theorem Decoration.atoms_series (D : Decoration) (k : ℕ) :
    Graded.series (D.Atoms k) = D.series^k := by
  change Graded.atomSeries (fun f : Fin k → D.Letter => ∑ i, D.weight (f i)) = _
  rw [Graded.atomSeries_eq_sum]
  unfold series
  rw [Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro f _
  exact (Finset.prod_pow_eq_pow_sum Finset.univ (fun i => D.weight (f i)) X).symm

def decoratedAlphabet {A : Type} [Fintype A] (w : A → ℕ) (hw : ∀ a, 0 < w a)
    (D : Decoration) (k : ℕ) :=
  finiteAlphabet (fun p : A × (Fin k → D.Letter) => w p.1 + ∑ i, D.weight (p.2 i))
    (by intro p; have := hw p.1; omega)

theorem decorated_letters {A : Type} [Fintype A] (w : A → ℕ) (hw : ∀ a, 0 < w a)
    (D : Decoration) (k : ℕ) :
    LocallyFinite.letterSeries (decoratedAlphabet w hw D k) =
      (∑ a : A, (X : PowerSeries ℤ)^w a) * D.series^k := by
  unfold decoratedAlphabet
  rw [finiteAlphabet_letters]
  simp only [Fintype.sum_prod_type, pow_add]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.mul_sum]
  congr 1
  unfold Decoration.series
  rw [Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro f _
  exact (Finset.prod_pow_eq_pow_sum Finset.univ (fun i => D.weight (f i)) X).symm

abbrev decoratedU (D : Decoration) (k : ℕ) :=
  decoratedAlphabet uValue (by intro a; dsimp [uValue]; omega) D k
abbrev decoratedUV (D : Decoration) (k : ℕ) :=
  decoratedAlphabet (fun p : U×V => uValue p.1+vValue p.2)
    (by intro p; dsimp [uValue,vValue]; omega) D k
abbrev decoratedUU (D : Decoration) (k : ℕ) :=
  decoratedAlphabet (fun p : U×U => uValue p.1+uValue p.2)
    (by intro p; dsimp [uValue]; omega) D k

theorem decoratedU_letters (D : Decoration) (k : ℕ) :
    LocallyFinite.letterSeries (decoratedU D k) = u*D.series^k := by
  rw [decorated_letters]
  have h := u_letters
  rw [finiteAlphabet_letters] at h
  rw [h]

theorem decoratedUV_letters (D : Decoration) (k : ℕ) :
    LocallyFinite.letterSeries (decoratedUV D k) = v*D.series^k := by
  rw [decorated_letters]
  have h := uv_letters
  rw [finiteAlphabet_letters] at h
  rw [h]

theorem decoratedUU_letters (D : Decoration) (k : ℕ) :
    LocallyFinite.letterSeries (decoratedUU D k) = u^2*D.series^k := by
  rw [decorated_letters]
  have h := uu_letters
  rw [finiteAlphabet_letters] at h
  rw [h]

abbrev unitDecoration : Decoration := ⟨Unit, inferInstance, fun _ => 0⟩
abbrev binaryDecoration : Decoration := ⟨Fin 2, inferInstance, fun a => a.val+1⟩

@[simp] theorem unitDecoration_series : unitDecoration.series = 1 := by simp [Decoration.series]
@[simp] theorem binaryDecoration_series : binaryDecoration.series = c := by
  simp only [Decoration.series, Fin.sum_univ_succ]
  norm_num [binaryDecoration, c]

#print axioms Decoration.atoms_series
#print axioms decoratedUV_letters
end SubmittedGenus.FiniteArithmetic.Reservoir
