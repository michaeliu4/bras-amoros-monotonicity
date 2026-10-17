import Results.Genus.FiniteArithmetic.ReflectionSeries
import Results.Genus.FiniteArithmetic.GeometricSources

/-!
# Complete original high-pivot q ≥ 9 tail

The pair alphabet contains every ordered pair of positive natural numbers with
sum at least eight. It is genuinely unbounded. All coefficient fibers are
finite by the general locally-finite source theorem. The pivot source contains
every natural q ≥ 9, and the two reflection blocks are independent actual
words. The rational identity is derived from these source cardinalities.
-/

namespace SubmittedGenus.FiniteArithmetic.OriginalTail

open PowerSeries
open Reflection

abbrev relaxedEightSystem : Reflection.System where
  pairAllowed a b := 1 ≤ a ∧ 1 ≤ b ∧ 8 ≤ a + b
  centerAllowed a := 4 ≤ a
  pairPositive a b h := by omega

noncomputable instance relaxedLettersFintype (n : ℕ) :
    Fintype (LocallyFinite.Letters relaxedEightSystem.pairAlphabet n) :=
  LocallyFinite.lettersFintype relaxedEightSystem.pairAlphabet n

noncomputable instance relaxedCentersFintype (n : ℕ) :
    Fintype (Reflection.Centers relaxedEightSystem n) :=
  Reflection.centersFintype relaxedEightSystem n

noncomputable def pairSeries : PowerSeries ℤ :=
  LocallyFinite.letterSeries relaxedEightSystem.pairAlphabet

/-- The first coordinate picks exactly one of the n−1 positive ordered pairs. -/
def pairLetterEquiv (n : ℕ) (hn : 8 ≤ n) :
    LocallyFinite.Letters relaxedEightSystem.pairAlphabet n ≃ Fin (n - 1) where
  toFun p := ⟨p.val.val.1 - 1, by
    have hp := p.val.property
    have hw := p.property
    change 1 ≤ p.val.val.1 ∧ 1 ≤ p.val.val.2 ∧ 8 ≤ p.val.val.1 + p.val.val.2 at hp
    change p.val.val.1 + p.val.val.2 = n at hw
    omega⟩
  invFun i := ⟨⟨(i.val + 1, n - (i.val + 1)), by
    change 1 ≤ i.val + 1 ∧ 1 ≤ n - (i.val + 1) ∧ 8 ≤ i.val + 1 + (n - (i.val + 1))
    have := i.isLt
    omega⟩, by
      change i.val + 1 + (n - (i.val + 1)) = n
      have := i.isLt
      omega⟩
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · change p.val.val.1 - 1 + 1 = p.val.val.1
      have hp := p.val.property.1
      omega
    · change n - (p.val.val.1 - 1 + 1) = p.val.val.2
      have hp := p.val.property.1
      have hw := p.property
      change p.val.val.1 + p.val.val.2 = n at hw
      omega
  right_inv i := by
    apply Fin.ext
    change i.val + 1 - 1 = i.val
    omega

theorem pairCount (n : ℕ) :
    LocallyFinite.letterCount relaxedEightSystem.pairAlphabet n =
      if 8 ≤ n then n - 1 else 0 := by
  by_cases hn : 8 ≤ n
  · rw [if_pos hn]
    exact (Fintype.card_congr (pairLetterEquiv n hn)).trans (Fintype.card_fin _)
  · rw [if_neg hn]
    haveI : IsEmpty (LocallyFinite.Letters relaxedEightSystem.pairAlphabet n) := by
      constructor
      intro p
      have hp := p.val.property.2.2
      have hw := p.property
      change p.val.val.1 + p.val.val.2 = n at hw
      exact hn (hw ▸ hp)
    exact Fintype.card_eq_zero

@[simp] theorem coeff_pairSeries (n : ℕ) :
    coeff n pairSeries = if 8 ≤ n then ((n - 1 : ℕ) : ℤ) else 0 := by
  simp [pairSeries, pairCount]

/-- Original b(z)=z⁸(7−6z)/(1−z)², with all ordered-pair multiplicities proved. -/
theorem pairSeries_identity :
    (1 - (X : PowerSeries ℤ))^2 * pairSeries = 7 • X^8 - 6 • X^9 := by
  have he : (1 - (X : PowerSeries ℤ))^2 * pairSeries =
      pairSeries - (X * pairSeries + X * pairSeries) + X^2 * pairSeries := by ring
  rw [he]
  apply PowerSeries.ext
  intro n
  simp only [map_add, map_sub, map_nsmul]
  have hx : (X : PowerSeries ℤ) * pairSeries = X^1 * pairSeries := by simp
  rw [hx]
  simp only [coeff_X_pow_mul', coeff_pairSeries, coeff_X_pow]
  by_cases hn : n ≤ 9
  · interval_cases n <;> norm_num
  · have h8 : 8 ≤ n := by omega
    have h81 : 8 ≤ n - 1 := by omega
    have h82 : 8 ≤ n - 2 := by omega
    simp only [if_pos h8, if_pos h81, if_pos h82,
      if_pos (show 1 ≤ n by omega), if_pos (show 2 ≤ n by omega),
      if_neg (show n ≠ 8 by omega), if_neg (show n ≠ 9 by omega)]
    norm_num
    omega

theorem centerCount (n : ℕ) :
    Fintype.card (Reflection.Centers relaxedEightSystem n) =
      (if n = 0 then 1 else 0) + (if 4 ≤ n then 1 else 0) := by
  by_cases hn : n = 0
  · subst n
    letI : Unique (Reflection.Centers relaxedEightSystem 0) := {
      default := ⟨none, rfl⟩
      uniq c := by
        rcases c with ⟨c, hc⟩
        apply Subtype.ext
        cases c with
        | none => rfl
        | some a =>
          have ha := a.property
          change 4 ≤ a.val at ha
          change a.val = 0 at hc
          omega }
    simp
  · by_cases h4 : 4 ≤ n
    · letI : Unique (Reflection.Centers relaxedEightSystem n) := {
        default := ⟨some ⟨n, h4⟩, rfl⟩
        uniq c := by
          rcases c with ⟨c, hc⟩
          apply Subtype.ext
          cases c with
          | none => exact (hn hc.symm).elim
          | some a =>
            exact congrArg Option.some (Subtype.ext hc) }
      simp [hn, h4]
    · haveI : IsEmpty (Reflection.Centers relaxedEightSystem n) := by
        constructor
        rintro ⟨c, hc⟩
        cases c with
        | none => exact hn hc.symm
        | some a => exact h4 (hc ▸ a.property)
      simp [hn, h4]

/-- Optional center source is one empty center plus every singleton ≥4. -/
theorem centerSeries_identity : Reflection.centerSeries relaxedEightSystem =
    1 + Geometric.digitSeries 4 := by
  apply PowerSeries.ext
  intro n
  simp only [Reflection.centerSeries, Graded.coeff_series, centerCount, Nat.cast_add,
    map_add, coeff_one, Geometric.coeff_digitSeries]
  split_ifs <;> norm_num

noncomputable def blockSeries : PowerSeries ℤ := Reflection.blockSeries relaxedEightSystem

/-- Exact all-length reflection-block relation (1−b) T = 1+a. -/
theorem blockSeries_identity : (1 - pairSeries) * blockSeries = 1 + Geometric.digitSeries 4 := by
  exact (Reflection.blockSeries_identity relaxedEightSystem).trans centerSeries_identity

/-- Actual marked-pivot source for every q ≥ 9 and both independent blocks. -/
abbrev TailSource := Graded.Product (Geometric.Digits 9)
  (Graded.Product (Reflection.Blocks relaxedEightSystem) (Reflection.Blocks relaxedEightSystem))

noncomputable def capacityMTail : PowerSeries ℤ := Graded.series TailSource

@[simp] theorem capacityMTail_source_coeff (n : ℕ) :
    coeff n capacityMTail = (Fintype.card (TailSource n) : ℤ) := by
  simp [capacityMTail]

theorem capacityMTail_factorization :
    capacityMTail = Geometric.digitSeries 9 * blockSeries^2 := by
  unfold capacityMTail TailSource
  rw [Graded.product_series, Graded.product_series]
  simp [Geometric.digitSeries, blockSeries, Reflection.blockSeries, pow_two]

/-- The full q ≥ 9 summand of original M, not a finite pivot truncation. -/
theorem capacityMTail_source_identity :
    ((1 - (X : PowerSeries ℤ)) * (1 - pairSeries)^2) * capacityMTail =
      X^9 * (1 + Geometric.digitSeries 4)^2 := by
  rw [capacityMTail_factorization]
  calc
    _ = ((1 - (X : PowerSeries ℤ)) * Geometric.digitSeries 9) *
        ((1 - pairSeries) * blockSeries)^2 := by ring
    _ = X^9 * (1 + Geometric.digitSeries 4)^2 := by
      rw [Geometric.digitSeries_identity, blockSeries_identity]

#print axioms pairSeries_identity
#print axioms capacityMTail_source_coeff
#print axioms capacityMTail_source_identity

end SubmittedGenus.FiniteArithmetic.OriginalTail
