import Results.Genus.FiniteArithmetic.ReflectionSeries
import Results.Genus.FiniteArithmetic.FiniteAtoms
import Mathlib.Logic.Equiv.Option

namespace SubmittedGenus.FiniteArithmetic.Reflection

open scoped BigOperators
open PowerSeries

/-- Reflection threshold and cap are independent: this includes isolated-five
left/right blocks as well as the K_k factors in original M. -/
abbrev boundedSystem (threshold cap : ℕ) : System where
  pairAllowed a b := 1 ≤ a ∧ a ≤ cap ∧ 1 ≤ b ∧ b ≤ cap ∧ threshold ≤ a + b
  centerAllowed a := 1 ≤ a ∧ a ≤ cap ∧ threshold ≤ 2 * a
  pairPositive a b h := by omega

abbrev PairIndices (threshold cap : ℕ) :=
  {ij : Fin cap × Fin cap // threshold ≤ (ij.1.val + 1) + (ij.2.val + 1)}

abbrev CenterIndices (threshold cap : ℕ) :=
  {i : Fin cap // threshold ≤ 2 * (i.val + 1)}

def pairIndexWeight {threshold cap : ℕ} (p : PairIndices threshold cap) : ℕ :=
  (p.val.1.val + 1) + (p.val.2.val + 1)

def centerIndexWeight {threshold cap : ℕ} : Option (CenterIndices threshold cap) → ℕ
  | none => 0
  | some a => a.val.val + 1

def boundedPairEquiv (threshold cap : ℕ) :
    Pair (boundedSystem threshold cap).pairAllowed ≃ PairIndices threshold cap where
  toFun p := ⟨(⟨p.val.1 - 1, by have := p.property; dsimp at this; omega⟩,
      ⟨p.val.2 - 1, by have := p.property; dsimp at this; omega⟩), by
        have := p.property
        change threshold ≤ (p.val.1 - 1 + 1) + (p.val.2 - 1 + 1)
        omega⟩
  invFun p := ⟨(p.val.1.val + 1, p.val.2.val + 1), by
    have h1 := p.val.1.isLt
    have h2 := p.val.2.isLt
    have ht := p.property
    change 1 ≤ p.val.1.val + 1 ∧ p.val.1.val + 1 ≤ cap ∧
      1 ≤ p.val.2.val + 1 ∧ p.val.2.val + 1 ≤ cap ∧
      threshold ≤ (p.val.1.val + 1) + (p.val.2.val + 1)
    omega⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · change p.val.1 - 1 + 1 = p.val.1
      have := p.property.1
      omega
    · change p.val.2 - 1 + 1 = p.val.2
      have := p.property.2.2.1
      omega
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext <;> simp

theorem boundedPairEquiv_weight (threshold cap : ℕ)
    (p : Pair (boundedSystem threshold cap).pairAllowed) :
    pairIndexWeight (boundedPairEquiv threshold cap p) = pairWeight p := by
  change (p.val.1 - 1 + 1) + (p.val.2 - 1 + 1) = p.val.1 + p.val.2
  have hp := p.property
  omega

def boundedCenterEquiv (threshold cap : ℕ) :
    Center (boundedSystem threshold cap).centerAllowed ≃ CenterIndices threshold cap where
  toFun a := ⟨⟨a.val - 1, by have := a.property; dsimp at this; omega⟩, by
    change threshold ≤ 2 * (a.val - 1 + 1)
    have := a.property
    omega⟩
  invFun a := ⟨a.val.val + 1, by
    have := a.val.isLt
    have := a.property
    change 1 ≤ a.val.val + 1 ∧ a.val.val + 1 ≤ cap ∧ threshold ≤ 2 * (a.val.val + 1)
    omega⟩
  left_inv a := by
    apply Subtype.ext
    change a.val - 1 + 1 = a.val
    have := a.property.1
    omega
  right_inv a := by
    apply Subtype.ext
    apply Fin.ext
    simp

theorem boundedCenterEquiv_weight (threshold cap : ℕ)
    (c : Option (Center (boundedSystem threshold cap).centerAllowed)) :
    centerIndexWeight ((Equiv.optionCongr (boundedCenterEquiv threshold cap)) c) = centerWeight c := by
  cases c with
  | none => rfl
  | some a =>
    change a.val - 1 + 1 = a.val
    have := a.property.1
    omega

noncomputable def pairPolynomial (threshold cap : ℕ) : PowerSeries ℤ :=
  ∑ ij : Fin cap × Fin cap,
    if threshold ≤ (ij.1.val + 1) + (ij.2.val + 1) then
      X ^ ((ij.1.val + 1) + (ij.2.val + 1)) else 0

noncomputable def centerPolynomial (threshold cap : ℕ) : PowerSeries ℤ :=
  ∑ i : Fin cap, if threshold ≤ 2 * (i.val + 1) then X^(i.val + 1) else 0

/-- Actual ordered pairs, enumerated once by each physical coordinate. -/
theorem bounded_pair_series (threshold cap : ℕ) :
    LocallyFinite.letterSeries (boundedSystem threshold cap).pairAlphabet = pairPolynomial threshold cap := by
  letI : ∀ n, Fintype (Graded.Atoms (pairWeight (P := (boundedSystem threshold cap).pairAllowed)) n) :=
    fun n => LocallyFinite.lettersFintype (boundedSystem threshold cap).pairAlphabet n
  have h := Graded.atomSeries_congr (boundedPairEquiv threshold cap)
    pairWeight pairIndexWeight (boundedPairEquiv_weight threshold cap)
  have hh := Graded.atomSeries_subtype
    (fun ij : Fin cap × Fin cap => threshold ≤ (ij.1.val + 1) + (ij.2.val + 1))
    (fun ij : Fin cap × Fin cap => (ij.1.val + 1) + (ij.2.val + 1))
  exact h.trans hh

/-- The optional central physical coordinate contributes 1+a_k. -/
theorem bounded_center_series (threshold cap : ℕ) :
    centerSeries (boundedSystem threshold cap) = 1 + centerPolynomial threshold cap := by
  letI : ∀ n, Fintype (Graded.Atoms (centerWeight (C := (boundedSystem threshold cap).centerAllowed)) n) :=
    fun n => centersFintype (boundedSystem threshold cap) n
  have h := Graded.atomSeries_congr (Equiv.optionCongr (boundedCenterEquiv threshold cap))
    centerWeight centerIndexWeight (boundedCenterEquiv_weight threshold cap)
  have he : Graded.atomSeries (centerIndexWeight (threshold := threshold) (cap := cap)) =
      1 + centerPolynomial threshold cap := by
    rw [Graded.atomSeries_eq_sum, Fintype.sum_option]
    simp only [centerIndexWeight, pow_zero]
    rw [← Finset.sum_subtype (Finset.univ.filter (fun i : Fin cap => threshold ≤ 2 * (i.val + 1)))
      (by simp) (fun i : Fin cap => (X : PowerSeries ℤ)^(i.val + 1))]
    rw [Finset.sum_filter]
    rfl
  exact h.trans he

theorem bounded_block_identity (threshold cap : ℕ) :
    (1 - pairPolynomial threshold cap) * blockSeries (boundedSystem threshold cap) =
      1 + centerPolynomial threshold cap := by
  have h := blockSeries_identity (boundedSystem threshold cap)
  rw [bounded_pair_series, bounded_center_series] at h
  exact h

/-- Original K_k has pair threshold and letter cap both k. -/
noncomputable def capacityFactor (k : ℕ) : PowerSeries ℤ := blockSeries (boundedSystem k k)

theorem capacityFactor_source_identity (k : ℕ) :
    (1 - pairPolynomial k k) * capacityFactor k = 1 + centerPolynomial k k :=
  bounded_block_identity k k

#print axioms bounded_pair_series
#print axioms bounded_center_series
#print axioms capacityFactor_source_identity

end SubmittedGenus.FiniteArithmetic.Reflection
