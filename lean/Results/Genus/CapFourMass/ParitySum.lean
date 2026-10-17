import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Tactic

/-!
# Exact convergent parity-strip sum of the submitted tail proof

The first two rational terms come from one finite strip in each outer row.
Their infinite sums converge under AB<1 and AB²<1, even when B>1.
-/
noncomputable section
open scoped BigOperators
namespace SubmittedGenus.CapFourMass

/-- One row, split at its genuine finite-strip endpoint. -/
def stripRow (B σ : ℝ) (n j : ℕ) : ℝ := B^j*σ^(j-n)

lemma stripRow_tail (B σ : ℝ) (n j : ℕ) :
    stripRow B σ n (j+(n+1)) = (B^(n+1)*σ)*(B*σ)^j := by
  have hsub : j+(n+1)-n=j+1 := by omega
  rw [stripRow,hsub,pow_add,pow_succ,mul_pow]
  ring

lemma stripRow_prefix (B σ : ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range (n+1), stripRow B σ n j) = ∑ j ∈ Finset.range (n+1), B^j := by
  apply Finset.sum_congr rfl
  intro j hj
  have hsub : j-n=0 := by have := Finset.mem_range.mp hj; omega
  simp [stripRow,hsub]

lemma stripRow_hasSum {B σ : ℝ} (hB : 0 ≤ B) (hσ : 0 ≤ σ)
    (hBσ : B*σ < 1) (n : ℕ) :
    HasSum (stripRow B σ n)
      ((∑ j ∈ Finset.range (n+1), B^j)+B^(n+1)*σ/(1-B*σ)) := by
  have hg := (hasSum_geometric_of_lt_one (mul_nonneg hB hσ) hBσ).mul_left (B^(n+1)*σ)
  have ht : HasSum (fun j => stripRow B σ n (j+(n+1))) (B^(n+1)*σ/(1-B*σ)) := by
    simpa only [stripRow_tail,div_eq_mul_inv] using hg
  have h := ht.sum_range_add
  rwa [stripRow_prefix] at h

lemma finite_geometric_strip (B : ℝ) (hB : B ≠ 1) (n : ℕ) :
    (∑ j ∈ Finset.range (n+1), B^j) = (1-B^(n+1))/(1-B) := by
  apply (eq_div_iff (sub_ne_zero.mpr hB.symm)).mpr
  exact geom_sum_mul_neg B (n+1)

/-- Reindex b=a+h+j, exactly the manuscript pivot domain b≥a+h. -/
def parityTerm (A B σ : ℝ) (u h a j : ℕ) : ℝ :=
  A^a*B^(a+h+j)*σ^((a+h+j)-(2*a+u))

def parityRowValue (A B σ : ℝ) (u h a : ℕ) : ℝ :=
  (B^h*(A*B)^a-B^(u+1)*(A*B^2)^a)/(1-B)+
    (B^(u+1)*σ*(A*B^2)^a)/(1-B*σ)

def parityRational (A B σ : ℝ) (u h : ℕ) : ℝ :=
  B^h/((1-B)*(1-A*B))-B^(u+1)/((1-B)*(1-A*B^2))+
    B^(u+1)*σ/((1-B*σ)*(1-A*B^2))

lemma parityTerm_row (A B σ : ℝ) (u h a j : ℕ) (hhu : h ≤ u) :
    parityTerm A B σ u h a j = B^h*(A*B)^a*stripRow B σ (a+u-h) j := by
  have he : a+h+j-(2*a+u)=j-(a+u-h) := by omega
  simp only [parityTerm,he,stripRow,pow_add,mul_pow]
  ring

lemma parity_corner_power (A B : ℝ) (u h a : ℕ) (hhu : h ≤ u) :
    B^h*(A*B)^a*B^(a+u-h+1) = B^(u+1)*(A*B^2)^a := by
  rw [mul_pow,mul_pow,← pow_mul]
  have he : h+a+(a+u-h+1)=(u+1)+2*a := by omega
  calc
    B^h*(A^a*B^a)*B^(a+u-h+1) = A^a*B^(h+a+(a+u-h+1)) := by
      simp only [pow_add]
      ring
    _ = A^a*B^((u+1)+2*a) := by rw [he]
    _ = _ := by rw [pow_add]; ring

lemma parityRow_hasSum {A B σ : ℝ} (hB : 0 ≤ B) (hσ : 0 ≤ σ)
    (hBσ : B*σ < 1) (hB1 : B ≠ 1) (u h a : ℕ) (hhu : h ≤ u) :
    HasSum (parityTerm A B σ u h a) (parityRowValue A B σ u h a) := by
  have hs := (stripRow_hasSum hB hσ hBσ (a+u-h)).mul_left (B^h*(A*B)^a)
  have he : (B^h*(A*B)^a)*
      ((∑ j ∈ Finset.range (a+u-h+1), B^j)+B^(a+u-h+1)*σ/(1-B*σ)) =
      parityRowValue A B σ u h a := by
    rw [finite_geometric_strip B hB1]
    unfold parityRowValue
    have hp := parity_corner_power A B u h a hhu
    calc
      _ = (B^h*(A*B)^a-B^h*(A*B)^a*B^(a+u-h+1))/(1-B)+
          (B^h*(A*B)^a*B^(a+u-h+1))*σ/(1-B*σ) := by ring
      _ = _ := by rw [hp]; ring
  rw [he] at hs
  have hf : parityTerm A B σ u h a = fun j => B^h*(A*B)^a*stripRow B σ (a+u-h) j :=
    funext (fun j => parityTerm_row A B σ u h a j hhu)
  rw [← hf] at hs
  exact hs

/-- The two finite-strip series are individually geometric in AB and AB².
No B<1 hypothesis occurs anywhere in this identity. -/
lemma parityRows_hasSum {A B σ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hAB : A*B < 1) (hAB2 : A*B^2 < 1) (u h : ℕ) :
    HasSum (parityRowValue A B σ u h) (parityRational A B σ u h) := by
  have hg1 := hasSum_geometric_of_lt_one (mul_nonneg hA hB) hAB
  have hg2 := hasSum_geometric_of_lt_one (mul_nonneg hA (sq_nonneg _)) hAB2
  have hs := ((hg1.mul_left (B^h)).sub (hg2.mul_left (B^(u+1)))).div_const (1-B)
  have ht := (hg2.mul_left (B^(u+1)*σ)).div_const (1-B*σ)
  have hall := hs.add ht
  have he : (B^h*(1-A*B)⁻¹-B^(u+1)*(1-A*B^2)⁻¹)/(1-B)+
      (B^(u+1)*σ*(1-A*B^2)⁻¹)/(1-B*σ) = parityRational A B σ u h := by
    unfold parityRational
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [he] at hall
  exact hall

/-- Exact iterated original parity sum with its full convergence domain. -/
theorem parity_iterated_hasSum {A B σ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hσ : 0 ≤ σ) (hAB : A*B < 1) (hAB2 : A*B^2 < 1) (hBσ : B*σ < 1)
    (hB1 : B ≠ 1) (u h : ℕ) (hhu : h ≤ u) :
    HasSum (fun a => ∑' j, parityTerm A B σ u h a j) (parityRational A B σ u h) := by
  have he (a : ℕ) : (∑' j, parityTerm A B σ u h a j) = parityRowValue A B σ u h a :=
    (parityRow_hasSum hB hσ hBσ hB1 u h a hhu).tsum_eq
  simpa only [he] using parityRows_hasSum hA hB hAB hAB2 u h

lemma parityTerm_nonneg {A B σ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hσ : 0 ≤ σ)
    (u h a j : ℕ) : 0 ≤ parityTerm A B σ u h a j := by
  unfold parityTerm
  positivity

/-- Genuine two-index summability, not just a formal iterated expression. -/
theorem parity_summable {A B σ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hσ : 0 ≤ σ) (hAB : A*B < 1) (hAB2 : A*B^2 < 1) (hBσ : B*σ < 1)
    (hB1 : B ≠ 1) (u h : ℕ) (hhu : h ≤ u) :
    Summable (fun q : ℕ×ℕ => parityTerm A B σ u h q.1 q.2) := by
  apply (summable_prod_of_nonneg (fun q => parityTerm_nonneg hA hB hσ u h q.1 q.2)).mpr
  exact ⟨fun a => (parityRow_hasSum hB hσ hBσ hB1 u h a hhu).summable,
    (parity_iterated_hasSum hA hB hσ hAB hAB2 hBσ hB1 u h hhu).summable⟩

theorem parity_tsum {A B σ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hσ : 0 ≤ σ) (hAB : A*B < 1) (hAB2 : A*B^2 < 1) (hBσ : B*σ < 1)
    (hB1 : B ≠ 1) (u h : ℕ) (hhu : h ≤ u) :
    (∑' q : ℕ×ℕ, parityTerm A B σ u h q.1 q.2) = parityRational A B σ u h := by
  rw [(parity_summable hA hB hσ hAB hAB2 hBσ hB1 u h hhu).tsum_prod]
  exact (parity_iterated_hasSum hA hB hσ hAB hAB2 hBσ hB1 u h hhu).tsum_eq

/-- Exact finite set of omitted-prefix coordinates, in the source reindexing
r=2a+u and p=2(a+h+j)+v. -/
def parityPrefix (P h v : ℕ) : Finset (ℕ×ℕ) :=
  ((Finset.range (P+1)).product (Finset.range (P+1))).filter
    (fun q => 2*(q.1+h+q.2)+v ≤ P)

lemma mem_parityPrefix (P h v : ℕ) (q : ℕ×ℕ) :
    q ∈ parityPrefix P h v ↔ 2*(q.1+h+q.2)+v ≤ P := by
  constructor
  · intro hq
    exact (Finset.mem_filter.mp hq).2
  · intro hq
    apply Finset.mem_filter.mpr
    refine ⟨?_, hq⟩
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩

def omittedParityTerm (A B σ : ℝ) (P u v h : ℕ) (q : ℕ×ℕ) : ℝ :=
  if P < 2*(q.1+h+q.2)+v then parityTerm A B σ u h q.1 q.2 else 0

def omittedParityRational (A B σ : ℝ) (P u v h : ℕ) : ℝ :=
  parityRational A B σ u h-
    ∑ q ∈ parityPrefix P h v, parityTerm A B σ u h q.1 q.2

/-- Removing the finite prefix leaves exactly the displayed rational tail,
not an asymptotic approximation and not a subtraction of divergent sums. -/
theorem omittedParity_hasSum {A B σ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hσ : 0 ≤ σ) (hAB : A*B < 1) (hAB2 : A*B^2 < 1) (hBσ : B*σ < 1)
    (hB1 : B ≠ 1) (P u v h : ℕ) (hhu : h ≤ u) :
    HasSum (omittedParityTerm A B σ P u v h) (omittedParityRational A B σ P u v h) := by
  classical
  let f := fun q : ℕ×ℕ => parityTerm A B σ u h q.1 q.2
  have hs : Summable f := parity_summable hA hB hσ hAB hAB2 hBσ hB1 u h hhu
  have ht : Summable (omittedParityTerm A B σ P u v h) := by
    apply hs.of_norm_bounded
    intro q
    unfold omittedParityTerm
    split_ifs
    · rw [Real.norm_eq_abs,abs_of_nonneg (parityTerm_nonneg hA hB hσ u h q.1 q.2)]
    · simpa only [norm_zero] using parityTerm_nonneg hA hB hσ u h q.1 q.2
  have hp : Summable (fun q : ℕ×ℕ => if 2*(q.1+h+q.2)+v ≤ P then f q else 0) := by
    apply hs.of_norm_bounded
    intro q
    split_ifs
    · exact le_of_eq (Real.norm_of_nonneg (parityTerm_nonneg hA hB hσ u h q.1 q.2))
    · simpa only [norm_zero] using parityTerm_nonneg hA hB hσ u h q.1 q.2
  have hsplit : (fun q : ℕ×ℕ =>
      (if 2*(q.1+h+q.2)+v ≤ P then f q else 0)+omittedParityTerm A B σ P u v h q) = f := by
    funext q
    unfold omittedParityTerm
    by_cases hq : 2*(q.1+h+q.2)+v ≤ P
    · simp [hq,show ¬ P < 2*(q.1+h+q.2)+v by omega]
    · simp [hq,show P < 2*(q.1+h+q.2)+v by omega,f]
  have hsum := hp.tsum_add ht
  rw [hsplit] at hsum
  have hprefix : (∑' q : ℕ×ℕ, if 2*(q.1+h+q.2)+v ≤ P then f q else 0) =
      ∑ q ∈ parityPrefix P h v, f q := by
    rw [tsum_eq_sum (s := parityPrefix P h v)]
    · apply Finset.sum_congr rfl
      intro q hq
      rw [if_pos ((mem_parityPrefix P h v q).mp hq)]
    · intro q hq
      exact if_neg (fun hh => hq ((mem_parityPrefix P h v q).mpr hh))
  rw [hprefix] at hsum
  have htotal : (∑' q, f q) = parityRational A B σ u h :=
    parity_tsum hA hB hσ hAB hAB2 hBσ hB1 u h hhu
  rw [htotal] at hsum
  have he : (∑' q, omittedParityTerm A B σ P u v h q) =
      omittedParityRational A B σ P u v h := by
    unfold omittedParityRational
    linarith
  exact he ▸ ht.hasSum

lemma omittedParity_nonneg {A B σ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hσ : 0 ≤ σ) (P u v h : ℕ) (q : ℕ×ℕ) :
    0 ≤ omittedParityTerm A B σ P u v h q := by
  unfold omittedParityTerm
  split_ifs
  · exact parityTerm_nonneg hA hB hσ u h q.1 q.2
  · rfl

end SubmittedGenus.CapFourMass
