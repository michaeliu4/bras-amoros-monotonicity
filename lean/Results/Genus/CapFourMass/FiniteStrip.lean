import Results.Genus.CapFourMass.ParitySum

noncomputable section
open scoped BigOperators
namespace SubmittedGenus.CapFourMass

def geometricPrefix (B : ℝ) (k : ℕ) : ℝ := (1-B^k)/(1-B)

lemma geometricPrefix_eq_sum (B : ℝ) (hB : B≠1) (k : ℕ) :
    geometricPrefix B k=∑j∈Finset.range k,B^j := by
  symm
  apply (eq_div_iff (sub_ne_zero.mpr hB.symm)).mpr
  exact geom_sum_mul_neg B k

/-- A finite row can cross its strip boundary only once. This exact formula
avoids quadratic expansion of the original omitted-pivot prefix. -/
def stripPrefix (B σ : ℝ) (n k : ℕ) : ℝ :=
  geometricPrefix B (min k (n+1)) +
    B^(n+1)*σ*geometricPrefix (B*σ) (k-(n+1))

lemma stripPrefix_eq_sum (B σ : ℝ) (hB : B≠1) (hBσ : B*σ≠1) (n k : ℕ) :
    stripPrefix B σ n k=∑j∈Finset.range k,stripRow B σ n j := by
  unfold stripPrefix
  rw [geometricPrefix_eq_sum B hB,geometricPrefix_eq_sum (B*σ) hBσ]
  by_cases hk : k≤n+1
  · rw [min_eq_left hk,Nat.sub_eq_zero_of_le hk]
    simp only [Finset.range_zero,Finset.sum_empty,mul_zero,add_zero]
    apply Finset.sum_congr rfl
    intro j hj
    have hsub : j-n=0 := by have := Finset.mem_range.mp hj; omega
    simp [stripRow,hsub]
  · have hk' : n+1≤k := by omega
    rw [min_eq_right hk']
    have he : k=(n+1)+(k-(n+1)) := by omega
    conv_rhs => rw [he,Finset.sum_range_add]
    rw [stripRow_prefix]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Nat.add_comm (n+1) j,stripRow_tail]

def parityRowPrefix (A B σ : ℝ) (u h a k : ℕ) : ℝ :=
  B^h*(A*B)^a*stripPrefix B σ (a+u-h) k

lemma parityRowPrefix_eq_sum (A B σ : ℝ) (hB : B≠1) (hBσ : B*σ≠1)
    (u h a k : ℕ) (hhu : h≤u) :
    parityRowPrefix A B σ u h a k=∑j∈Finset.range k,parityTerm A B σ u h a j := by
  unfold parityRowPrefix
  rw [stripPrefix_eq_sum B σ hB hBσ,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact (parityTerm_row A B σ u h a j hhu).symm

def parityRowCut (P v h a : ℕ) : ℕ :=
  (if v≤P then (P-v)/2+1 else 0)-(a+h)

lemma parityRowCut_iff (P v h a j : ℕ) :
    2*(a+h+j)+v≤P ↔ j<parityRowCut P v h a := by
  unfold parityRowCut
  split_ifs <;> omega

lemma parityRowCut_le (P v h a : ℕ) : parityRowCut P v h a≤P+1 := by
  unfold parityRowCut
  split_ifs <;> omega

/-- Exact linear-row evaluation of the original finite two-index prefix. -/
theorem parityPrefix_rows (A B σ : ℝ) (hB : B≠1) (hBσ : B*σ≠1)
    (P u v h : ℕ) (hhu : h≤u) :
    (∑q∈parityPrefix P h v,parityTerm A B σ u h q.1 q.2)=
      ∑a∈Finset.range (P+1),parityRowPrefix A B σ u h a (parityRowCut P v h a) := by
  unfold parityPrefix
  rw [Finset.sum_filter]
  calc
    _ = ∑a∈Finset.range (P+1),∑j∈Finset.range (P+1),
        if 2*(a+h+j)+v≤P then parityTerm A B σ u h a j else 0 :=
      Finset.sum_product _ _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [parityRowPrefix_eq_sum A B σ hB hBσ u h a _ hhu]
      simp_rw [parityRowCut_iff]
      rw [←Finset.sum_filter]
      congr 1
      ext j
      simp only [Finset.mem_filter,Finset.mem_range]
      have hh := parityRowCut_le P v h a
      omega

/-- The same actual omitted tail with O(P) closed finite rows. -/
theorem omittedParityRational_rows (A B σ : ℝ) (hB : B≠1) (hBσ : B*σ≠1)
    (P u v h : ℕ) (hhu : h≤u) :
    omittedParityRational A B σ P u v h=parityRational A B σ u h-
      ∑a∈Finset.range (P+1),parityRowPrefix A B σ u h a (parityRowCut P v h a) := by
  unfold omittedParityRational
  rw [parityPrefix_rows A B σ hB hBσ P u v h hhu]

#print axioms omittedParityRational_rows
end SubmittedGenus.CapFourMass
