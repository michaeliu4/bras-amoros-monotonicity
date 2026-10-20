import Results.Genus.FiniteComparison.FiveAggregate
import Results.Genus.Injection.RawFourAggregate

/-! Finite source boxes from the submitted reflection support inequality.
These source reductions do not assert any imported coefficient table values. -/
noncomputable section
open scoped BigOperators
namespace SubmittedGenus.FiniteComparison.SourceBoxes
open RawGraph

lemma sum_range_same {f : ℕ → ℕ} {a b : ℕ}
    (ha : ∀ i, a ≤ i → f i = 0) (hb : ∀ i, b ≤ i → f i = 0) :
    ∑ i ∈ Finset.range a, f i = ∑ i ∈ Finset.range b, f i := by
  have h (n : ℕ) (hn : n ≤ max a b) (hz : ∀ i, n ≤ i → f i=0) :
      ∑ i ∈ Finset.range n, f i = ∑ i ∈ Finset.range (max a b), f i := by
    apply Finset.sum_subset (Finset.range_mono hn)
    intro i hi hni
    exact hz i (by simpa using hni)
  exact (h a (le_max_left _ _) ha).trans (h b (le_max_right _ _) hb).symm

lemma triple_sum_same {f : ℕ → ℕ → ℕ → ℕ} {a b : ℕ}
    (ha : ∀ m r p, a ≤ m ∨ a ≤ r ∨ a ≤ p → f m r p=0)
    (hb : ∀ m r p, b ≤ m ∨ b ≤ r ∨ b ≤ p → f m r p=0) :
    (∑ m ∈ Finset.range a, ∑ r ∈ Finset.range a, ∑ p ∈ Finset.range a, f m r p) =
    ∑ m ∈ Finset.range b, ∑ r ∈ Finset.range b, ∑ p ∈ Finset.range b, f m r p := by
  calc
    _ = ∑ m ∈ Finset.range a, ∑ r ∈ Finset.range a, ∑ p ∈ Finset.range b, f m r p := by
      apply Finset.sum_congr rfl; intro m hm
      apply Finset.sum_congr rfl; intro r hr
      exact sum_range_same (fun p hp => ha m r p (Or.inr (Or.inr hp)))
        (fun p hp => hb m r p (Or.inr (Or.inr hp)))
    _ = ∑ m ∈ Finset.range a, ∑ r ∈ Finset.range b, ∑ p ∈ Finset.range b, f m r p := by
      apply Finset.sum_congr rfl; intro m hm
      apply sum_range_same
      · intro r hr; apply Finset.sum_eq_zero; intro p hp; exact ha m r p (Or.inr (Or.inl hr))
      · intro r hr; apply Finset.sum_eq_zero; intro p hp; exact hb m r p (Or.inr (Or.inl hr))
    _ = _ := by
      apply sum_range_same
      · intro m hm; apply Finset.sum_eq_zero; intro r hr
        apply Finset.sum_eq_zero; intro p hp; exact ha m r p (Or.inl hm)
      · intro m hm; apply Finset.sum_eq_zero; intro r hr
        apply Finset.sum_eq_zero; intro p hp; exact hb m r p (Or.inl hm)

lemma coefficient_cube_support {a g n : ℕ}
    (h : ∀ m, n ≤ m → 2*g < (a-1)*m+1) (m r p : ℕ)
    (hout : n ≤ m ∨ n ≤ r ∨ n ≤ p) : (rawPolynomial m r p a).coeff g=0 := by
  by_cases hm : n ≤ m
  · apply rawPolynomial_coeff_zero_of_support
    have hh:=h m hm
    omega
  · have hi : ¬ Parameters m r p a := by
      intro hp
      unfold Parameters at hp
      rcases hout with hm'|hr|hp'
      · exact hm hm'
      · omega
      · omega
    simp [rawPolynomial_invalid hi]

def box (a n g : ℕ) : ℕ :=
  ∑ m ∈ Finset.range n, ∑ r ∈ Finset.range n, ∑ p ∈ Finset.range n,
    (rawPolynomial m r p a).coeff g

lemma capFive_box (g : ℕ) (hg : g ≤ 300) : box 5 (g+2) g = box 5 150 g := by
  apply triple_sum_same
  · exact coefficient_cube_support (by intro m hm; omega)
  · exact coefficient_cube_support (by intro m hm; omega)

lemma capFour_box (g : ℕ) (hg : g ≤ 897) : box 4 (g+2) g = box 4 598 g := by
  apply triple_sum_same
  · exact coefficient_cube_support (by intro m hm; omega)
  · exact coefficient_cube_support (by intro m hm; omega)

lemma fin_aggregate_eq_box (a g : ℕ) :
    (∑ m : Fin (g+2), ∑ r : Fin (g+2), ∑ p : Fin (g+2),
      (rawPolynomial m.val r.val p.val a).coeff g) = box a (g+2) g := by
  unfold box
  calc
    _ = ∑ m : Fin (g+2), ∑ r : Fin (g+2), ∑ p ∈ Finset.range (g+2),
        (rawPolynomial m.val r.val p a).coeff g := by
      apply Finset.sum_congr rfl; intro m hm
      apply Finset.sum_congr rfl; intro r hr
      exact Fin.sum_univ_eq_sum_range (fun p : ℕ => (rawPolynomial m.val r.val p a).coeff g) (g+2)
    _ = ∑ m : Fin (g+2), ∑ r ∈ Finset.range (g+2), ∑ p ∈ Finset.range (g+2),
        (rawPolynomial m.val r p a).coeff g := by
      apply Finset.sum_congr rfl; intro m hm
      exact Fin.sum_univ_eq_sum_range (fun r : ℕ => ∑ p ∈ Finset.range (g+2),
        (rawPolynomial m.val r p a).coeff g) (g+2)
    _ = _ := Fin.sum_univ_eq_sum_range (fun m : ℕ => ∑ r ∈ Finset.range (g+2),
      ∑ p ∈ Finset.range (g+2), (rawPolynomial m r p a).coeff g) (g+2)

/-- Exact full raw-four aggregate lies in the original multiplicity range
through genus897. This statement does not truncate the pivot at300. -/
theorem rawFourCount_eq_box (g : ℕ) (hg : g ≤ 897) :
    OriginalPopulations.rawFourCount g = box 4 598 g := by
  rw [OriginalPopulations.RawFourAggregate.rawFourCount_eq_aggregate,
    fin_aggregate_eq_box, capFour_box g hg]

/-- All genuine low cap-five sources inject into the finite original raw box.
The imported301 coefficients still require source-correct evaluation. -/
theorem genuineFive_le_box (g : ℕ) (hg : g ≤ 300) :
    CapFiveMass.count g ≤ box 5 150 g := by
  have h := FiveAggregate.genuineFive_le_aggregate g
  rwa [fin_aggregate_eq_box, capFive_box g hg] at h

/-- The original cap-five file kept multiplicities through293. The smaller
support-correct box through149 has exactly the same coefficients through300. -/
theorem originalFive_box (g : ℕ) (hg : g ≤ 300) : box 5 150 g = box 5 294 g := by
  apply triple_sum_same
  · exact coefficient_cube_support (by intro m hm; omega)
  · exact coefficient_cube_support (by intro m hm; omega)

def retainedFour (g : ℕ) : ℕ :=
  ∑ m ∈ Finset.range 598, ∑ r ∈ Finset.range 301, ∑ p ∈ Finset.range 301,
    (rawPolynomial m r p 4).coeff g

/-- Before genus604 all omitted pivots vanish by the original support lemma. -/
theorem rawFourCount_eq_retained (g : ℕ) (hg : g < 604) :
    OriginalPopulations.rawFourCount g = retainedFour g := by
  rw [rawFourCount_eq_box g (by omega)]
  unfold box retainedFour
  apply Finset.sum_congr rfl
  intro m hm
  calc
    _ = ∑ r ∈ Finset.range 598, ∑ p ∈ Finset.range 301,
        (rawPolynomial m r p 4).coeff g := by
      apply Finset.sum_congr rfl; intro r hr
      apply sum_range_same
      · intro p hp; exact omitted_pivot_coeff_zero (by omega) hg
      · intro p hp; exact omitted_pivot_coeff_zero (by omega) hg
    _ = _ := by
      apply sum_range_same
      · intro r hr
        apply Finset.sum_eq_zero; intro p hp
        have hp' := Finset.mem_range.mp hp
        have hi : ¬ Parameters m r p 4 := by unfold Parameters; omega
        simp [rawPolynomial_invalid hi]
      · intro r hr
        apply Finset.sum_eq_zero; intro p hp
        have hp' := Finset.mem_range.mp hp
        have hi : ¬ Parameters m r p 4 := by unfold Parameters; omega
        simp [rawPolynomial_invalid hi]

#print axioms rawFourCount_eq_box
#print axioms genuineFive_le_box

end SubmittedGenus.FiniteComparison.SourceBoxes
