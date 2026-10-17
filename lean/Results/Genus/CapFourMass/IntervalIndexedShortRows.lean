import Results.Genus.CapFourMass.IntervalPrefixRows
import Results.Genus.CapFourMass.IntervalTables

/-! Nested original short-prefix aggregation. Fin indices retain every original
r and m once; per-pivot constants can be checked and compiled independently. -/
open scoped BigOperators
namespace SubmittedGenus.CapFourMass.Interval.IndexedShort

noncomputable def pairSource (p r : ℕ) : ℝ :=
  ∑ j : Fin p, Polynomial.eval₂ (Nat.castRingHom ℝ) radius
    (RawGraph.rawPolynomial (p+1+j.val) r p 4)

def pairBox {p : ℕ} (b : Fin p → Box) : Box := sumBoxes b

theorem pair_contains {p r : ℕ} (b : Fin p → Box)
    (h : ∀ j, Contains (b j) (Polynomial.eval₂ (Nat.castRingHom ℝ) radius
      (RawGraph.rawPolynomial (p+1+j.val) r p 4))) :
    Contains (pairBox b) (pairSource p r) := sumBoxes_contains h

theorem pairSource_eq (p r : ℕ) : pairSource p r =
    ∑ m ∈ Finset.Ico (p+1) (2*p+1), Polynomial.eval₂ (Nat.castRingHom ℝ) radius
      (RawGraph.rawPolynomial m r p 4) := by
  unfold pairSource
  rw [Finset.sum_Ico_eq_sum_range]
  have hn : 2*p+1-(p+1)=p := by omega
  rw [hn]
  exact Fin.sum_univ_eq_sum_range (fun j => Polynomial.eval₂ (Nat.castRingHom ℝ) radius
    (RawGraph.rawPolynomial (p+1+j) r p 4)) p

noncomputable def rowSource (p : ℕ) : ℝ :=
  ∑ i : Fin (p-1), pairSource p (i.val+1)

def rowBox {p : ℕ} (b : Fin (p-1) → Box) : Box := sumBoxes b

theorem rowSource_eq (p : ℕ) : rowSource p = originalShortRow p := by
  unfold rowSource originalShortRow
  simp_rw [pairSource_eq]
  rw [Finset.sum_Ico_eq_sum_range]
  simpa only [Nat.add_comm] using Fin.sum_univ_eq_sum_range
    (fun r => ∑ m ∈ Finset.Ico (p+1) (2*p+1),
      Polynomial.eval₂ (Nat.castRingHom ℝ) radius (RawGraph.rawPolynomial m (r+1) p 4)) (p-1)

theorem row_contains {p : ℕ} (b : Fin (p-1) → Box)
    (h : ∀ i, Contains (b i) (pairSource p (i.val+1))) :
    Contains (rowBox b) (originalShortRow p) := by
  rw [←rowSource_eq]
  exact sumBoxes_contains h

/-- Combine any checked next original row with an accepted prefix. -/
theorem prefix_step {P : ℕ} {b row : Box}
    (hb : Contains b (originalShortPrefix P))
    (hr : Contains row (originalShortRow (P+1))) :
    Contains (add b row) (originalShortPrefix (P+1)) := by
  rw [originalShortPrefix_succ]
  exact add_contains hb hr

end SubmittedGenus.CapFourMass.Interval.IndexedShort
