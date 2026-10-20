import Results.Genus.RawGraph.PackedAcceptance.Checker
import Mathlib.Data.Nat.Choose.Sum

namespace SubmittedGenus.RawGraph.PackedAcceptance
open scoped BigOperators

/-- Exact original loop ranges: m=3…M, p=2…min(P,m−1), r=1…p−1. -/
abbrev Triple (M P : ℕ) :=
  (mi : Fin (M-2)) × (pi : Fin (min P (mi.val+2)-1)) × Fin (pi.val+1)

def Triple.m {M P : ℕ} (t : Triple M P) := t.1.val+3
def Triple.p {M P : ℕ} (t : Triple M P) := t.2.1.val+2
def Triple.r {M P : ℕ} (t : Triple M P) := t.2.2.val+1

lemma Triple.parameters {M P a : ℕ} (t : Triple M P) (ha : a=4 ∨ a=5) :
    Parameters t.m t.r t.p a := by
  have hp := t.2.1.isLt
  have hr := t.2.2.isLt
  dsimp [Triple.m,Triple.r,Triple.p]
  have hmin := Nat.min_le_right P (t.1.val+2)
  exact ⟨by omega,by omega,by omega,ha⟩

lemma Triple.bounds {M P : ℕ} (t : Triple M P) :
    3≤t.m ∧ t.m≤M ∧ 2≤t.p ∧ t.p≤P := by
  have hm := t.1.isLt
  have hp := t.2.1.isLt
  have hmin := Nat.min_le_left P (t.1.val+2)
  dsimp [Triple.m,Triple.p]
  omega

lemma sum_fin_succ_choose (n : ℕ) : (∑i:Fin n,(i.val+1))=(n+1).choose 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last,ih]
    have hc := Nat.choose_succ_succ (n+1) 1
    change (n+1+1).choose 2=(n+1).choose 1+(n+1).choose 2 at hc
    rw [Nat.choose_one_right] at hc
    omega

/-- Coverage cardinality is checked with one arithmetic term per multiplicity,
not by constructing millions of graph objects inside the kernel. -/
lemma triple_card (M P : ℕ) (hP : 2≤P) :
    Fintype.card (Triple M P)=∑mi:Fin (M-2),(min P (mi.val+2)).choose 2 := by
  simp only [Triple,Fintype.card_sigma,Fintype.card_fin,sum_fin_succ_choose]
  apply Finset.sum_congr rfl
  intro mi _
  congr 1
  have hq : 1≤min P (mi.val+2) := le_min (by omega) (by omega)
  omega

set_option maxRecDepth 10000 in
lemma original_cap4_triple_count : Fintype.card (Triple 597 300)=17775550 := by
  rw [triple_card _ _ (by decide)]
  decide

set_option maxRecDepth 10000 in
lemma original_cap5_sufficient_triple_count : Fintype.card (Triple 149 149)=540274 := by
  rw [triple_card _ _ (by decide)]
  decide

set_option maxRecDepth 10000 in
lemma original_cap5_retained_triple_count : Fintype.card (Triple 293 293)=4149466 := by
  rw [triple_card _ _ (by decide)]
  decide

/-- Exact cap-four multiplicity cutoff for every retained genus. -/
lemma cap4_multiplicity_outside_zero {m r p g : ℕ} (hm : 598≤m) (hg : g≤897) :
    (rawPolynomial m r p 4).coeff g=0 := by
  by_cases hp : Parameters m r p 4
  · apply rawPolynomial_coeff_zero_of_support
    have hr := hp.1
    have hrp := hp.2.1
    omega
  · rw [rawPolynomial_invalid hp]
    simp

/-- The extra m=150…293 terms in the retained cap-five file are all zero
through300, so regeneration through149 has exactly the same coefficients. -/
lemma cap5_multiplicity_outside_zero {m r p g : ℕ} (hm : 150≤m) (hg : g≤300) :
    (rawPolynomial m r p 5).coeff g=0 := by
  by_cases hp : Parameters m r p 5
  · apply rawPolynomial_coeff_zero_of_support
    have hr := hp.1
    have hrp := hp.2.1
    omega
  · rw [rawPolynomial_invalid hp]
    simp

#print axioms original_cap4_triple_count
#print axioms original_cap5_sufficient_triple_count
#print axioms original_cap5_retained_triple_count
#print axioms cap4_multiplicity_outside_zero
#print axioms cap5_multiplicity_outside_zero
end SubmittedGenus.RawGraph.PackedAcceptance
