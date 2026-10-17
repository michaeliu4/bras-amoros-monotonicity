import Results.Genus.RawGraph.PackedAcceptance.ReflectionChunkClosure
import Results.Genus.RawGraph.PackedAcceptance.ReflectionDeltaOneProduct

/-! Exact first-edge shift counts for coprime paired source words. These
counts do not enumerate source positions or move the terminal vertex. -/
namespace SubmittedGenus.RawGraph.PackedAcceptance.PairMonomialShift
open ReflectionThresholdWord ReflectionPairedOrbit
open scoped BigOperators

def orbitShift (L δ cap q : ℕ) : ℕ :=
  ∑ k : Fin L, evenBound cap (reducedLetter L δ q ((δ*k.val)%L))

def interiorShift (n δ cap q : ℕ) : ℕ :=
  ∑ k : Fin n, evenBound cap (reducedLetter (n+2) δ q ((δ*(k.val+1))%(n+2)))

lemma evenBound_reduced (L δ cap q t : ℕ) (hcap : 1≤cap) :
    evenBound cap (reducedLetter L δ q t) = cap-1 + if t<q then 1 else 0 := by
  unfold evenBound reducedLetter
  split_ifs <;> simp_all

lemma threshold_count (L q : ℕ) (hq : q≤L) :
    (∑ k : Fin L, if k.val<q then 1 else 0) = q := by
  rw [← List.sum_ofFn, ofFn_cut L q hq]
  simp

/-- Coprime modular multiplication preserves every residue sum. -/
lemma modular_sum (L δ : ℕ) (hL : 0<L) (hc : Nat.Coprime δ L) (f : ℕ→ℕ) :
    (∑ k : Fin L, f ((δ*k.val)%L)) = ∑ k : Fin L, f k.val := by
  letI : NeZero L := ⟨ne_of_gt hL⟩
  let e : Fin L ≃ Fin L := unitCoordinates (ZMod.unitOfCoprime δ hc)
  apply Fintype.sum_equiv e
  intro k
  congr 1
  dsimp only [e]
  rw [unitCoordinates_val]
  change (δ*k.val)%L=((δ : ZMod L)*(k.val : ZMod L)).val
  rw [← Nat.cast_mul, ZMod.val_natCast]

/-- Every below-cut residue contributes one extra unit above cap minus one. -/
theorem orbit_shift_count (L δ cap q : ℕ) (hL : 0<L)
    (hc : Nat.Coprime δ L) (hq : q≤L) (hcap : 1≤cap) :
    orbitShift L δ cap q = (cap-1)*L+q := by
  unfold orbitShift
  rw [modular_sum L δ hL hc (fun t => evenBound cap (reducedLetter L δ q t))]
  simp_rw [evenBound_reduced L δ cap q _ hcap]
  rw [Finset.sum_add_distrib, threshold_count L q hq]
  simp [Nat.mul_comm]

/-- Original source cut restriction is retained in the cycle interface. -/
theorem paired_cycle_shift_count (n δ cap q : ℕ) (hδ : 0<δ)
    (hdL : δ<n+2) (hc : Nat.Coprime δ (n+2)) (hq : q≤n+2-δ)
    (hcap : 1≤cap) :
    orbitShift (n+2) δ cap q = (cap-1)*(n+2)+q :=
  orbit_shift_count (n+2) δ cap q (by omega) hc (by omega) hcap

/-- Trim initial A and final C, leaving n=L-2 complete ordinary pairs.
The final free vertex is not part of this shift count. -/
theorem zero_interior_shift_count (n δ cap q : ℕ) (hδ : 0<δ)
    (hdL : δ<n+2) (hc : Nat.Coprime δ (n+2)) (hq0 : 0<q)
    (hq : q≤n+2-δ) (hcap : 1≤cap) :
    interiorShift n δ cap q = (cap-1)*n+(q-1) := by
  have h := paired_cycle_shift_count n δ cap q hδ hdL hc hq hcap
  unfold orbitShift at h
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc] at h
  simp only [Fin.val_zero, Fin.val_succ, Fin.val_castSucc, Fin.val_last,
    Nat.mul_zero, Nat.zero_mod] at h
  have hfirst : evenBound cap (reducedLetter (n+2) δ q 0) = cap := by
    simp [reducedLetter, evenBound, hq0]
  have hlast : evenBound cap (reducedLetter (n+2) δ q ((δ*(n+1))%(n+2))) = cap-1 := by
    rw [show n+1=(n+2)-1 by omega, final_reduced_letter (n+2) δ q hδ hdL hq]
    simp [evenBound]
  rw [hfirst, hlast] at h
  change cap + (interiorShift n δ cap q + (cap-1)) = (cap-1)*(n+2)+q at h
  rw [Nat.mul_add] at h
  omega

#print axioms modular_sum
#print axioms orbit_shift_count
#print axioms zero_interior_shift_count
end SubmittedGenus.RawGraph.PackedAcceptance.PairMonomialShift
