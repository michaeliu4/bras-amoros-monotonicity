import Results.Genus.RawGraph.PackedAcceptance.ReflectionNormalizedPairShift
import Results.Genus.RawGraph.PackedAcceptance.PairMonomialPhase

/-! Exact p-phase shift of a complete paired cycle after one matrix-step
trace rotation. The physical source signature and closure remain unchanged. -/
namespace SubmittedGenus.RawGraph.PackedAcceptance.PairMonomialShift
open ReflectionThresholdWord ReflectionPairedOrbit CompressedSignature
open scoped BigOperators Matrix

def oddOrbitShift (L δ cap q : ℕ) : ℕ :=
  ∑ k : Fin L, oddBound cap (reducedLetter L δ q ((δ*k.val)%L))

lemma oddBound_reduced (L δ cap q t : ℕ) (hq : q≤L-δ) (hcap : 1≤cap) :
    oddBound cap (reducedLetter L δ q t) =
      cap-1 + ((if t<q then 1 else 0) + (if L-δ≤t then 1 else 0)) := by
  by_cases ht : t<q
  · have hn : ¬L-δ≤t := by omega
    simp [reducedLetter, oddBound, ht, hn]
    omega
  · by_cases hb : t<L-δ
    · simp [reducedLetter, oddBound, ht, hb, show ¬L-δ≤t by omega]
    · simp [reducedLetter, oddBound, ht, hb, show L-δ≤t by omega]
      omega

lemma upper_threshold_count (L b : ℕ) (hb : b≤L) :
    (∑ k : Fin L, if b≤k.val then 1 else 0) = L-b := by
  have he : (fun k : Fin L => if b≤k.val then 1 else 0) =
      (fun k : Fin L => if k.val<b then 0 else 1) := by
    funext k
    split_ifs <;> omega
  rw [he, ← List.sum_ofFn, ofFn_cut L b hb]
  simp

theorem odd_orbit_shift_count (L δ cap q : ℕ) (hδ : 0<δ) (hdL : δ<L)
    (hc : Nat.Coprime δ L) (hq : q≤L-δ) (hcap : 1≤cap) :
    oddOrbitShift L δ cap q = (cap-1)*L+q+δ := by
  unfold oddOrbitShift
  rw [modular_sum L δ (by omega) hc (fun t => oddBound cap (reducedLetter L δ q t))]
  simp_rw [oddBound_reduced L δ cap q _ hq hcap]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, threshold_count L q (by omega),
    upper_threshold_count L (L-δ) (by omega)]
  simp [Nat.mul_comm, Nat.sub_sub_self hdL.le, Nat.add_assoc]

/-- Ordinary paired steps of the zero free path, before its final free vertex. -/
def oddInteriorShift (n δ cap q : ℕ) : ℕ :=
  ∑ k : Fin n, oddBound cap (reducedLetter (n+2) δ q ((δ*(k.val+1))%(n+2)))

/-- Trim initial A and final C. This is only a bound count; the open-path
head and final terminal matrix remain the responsibility of the path adapter. -/
theorem zero_odd_interior_shift_count (n δ cap q : ℕ) (hδ : 0<δ)
    (hdL : δ<n+2) (hc : Nat.Coprime δ (n+2)) (hq0 : 0<q)
    (hq : q≤n+2-δ) (hcap : 1≤cap) :
    oddInteriorShift n δ cap q = (cap-1)*n+(q+δ-2) := by
  have h := odd_orbit_shift_count (n+2) δ cap q hδ hdL hc hq hcap
  unfold oddOrbitShift at h
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc] at h
  simp only [Fin.val_zero, Fin.val_succ, Fin.val_castSucc, Fin.val_last,
    Nat.mul_zero, Nat.zero_mod] at h
  have hfirst : oddBound cap (reducedLetter (n+2) δ q 0) = cap := by
    simp [reducedLetter, oddBound, hq0]
  have hlast : oddBound cap (reducedLetter (n+2) δ q ((δ*(n+1))%(n+2))) = cap := by
    rw [show n+1=(n+2)-1 by omega, final_reduced_letter (n+2) δ q hδ hdL hq]
    simp [oddBound]
  rw [hfirst, hlast] at h
  change cap + (oddInteriorShift n δ cap q + cap) = (cap-1)*(n+2)+q+δ at h
  rw [Nat.mul_add] at h
  omega

lemma normalized_pPhase_wordShift (n δ cap q : ℕ) :
    wordShift (pPhasePairs (normalizedPairs n δ cap q)) = oddOrbitShift (n+2) δ cap q := by
  rw [pPhase_wordShift]
  simp only [normalizedPairs, List.map_ofFn, List.sum_ofFn, letterPair,
    oddOrbitShift, Function.comp_def]

/-- The adjacent cross-letter masks are retained by pPhasePairs. -/
theorem normalized_pPhase_factor {R : Type*} [CommSemiring R]
    (n δ cap q : ℕ) (hδ : 0<δ) (hdL : δ<n+2)
    (hc : Nat.Coprime δ (n+2)) (hq : q≤n+2-δ) (hcap : 1≤cap) (z : R) :
    signatureScalar (normalizedSignature n δ cap q) z =
      z^((cap-1)*(n+2)+q+δ) *
        Matrix.trace (shiftedWordMatrix z (pPhasePairs (normalizedPairs n δ cap q))) := by
  rw [cycle_pPhase_factor _ rfl _ (normalized_complete_word n δ cap q),
    normalized_pPhase_wordShift, odd_orbit_shift_count (n+2) δ cap q hδ hdL hc hq hcap]

variable {g : ℕ} [NeZero g]

theorem canonical_pPhase_factor {R : Type*} [CommSemiring R]
    (n r p δ cap : ℕ) (hr : 0<r) (hδ : 0<δ) (hcap : 1≤cap)
    (hp : p=r+g*δ) (hpm : p<g*(n+2)) (hc : Nat.Coprime δ (n+2))
    (a : Fin g) (ha : a≤mate r a) (ha0 : a≠0) (hpair : a≠mate r a) (z : R) :
    signatureScalar (canonicalSignature n r p δ cap hp hc a ha ha0 hpair) z =
      z^((cap-1)*(n+2)+cut g a.val r+δ) *
        Matrix.trace (shiftedWordMatrix z
          (pPhasePairs (normalizedPairs n δ cap (cut g a.val r)))) := by
  rw [canonicalSignature_normalized n r p δ cap hr hδ hp hpm hc a ha ha0 hpair]
  apply normalized_pPhase_factor n δ cap (cut g a.val r) hδ _ hc _ hcap z
  · exact Nat.lt_of_mul_lt_mul_left (by omega : g*δ<g*(n+2))
  · exact reduced_cut_bound g (n+2) r δ a.val (NeZero.pos g) (by omega)

#print axioms odd_orbit_shift_count
#print axioms zero_odd_interior_shift_count
#print axioms normalized_pPhase_factor
#print axioms canonical_pPhase_factor
end SubmittedGenus.RawGraph.PackedAcceptance.PairMonomialShift
