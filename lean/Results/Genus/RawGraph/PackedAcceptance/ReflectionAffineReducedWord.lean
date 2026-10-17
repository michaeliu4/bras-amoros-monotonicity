import Results.Genus.RawGraph.PackedAcceptance.ReflectionDeltaOneWord

/-! The general original-source three-letter word reduced to its true orbit
modulus. This is an exact arithmetic interface for future Euclidean word
compression; it does not assert that ordinary runs are uniformly short. -/
namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord

lemma affine_threshold (g a t b : ℕ) (ha : a<g) :
    a+g*t<g*b ↔ t<b := by
  constructor
  · intro h
    by_contra hn
    have hm:=Nat.mul_le_mul_left g (by omega : b≤t)
    omega
  · intro h
    have hm:=Nat.mul_le_mul_left g (by omega : t+1≤b)
    rw [Nat.mul_succ] at hm
    omega

/-- Both original physical cuts become integer cuts on the exact modular
orbit coordinate; the first cut retains the pivot and coset phase. -/
theorem affine_letter_reduced (g L r δ a t : ℕ) (hg : 0<g) (ha : a<g) :
    letter (g*L) r (g*δ) (a+g*t)=
      if t<cut g a r then .fullStrong
      else if t<L-δ then .carryCarry else .carryStrong := by
  unfold letter
  rw [←Nat.mul_sub_left_distrib]
  simp only [affine_threshold g a t (L-δ) ha,←lt_cut_iff g a r t hg]

/-- Uniform exact source alphabet for every modular-affine paired orbit.
This is order-preserving and leaves the complete modular k-sequence intact. -/
theorem affine_word_reduced (g L r δ a : ℕ) (hg : 0<g) (ha : a<g) :
    (List.range L).map (fun k=>letter (g*L) r (g*δ) (a+g*((δ*k)%L)))=
      (List.range L).map (fun k=>if (δ*k)%L<cut g a r then Letter.fullStrong
        else if (δ*k)%L<L-δ then Letter.carryCarry else Letter.carryStrong) := by
  apply List.map_congr_left
  intro k _
  exact affine_letter_reduced g L r δ a _ hg ha

lemma reduced_cut_bound (g L r δ a : ℕ) (hg : 0<g) (hp : r+g*δ<g*L) :
    cut g a r≤L-δ := by
  apply cut_le g a r (L-δ) hg
  rw [Nat.mul_sub_left_distrib]
  omega

#print axioms affine_letter_reduced
#print axioms affine_word_reduced
#print axioms reduced_cut_bound
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord
