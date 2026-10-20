import Results.Genus.RawGraph.PackedAcceptance.ReflectionChunkWord

namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord

/-- The last orbit coordinate is exactly the wrap cut, for every positive
step below the modulus. Coprimality is unnecessary for this endpoint fact. -/
lemma final_modular_coordinate (L δ : ℕ) (hδ : 0<δ) (hdL : δ<L) :
    (δ*(L-1))%L=L-δ := by
  have hL : 0<L := lt_trans hδ hdL
  have he : δ*(L-1)=(δ-1)*L+(L-δ) := by
    nlinarith [Nat.sub_add_cancel hδ,Nat.sub_add_cancel hdL.le,Nat.sub_add_cancel hL]
  rw [he,Nat.mul_comm (δ-1) L,Nat.mul_add_mod,Nat.mod_eq_of_lt (by omega : L-δ<L)]

/-- The final pair is always the carry/strong letter, with the strong
edge being the actual first-state closing edge. -/
theorem final_reduced_letter (L δ q : ℕ) (hδ : 0<δ) (hdL : δ<L) (hq : q≤L-δ) :
    reducedLetter L δ q ((δ*(L-1))%L)=.carryStrong := by
  rw [final_modular_coordinate L δ hδ hdL]
  simp [reducedLetter,show ¬L-δ<q by omega]

theorem final_affine_letter (g L r δ a : ℕ) (hg : 0<g) (hδ : 0<δ)
    (hdL : δ<L) (ha : a<g) (hp : r+g*δ<g*L) :
    letter (g*L) r (g*δ) (a+g*((δ*(L-1))%L))=.carryStrong := by
  rw [affine_letter_reduced g L r δ a _ hg ha]
  exact final_reduced_letter L δ (cut g a r) hδ hdL (reduced_cut_bound g L r δ a hg hp)

#print axioms final_modular_coordinate
#print axioms final_reduced_letter
#print axioms final_affine_letter
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord
