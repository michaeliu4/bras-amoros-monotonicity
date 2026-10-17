import Results.Genus.RawGraph.PackedAcceptance.ReflectionChunkWord

/-! Closed-form quotient exponents for the exact negative-phase chunks.
Only two remainder thresholds determine each macro. No bound on recursive
depth or actual evaluator runtime is asserted. -/
namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord

lemma cut_residue_formula (δ s t : ℕ) (hδ : 0<δ) (hs : s<δ) :
    cut δ s t=t/δ+(if s<t%δ then 1 else 0) := by
  have ht:=Nat.mod_add_div t δ
  have hr:=Nat.mod_lt t hδ
  have hc:=(cut_le_iff δ s t (cut δ s t) hδ).mp le_rfl
  by_cases hsr : s<t%δ
  · rw [if_pos hsr]
    apply le_antisymm
    · apply (cut_le_iff δ s t (t/δ+1) hδ).mpr
      nlinarith
    · have hl : t/δ<cut δ s t := (lt_cut_iff δ s t (t/δ) hδ).mpr (by nlinarith)
      omega
  · rw [if_neg hsr,Nat.add_zero]
    apply le_antisymm
    · apply (cut_le_iff δ s t (t/δ) hδ).mpr
      omega
    · by_contra hn
      have hm:=Nat.mul_le_mul_left δ (by omega : cut δ s t+1≤t/δ)
      rw [Nat.mul_succ] at hm
      omega

/-- A macro dictionary with two exact interval tests on a residue s<delta. -/
def quotientMacro (L δ q s : ℕ) : List Letter :=
  let A := q/δ+(if s<q%δ then 1 else 0)
  let N := L/δ+(if s<L%δ then 1 else 0)
  List.replicate A .fullStrong ++ List.replicate (N-1-A) .carryCarry ++ [.carryStrong]

lemma chunkWord_quotientMacro (L δ q j : ℕ) (hδ : 0<δ) :
    chunkWord L δ q j=quotientMacro L δ q (chunkStart L δ j) := by
  have hs:=(chunkStart_spec L δ j hδ).1
  unfold chunkWord chunkFullCount quotientMacro
  rw [chunkLength_eq_cut L δ j hδ,cut_residue_formula δ (chunkStart L δ j) L hδ hs,
    cut_residue_formula δ (chunkStart L δ j) q hδ hs]

/-- First exact modulus reduction: L letters become delta ordered macros,
whose starts follow the negative modular step -L modulo delta. -/
theorem modular_word_quotient_macros (L δ q : ℕ) (hδ : 0<δ) (hdL : δ<L)
    (hq : q≤L-δ) :
    (List.range L).map (fun k=>reducedLetter L δ q ((δ*k)%L))=
      (List.range δ).flatMap (fun j=>quotientMacro L δ q (-((j*L:ℕ):ZMod δ)).val) := by
  rw [modular_word_chunks L δ q hδ hdL hq]
  apply List.flatMap_congr
  intro j _
  rw [chunkWord_quotientMacro L δ q j hδ,chunkStart_negative_mod L δ j hδ]

/-- The original physical source letters factor through the same exact
negative-phase macro dictionary. -/
theorem original_affine_quotient_macros (g L r δ a : ℕ) (hg : 0<g) (hδ : 0<δ)
    (hdL : δ<L) (ha : a<g) (hp : r+g*δ<g*L) :
    (List.range L).map (fun k=>letter (g*L) r (g*δ) (a+g*((δ*k)%L)))=
      (List.range δ).flatMap (fun j=>
        quotientMacro L δ (cut g a r) (-((j*L:ℕ):ZMod δ)).val) := by
  rw [affine_word_reduced g L r δ a hg ha]
  exact modular_word_quotient_macros L δ (cut g a r) hδ hdL
    (reduced_cut_bound g L r δ a hg hp)

#print axioms cut_residue_formula
#print axioms modular_word_quotient_macros
#print axioms original_affine_quotient_macros
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord
