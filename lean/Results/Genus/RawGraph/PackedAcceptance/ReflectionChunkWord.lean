import Results.Genus.RawGraph.PackedAcceptance.ReflectionEuclideanChunks

namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord

/-- Three ordered intervals, with the wrap region explicitly marked. -/
def reducedLetter (L δ q t : ℕ) : Letter :=
  if t<q then .fullStrong else if t<L-δ then .carryCarry else .carryStrong

def chunkFullCount (L δ q j : ℕ) : ℕ := cut δ (chunkStart L δ j) q

/-- A whole quotient chunk ends in exactly one wrap letter. -/
def chunkWord (L δ q j : ℕ) : List Letter :=
  List.replicate (chunkFullCount L δ q j) .fullStrong ++
  List.replicate (chunkLength L δ j-1-chunkFullCount L δ q j) .carryCarry ++ [.carryStrong]

lemma chunkLength_eq_cut (L δ j : ℕ) (hδ : 0<δ) :
    chunkLength L δ j=cut δ (chunkStart L δ j) L := by
  have he (i : ℕ) : i<chunkLength L δ j ↔ i<cut δ (chunkStart L δ j) L :=
    (chunk_index_iff L δ j i hδ).trans (lt_cut_iff δ (chunkStart L δ j) L i hδ).symm
  have h1:=he (chunkLength L δ j)
  have h2:=he (cut δ (chunkStart L δ j) L)
  omega

lemma chunk_before_wrap (L δ j : ℕ) (hδ : 0<δ) (hdL : δ<L) :
    cut δ (chunkStart L δ j) (L-δ)=chunkLength L δ j-1 := by
  have hn:=chunkLength_pos L δ j hδ hdL
  have he (i : ℕ) : i<cut δ (chunkStart L δ j) (L-δ) ↔ i<chunkLength L δ j-1 := by
    rw [lt_cut_iff δ (chunkStart L δ j) (L-δ) i hδ]
    have hh:=chunk_index_iff L δ j (i+1) hδ
    rw [Nat.mul_succ] at hh
    omega
  have h1:=he (cut δ (chunkStart L δ j) (L-δ))
  have h2:=he (chunkLength L δ j-1)
  omega

lemma chunkFullCount_le (L δ q j : ℕ) (hδ : 0<δ) (hdL : δ<L) (hq : q≤L-δ) :
    chunkFullCount L δ q j≤chunkLength L δ j-1 := by
  unfold chunkFullCount
  rw [←chunk_before_wrap L δ j hδ hdL]
  exact cut_mono δ (chunkStart L δ j) hδ hq

/-- Increasing-delta traversal inside one quotient block is exactly A* B* C. -/
theorem affine_chunk_word (L δ q j : ℕ) (hδ : 0<δ) (hdL : δ<L) (hq : q≤L-δ) :
    (List.range (chunkLength L δ j)).map
      (fun i=>reducedLetter L δ q (chunkStart L δ j+δ*i))=chunkWord L δ q j := by
  have hn:=chunkLength_pos L δ j hδ hdL
  have hq':=chunkFullCount_le L δ q j hδ hdL hq
  have he : chunkFullCount L δ q j+(chunkLength L δ j-1-chunkFullCount L δ q j)+1=
      chunkLength L δ j := by omega
  have hm:=map_range_three (chunkFullCount L δ q j)
    (chunkLength L δ j-1-chunkFullCount L δ q j)
    Letter.fullStrong Letter.carryCarry Letter.carryStrong
  rw [he] at hm
  unfold chunkWord
  rw [←hm]
  apply List.map_congr_left
  intro i _
  unfold reducedLetter
  simp only [←lt_cut_iff δ (chunkStart L δ j) q i hδ,
    ←lt_cut_iff δ (chunkStart L δ j) (L-δ) i hδ,
    chunk_before_wrap L δ j hδ hdL]
  change (if i<chunkFullCount L δ q j then _ else if i<chunkLength L δ j-1 then _ else _)=_
  rw [show chunkFullCount L δ q j+(chunkLength L δ j-1-chunkFullCount L δ q j)=
    chunkLength L δ j-1 by omega]

/-- Quotient-block source indices are mapped in their original order. -/
theorem modular_chunk_word (L δ q j : ℕ) (hδ : 0<δ) (hdL : δ<L) (hq : q≤L-δ) :
    (List.range' (chunkBoundary L δ j) (chunkLength L δ j)).map
      (fun k=>reducedLetter L δ q ((δ*k)%L))=chunkWord L δ q j := by
  rw [List.range'_eq_map_range,List.map_map]
  rw [←affine_chunk_word L δ q j hδ hdL hq]
  apply List.map_congr_left
  intro i hi
  dsimp only [Function.comp_def]
  rw [chunk_coordinate L δ j i hδ (List.mem_range.mp hi)]

/-- Exact ordered word identity for every positive delta<L. No coprimality,
rotation, matrix commutativity, or finite signature checker is used here. -/
theorem modular_word_chunks (L δ q : ℕ) (hδ : 0<δ) (hdL : δ<L) (hq : q≤L-δ) :
    (List.range L).map (fun k=>reducedLetter L δ q ((δ*k)%L))=
      (List.range δ).flatMap (chunkWord L δ q) := by
  conv_lhs => rw [←original_index_chunks L δ hδ]
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro j _
  exact modular_chunk_word L δ q j hδ hdL hq

/-- The same order-preserving identity interpreted in any noncommutative monoid. -/
theorem modular_product_chunks {A : Type*} [Monoid A] (f : Letter→A)
    (L δ q : ℕ) (hδ : 0<δ) (hdL : δ<L) (hq : q≤L-δ) :
    ((List.range L).map (fun k=>f (reducedLetter L δ q ((δ*k)%L)))).prod=
      ((List.range δ).map (fun j=>
        f .fullStrong^chunkFullCount L δ q j *
        f .carryCarry^(chunkLength L δ j-1-chunkFullCount L δ q j) * f .carryStrong)).prod := by
  rw [show (List.range L).map (fun k=>f (reducedLetter L δ q ((δ*k)%L)))=
    ((List.range L).map (fun k=>reducedLetter L δ q ((δ*k)%L))).map f by simp]
  rw [modular_word_chunks L δ q hδ hdL hq,List.map_flatMap,List.flatMap_def,List.prod_flatten,List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro j _
  simp [chunkWord,List.prod_append,mul_assoc]

/-- Instantiation of the chunk identity to the original affine source letters. -/
theorem original_affine_word_chunks (g L r δ a : ℕ) (hg : 0<g) (hδ : 0<δ)
    (hdL : δ<L) (ha : a<g) (hp : r+g*δ<g*L) :
    (List.range L).map (fun k=>letter (g*L) r (g*δ) (a+g*((δ*k)%L)))=
      (List.range δ).flatMap (chunkWord L δ (cut g a r)) := by
  rw [affine_word_reduced g L r δ a hg ha]
  exact modular_word_chunks L δ (cut g a r) hδ hdL (reduced_cut_bound g L r δ a hg hp)

#print axioms modular_word_chunks
#print axioms modular_product_chunks
#print axioms original_affine_word_chunks
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord
