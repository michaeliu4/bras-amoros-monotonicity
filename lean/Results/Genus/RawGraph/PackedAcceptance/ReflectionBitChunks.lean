import Results.Genus.RawGraph.PackedAcceptance.ReflectionIntervalChunks

namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord

abbrev BitLetter := Bool × Bool

def bitLetter (q d t : ℕ) : BitLetter := (decide (t<q),decide (t<d))

def bitChunk (A N : ℕ) : List BitLetter :=
  if A=0 then [(false,true)] ++ List.replicate (N-1) (false,false)
  else [(true,true)] ++ List.replicate (A-1) (true,false) ++ List.replicate (N-A) (false,false)

def bitMacro (L d q : ℕ) (b : BitLetter) : List BitLetter :=
  bitChunk (q/d+(if b.1 then 1 else 0)) (L/d+(if b.2 then 1 else 0))

def bitOrbitWord (L d q : ℕ) : List BitLetter :=
  (List.range L).map (fun k=>bitLetter q d ((d*k)%L))

lemma map_range_two {A : Type*} (N a : ℕ) (ha : a≤N) (x y : A) :
    (List.range N).map (fun k=>if k<a then x else y)=
      List.replicate a x ++ List.replicate (N-a) y := by
  have hn : N=a+(N-a) := by omega
  conv_lhs => rw [hn,List.range_add,List.map_append,List.map_map]
  have h1 : (List.range a).map (fun k=>if k<a then x else y)=List.replicate a x := by
    calc
      _=(List.range a).map (fun _=>x) := by
        apply List.map_congr_left
        intro k hk
        simp only [List.mem_range.mp hk,↓reduceIte]
      _=_ := by simp
  have h2 : (List.range (N-a)).map (fun k=>if a+k<a then x else y)=List.replicate (N-a) y := by
    calc
      _=(List.range (N-a)).map (fun _=>y) := by
        apply List.map_congr_left
        intro k _
        simp only [show ¬a+k<a by omega,↓reduceIte]
      _=_ := by simp
  simpa only [Function.comp_def,h1,h2]

lemma bit_index_word (N A : ℕ) (hN : 0<N) (hA : A≤N) :
    (List.range N).map (fun k:ℕ=>(decide (k<A),decide (k=0)))=bitChunk A N := by
  have hs : List.range N=0::(List.range (N-1)).map Nat.succ := by
    conv_lhs => rw [show N=(N-1)+1 by omega]
    rw [List.range_succ_eq_map]
  rw [hs,List.map_cons,List.map_map]
  unfold bitChunk
  by_cases hz : A=0
  · subst A
    simp [Function.comp_def]
  · have hp : 0<A := by omega
    rw [if_neg hz]
    simp only [hp,decide_true]
    have hm : (List.range (N-1)).map ((fun k:ℕ=>(decide (k<A),decide (k=0))) ∘ Nat.succ)=
        (List.range (N-1)).map (fun k=>if k<A-1 then (true,false) else (false,false)) := by
      apply List.map_congr_left
      intro k _
      dsimp only [Function.comp_def]
      by_cases hk : k<A-1
      · have hk' : k+1<A := by omega
        simp [hk,hk',Nat.succ_eq_add_one]
      · have hk' : ¬k+1<A := by omega
        simp [hk,hk',Nat.succ_eq_add_one]
    rw [hm,map_range_two (N-1) (A-1) (by omega)]
    rw [show N-1-(A-1)=N-A by omega]
    rfl

lemma affine_bit_word (L d q j : ℕ) (hd : 0<d) (hdL : d<L) (hq : q≤L) :
    (List.range (chunkLength L d j)).map (fun i=>bitLetter q d (chunkStart L d j+d*i))=
      bitMacro L d q (bitLetter (q%d) (L%d) (chunkStart L d j)) := by
  have hs:=(chunkStart_spec L d j hd).1
  have hN:=chunkLength_pos L d j hd hdL
  have hA : cut d (chunkStart L d j) q≤chunkLength L d j := by
    rw [chunkLength_eq_cut L d j hd]
    exact cut_mono d (chunkStart L d j) hd hq
  have hm : (List.range (chunkLength L d j)).map (fun i=>bitLetter q d (chunkStart L d j+d*i))=
      (List.range (chunkLength L d j)).map (fun i:ℕ=>(decide (i<cut d (chunkStart L d j) q),decide (i=0))) := by
    apply List.map_congr_left
    intro i _
    have hi : chunkStart L d j+d*i<d ↔ i=0 := by
      constructor
      · intro hi
        by_contra hz
        have hh:=Nat.mul_le_mul_left d (show 1 ≤ i by omega)
        omega
      · intro hi
        simpa [hi] using hs
    simp only [bitLetter,←lt_cut_iff d (chunkStart L d j) q i hd,hi]
  rw [hm,bit_index_word _ _ hN hA]
  unfold bitMacro bitLetter
  simp only [decide_eq_true_eq]
  rw [chunkLength_eq_cut L d j hd,cut_residue_formula d (chunkStart L d j) L hd hs,
    cut_residue_formula d (chunkStart L d j) q hd hs]

/-- The two-bit alphabet is closed under quotient reduction: the new two
cuts are q%d and the new positive Euclidean step L%d. -/
theorem bit_word_negative_macros (L d q : ℕ) (hd : 0<d) (hdL : d<L) (hq : q≤L) :
    bitOrbitWord L d q=(List.range d).flatMap (fun j=>
      bitMacro L d q (bitLetter (q%d) (L%d) (-((j*L:ℕ):ZMod d)).val)) := by
  unfold bitOrbitWord
  conv_lhs => rw [←original_index_chunks L d hd]
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro j _
  rw [List.range'_eq_map_range,List.map_map,←chunkStart_negative_mod L d j hd]
  rw [←affine_bit_word L d q j hd hdL hq]
  apply List.map_congr_left
  intro i hi
  dsimp only [Function.comp_def]
  rw [chunk_coordinate L d j i hd (List.mem_range.mp hi)]

#print axioms bit_index_word
#print axioms affine_bit_word
#print axioms bit_word_negative_macros
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord
