import Results.Genus.RawGraph.PackedAcceptance.ReflectionChunkMacros
import Mathlib.Data.List.Range

/-! Exact transport from the negative reduced phase to a positive Euclidean
remainder, reversing only the order of macro letters after the fixed first
macro. Individual macro contents and the original first state are unchanged. -/
namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord

lemma negative_residue_complement (n d k : ℕ) (hk : k<n) :
    (-((d*(k+1):ℕ):ZMod (n+1))).val=(d*(n-k))%(n+1) := by
  have he : d*(n-k)+d*(k+1)=d*(n+1) := by
    nlinarith [Nat.sub_add_cancel (by omega : k≤n)]
  have hc:=congrArg (fun v:ℕ=>(v:ZMod (n+1))) he
  rw [Nat.cast_add] at hc
  have hz : ((d*(n+1):ℕ):ZMod (n+1))=0 := by
    rw [Nat.cast_mul,ZMod.natCast_self,mul_zero]
  rw [hz] at hc
  have hn : -((d*(k+1):ℕ):ZMod (n+1))=((d*(n-k):ℕ):ZMod (n+1)) :=
    (eq_neg_of_add_eq_zero_left hc).symm
  rw [hn,ZMod.val_natCast]

/-- Negative-phase orbit order fixes zero and reverses the positive tail. -/
theorem negative_orbit_word {A : Type*} (f : ℕ→A) (n d : ℕ) :
    (List.range (n+1)).map (fun k=>f (-((d*k:ℕ):ZMod (n+1))).val)=
      f 0 :: ((List.range' 1 n).map (fun k=>f ((d*k)%(n+1)))).reverse := by
  rw [List.range_succ_eq_map,List.map_cons,List.map_map,←List.map_reverse,List.reverse_range',List.map_map]
  simp only [Nat.mul_zero,Nat.cast_zero,neg_zero,ZMod.val_zero,Nat.one_add,Nat.add_sub_cancel]
  congr 1
  apply List.map_congr_left
  intro k hk
  dsimp only [Function.comp_def]
  rw [negative_residue_complement n d k (List.mem_range.mp hk)]
  simp only [Nat.succ_eq_add_one,Nat.add_sub_cancel]

/-- The same transport written at an arbitrary positive modulus. -/
theorem negative_orbit_word_pos {A : Type*} (f : ℕ→A) (L d : ℕ) (hL : 0<L) :
    (List.range L).map (fun k=>f (-((d*k:ℕ):ZMod L)).val)=
      f 0 :: ((List.range' 1 (L-1)).map (fun k=>f (((d%L)*k)%L))).reverse := by
  obtain ⟨n,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (ne_of_gt hL)
  rw [negative_orbit_word f n d]
  congr 2
  change (List.range' 1 n).map (fun k=>f ((d*k)%(n+1)))=
    (List.range' 1 n).map (fun k=>f (((d%(n+1))*k)%(n+1)))
  apply List.map_congr_left
  intro k _
  congr 1
  simp only [Nat.mul_mod,Nat.mod_mod]

/-- Exact positive-remainder continuation of the chunk reduction. Reversal
acts on the list of macro words before flattening; it never reverses the
letters inside a macro. -/
theorem quotient_macros_positive_remainder (L δ q : ℕ) (hδ : 0<δ)
    (hdL : δ<L) (hq : q≤L-δ) :
    (List.range L).map (fun k=>reducedLetter L δ q ((δ*k)%L))=
      quotientMacro L δ q 0 ++
        (((List.range' 1 (δ-1)).map (fun j=>quotientMacro L δ q (((L%δ)*j)%δ))).reverse).flatten := by
  rw [modular_word_quotient_macros L δ q hδ hdL hq,List.flatMap_def]
  have he := negative_orbit_word_pos (quotientMacro L δ q) δ L hδ
  simp only [Nat.mul_comm L] at he
  rw [he,List.flatten_cons]

#print axioms negative_orbit_word
#print axioms negative_orbit_word_pos
#print axioms quotient_macros_positive_remainder
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord
