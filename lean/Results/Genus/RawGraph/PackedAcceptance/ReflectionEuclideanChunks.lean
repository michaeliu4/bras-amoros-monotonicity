import Results.Genus.RawGraph.PackedAcceptance.ReflectionAffineReducedWord

/-! Exact quotient-block decomposition of the ordered modular orbit word.
Chunk starts use the NEGATIVE remainder phase. This file makes no recursive
complexity assertion and never changes multiplication order. -/
namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord

lemma cut_le_iff (g a t k : ℕ) (hg : 0<g) :
    cut g a t≤k ↔ t≤a+g*k := by
  have h:=lt_cut_iff g a t k hg
  omega

lemma cut_mono (g a : ℕ) (hg : 0<g) : Monotone (cut g a) := by
  intro t u htu
  apply (cut_le_iff g a t (cut g a u) hg).mpr
  exact htu.trans ((cut_le_iff g a u (cut g a u) hg).mp le_rfl)

/-- Ceiling division of the j-th unwrapped multiple of L by delta. -/
def chunkBoundary (L δ j : ℕ) : ℕ := cut δ 0 (j*L)

def chunkStart (L δ j : ℕ) : ℕ := δ*chunkBoundary L δ j-j*L

def chunkLength (L δ j : ℕ) : ℕ := chunkBoundary L δ (j+1)-chunkBoundary L δ j

lemma boundary_mono (L δ : ℕ) (hδ : 0<δ) : Monotone (chunkBoundary L δ) := by
  intro i j hij
  exact cut_mono δ 0 hδ (Nat.mul_le_mul_right L hij)

lemma boundary_zero (L δ : ℕ) : chunkBoundary L δ 0=0 := by simp [chunkBoundary,cut]

lemma boundary_le_iff (L δ j k : ℕ) (hδ : 0<δ) :
    chunkBoundary L δ j≤k ↔ j*L≤δ*k := by
  simpa only [chunkBoundary,Nat.zero_add] using cut_le_iff δ 0 (j*L) k hδ

lemma lt_boundary_iff (L δ j k : ℕ) (hδ : 0<δ) :
    k<chunkBoundary L δ j ↔ δ*k<j*L := by
  simpa only [chunkBoundary,Nat.zero_add] using lt_cut_iff δ 0 (j*L) k hδ

lemma boundary_end (L δ : ℕ) (hδ : 0<δ) : chunkBoundary L δ δ=L := by
  apply le_antisymm
  · exact (boundary_le_iff L δ δ L hδ).mpr le_rfl
  · by_contra hn
    have hmul:=Nat.mul_lt_mul_of_pos_left (by omega : chunkBoundary L δ δ<L) hδ
    have hlo:=(boundary_le_iff L δ δ (chunkBoundary L δ δ) hδ).mp le_rfl
    omega

lemma boundary_spec (L δ j : ℕ) (hδ : 0<δ) :
    j*L≤δ*chunkBoundary L δ j ∧ δ*chunkBoundary L δ j<j*L+δ := by
  have hlo:=(boundary_le_iff L δ j (chunkBoundary L δ j) hδ).mp le_rfl
  refine ⟨hlo,?_⟩
  by_cases hz : chunkBoundary L δ j=0
  · rw [hz,Nat.mul_zero]
    omega
  · have hp : chunkBoundary L δ j-1<chunkBoundary L δ j := by omega
    have hh:=(lt_boundary_iff L δ j _ hδ).mp hp
    have he : δ*(chunkBoundary L δ j-1)+δ=δ*chunkBoundary L δ j := by
      nlinarith [Nat.sub_add_cancel (by omega : 1≤chunkBoundary L δ j)]
    omega

lemma chunkStart_spec (L δ j : ℕ) (hδ : 0<δ) :
    chunkStart L δ j<δ ∧ chunkStart L δ j+j*L=δ*chunkBoundary L δ j := by
  have h:=boundary_spec L δ j hδ
  unfold chunkStart
  omega

/-- The sign of the reduced phase is negative, including all modular wraps. -/
theorem chunkStart_negative_mod (L δ j : ℕ) (hδ : 0<δ) :
    chunkStart L δ j=(-((j*L:ℕ):ZMod δ)).val := by
  letI : NeZero δ := ⟨ne_of_gt hδ⟩
  have hs:=chunkStart_spec L δ j hδ
  have hc:=congrArg (fun v:ℕ=>(v:ZMod δ)) hs.2
  rw [Nat.cast_add] at hc
  have hz : ((δ*chunkBoundary L δ j:ℕ):ZMod δ)=0 := by
    rw [Nat.cast_mul,ZMod.natCast_self,zero_mul]
  rw [hz] at hc
  have he : (chunkStart L δ j:ZMod δ)=-((j*L:ℕ):ZMod δ) := eq_neg_of_add_eq_zero_left hc
  have hv:=congrArg ZMod.val he
  simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt hs.1] using hv

lemma chunk_index_iff (L δ j i : ℕ) (hδ : 0<δ) :
    i<chunkLength L δ j ↔ chunkStart L δ j+δ*i<L := by
  have hb:=boundary_mono L δ hδ (Nat.le_succ j)
  have hs:=chunkStart_spec L δ j hδ
  have hmul : δ*(chunkBoundary L δ j+i)=j*L+(chunkStart L δ j+δ*i) := by nlinarith [hs.2]
  have hb' := lt_boundary_iff L δ (j+1) (chunkBoundary L δ j+i) hδ
  rw [hmul,Nat.add_mul,Nat.one_mul] at hb'
  unfold chunkLength
  omega

lemma chunkLength_pos (L δ j : ℕ) (hδ : 0<δ) (hdL : δ<L) : 0<chunkLength L δ j := by
  apply (chunk_index_iff L δ j 0 hδ).mpr
  have hs:=chunkStart_spec L δ j hδ
  simpa only [Nat.mul_zero,Nat.add_zero] using hs.1.trans hdL

lemma chunk_coordinate (L δ j i : ℕ) (hδ : 0<δ) (hi : i<chunkLength L δ j) :
    (δ*(chunkBoundary L δ j+i))%L=chunkStart L δ j+δ*i := by
  have ht:=(chunk_index_iff L δ j i hδ).mp hi
  have hs:=chunkStart_spec L δ j hδ
  have he : δ*(chunkBoundary L δ j+i)=j*L+(chunkStart L δ j+δ*i) := by nlinarith [hs.2]
  rw [he,Nat.mul_comm j L,Nat.mul_add_mod,Nat.mod_eq_of_lt ht]

/-- A monotone sequence of cut positions concatenates consecutive source
intervals without permutation, omission, or repetition. -/
lemma ranges_at_boundaries (b : ℕ→ℕ) (hb : Monotone b) (n : ℕ) :
    (List.range n).flatMap (fun j=>List.range' (b j) (b (j+1)-b j))=
      List.range' (b 0) (b n-b 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ,List.flatMap_append,List.flatMap_singleton,ih]
    have h0:=hb (Nat.zero_le n)
    have hn:=hb (Nat.le_succ n)
    change b n≤b (n+1) at hn
    have he : b 0+(b n-b 0)=b n := by omega
    have he2 : List.range' (b n) (b (n+1)-b n)=
        List.range' (b 0+(b n-b 0)) (b (n+1)-b n) := by rw [he]
    rw [he2,List.range'_append_1]
    have hsum : (b n-b 0)+(b (n+1)-b n)=b (n+1)-b 0 := by omega
    exact congrArg (fun t=>List.range' (b 0) t) hsum

/-- Exact ordered decomposition of all L original indices into delta chunks. -/
theorem original_index_chunks (L δ : ℕ) (hδ : 0<δ) :
    (List.range δ).flatMap (fun j=>List.range' (chunkBoundary L δ j) (chunkLength L δ j))=
      List.range L := by
  change (List.range δ).flatMap (fun j=>List.range' (chunkBoundary L δ j)
    (chunkBoundary L δ (j+1)-chunkBoundary L δ j))=_
  rw [ranges_at_boundaries _ (boundary_mono L δ hδ),boundary_zero,boundary_end L δ hδ]
  simp [List.range_eq_range']

#print axioms chunkStart_negative_mod
#print axioms chunk_coordinate
#print axioms original_index_chunks
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord
