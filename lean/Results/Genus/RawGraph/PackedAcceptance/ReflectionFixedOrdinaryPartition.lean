import Results.Genus.RawGraph.PackedAcceptance.ReflectionFixedPairPartition

/-! Ordinary factors exclude the terminal vertex. The original first loop is
peeled before compiling complete interior two-step pair factors. -/
namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionFixedPhase

def ordinaryHead (n h : ℕ) : ℕ := min (n+1) (2-alignment h)
def ordinaryPairs (n h : ℕ) : ℕ := (n+1-ordinaryHead n h)/2
def ordinaryTailStart (n h : ℕ) : ℕ := ordinaryHead n h+2*ordinaryPairs n h
def ordinaryPairOffset (h : ℕ) : ℕ := 1-alignment h

lemma ordinaryHead_bounds (n h : ℕ) : 1≤ordinaryHead n h ∧ ordinaryHead n h≤2 ∧ ordinaryHead n h≤n+1 := by
  have:=alignment_le_one h
  unfold ordinaryHead
  omega

lemma ordinaryTail_bounds (n h : ℕ) : ordinaryTailStart n h≤n+1 ∧ n+1-ordinaryTailStart n h≤1 := by
  have:=ordinaryHead_bounds n h
  unfold ordinaryTailStart ordinaryPairs
  omega

/-- Exact ordinary-factor positions, with at most two head factors and one
tail factor. The original last vertex is deliberately outside this list. -/
theorem ordinary_indices (n h : ℕ) :
    List.range (n+1)=List.range (ordinaryHead n h) ++
      pairIndices (ordinaryHead n h) (ordinaryPairs n h) ++
      List.range' (ordinaryTailStart n h) (n+1-ordinaryTailStart n h) := by
  rw [pairIndices_range]
  simp only [List.range_eq_range']
  unfold ordinaryTailStart
  have hb:=(ordinaryTail_bounds n h).1
  unfold ordinaryTailStart at hb
  rw [show List.range' 0 (ordinaryHead n h) ++ List.range' (ordinaryHead n h) (2*ordinaryPairs n h)=
      List.range' 0 (ordinaryHead n h+2*ordinaryPairs n h) by
    simpa only [Nat.zero_add] using (List.range'_append_1 (s:=0) (m:=ordinaryHead n h) (n:=2*ordinaryPairs n h))]
  rw [show List.range' 0 (ordinaryHead n h+2*ordinaryPairs n h) ++
      List.range' (ordinaryHead n h+2*ordinaryPairs n h) (n+1-(ordinaryHead n h+2*ordinaryPairs n h))=
      List.range' 0 (ordinaryHead n h+2*ordinaryPairs n h+(n+1-(ordinaryHead n h+2*ordinaryPairs n h))) by
    simpa only [Nat.zero_add] using (List.range'_append_1 (s:=0)
      (m:=ordinaryHead n h+2*ordinaryPairs n h) (n:=n+1-(ordinaryHead n h+2*ordinaryPairs n h)))]
  rw [Nat.add_sub_of_le hb]

theorem ordinary_values_partition {A : Type*} (n h : ℕ) (f : ℕ→A) :
    (List.range (n+1)).map f=(List.range (ordinaryHead n h)).map f ++
      (List.range (ordinaryPairs n h)).flatMap
        (fun k=>[f (ordinaryHead n h+2*k),f (ordinaryHead n h+2*k+1)]) ++
      (List.range' (ordinaryTailStart n h) (n+1-ordinaryTailStart n h)).map f := by
  rw [ordinary_indices n h]
  simp [pairIndices,List.map_append,List.map_flatMap]

/-- Every body pair starts after the original loop endpoint and has a real
outgoing edge to a third source vertex. Global parity is unchanged. -/
lemma ordinary_pair_positions (n h k : ℕ) (hk : k<ordinaryPairs n h) :
    ordinaryHead n h+2*k=alignment h+2*(ordinaryPairOffset h+k) ∧
    0<ordinaryHead n h+2*k ∧
    ordinaryHead n h+2*k+1<n+1 ∧ ordinaryHead n h+2*k+2<n+2 := by
  have ha:=alignment_le_one h
  have hh:=ordinaryHead_bounds n h
  have ht:=(ordinaryTail_bounds n h).1
  unfold ordinaryTailStart at ht
  have hhead : ordinaryHead n h=2-alignment h := by
    unfold ordinaryHead ordinaryPairs at *
    omega
  unfold ordinaryPairOffset
  omega

lemma ordinaryPairs_le (n h : ℕ) : ordinaryPairs n h≤n+2 := by
  unfold ordinaryPairs
  omega

#print axioms ordinary_values_partition
#print axioms ordinary_pair_positions
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionFixedPhase
