import Results.Genus.RawGraph.PackedAcceptance.ReflectionFixedPhase

/-! Exact ordered head/pair/tail partition of full fixed-path positions.
Empty pieces are empty lists, with no inserted vertex or closing factor. -/
namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionFixedPhase

/-- Number of complete aligned pairs; an unmatched final vertex is separate. -/
def pairCount (n h : ℕ) : ℕ := (n+2-alignment h)/2

def pairIndices (start count : ℕ) : List ℕ :=
  (List.range count).flatMap (fun k=>[start+2*k,start+2*k+1])

lemma pairIndices_range (start count : ℕ) : pairIndices start count=List.range' start (2*count) := by
  induction count with
  | zero => simp [pairIndices]
  | succ count ih =>
    unfold pairIndices at *
    rw [List.range_succ,List.flatMap_append,List.flatMap_singleton,ih]
    have he : [start+2*count,start+2*count+1]=List.range' (start+2*count) 2 := by simp [List.range']
    rw [he,List.range'_append_1]
    congr 1

def headIndices (h : ℕ) : List ℕ := List.range (alignment h)
def tailStart (n h : ℕ) : ℕ := alignment h+2*pairCount n h
def tailIndices (n h : ℕ) : List ℕ := List.range' (tailStart n h) (n+2-tailStart n h)

lemma head_length_le_one (h : ℕ) : (headIndices h).length≤1 := by
  simp only [headIndices,List.length_range]
  exact alignment_le_one h

lemma tailStart_le (n h : ℕ) : tailStart n h≤n+2 := by
  have:=alignment_le_one h
  unfold tailStart pairCount
  omega

lemma tail_length_le_one (n h : ℕ) : (tailIndices n h).length≤1 := by
  have:=alignment_le_one h
  simp only [tailIndices,List.length_range']
  unfold tailStart pairCount
  omega

/-- Every original position occurs exactly in its original order. -/
theorem source_indices (n h : ℕ) :
    List.range (n+2)=headIndices h ++ pairIndices (alignment h) (pairCount n h) ++ tailIndices n h := by
  rw [pairIndices_range]
  unfold headIndices tailIndices tailStart
  simp only [List.range_eq_range']
  have hb:=tailStart_le n h
  unfold tailStart at hb
  rw [show List.range' 0 (alignment h) ++ List.range' (alignment h) (2*pairCount n h)=
      List.range' 0 (alignment h+2*pairCount n h) by
    simpa only [Nat.zero_add] using (List.range'_append_1 (s:=0) (m:=alignment h) (n:=2*pairCount n h))]
  rw [show List.range' 0 (alignment h+2*pairCount n h) ++
      List.range' (alignment h+2*pairCount n h) (n+2-(alignment h+2*pairCount n h))=
      List.range' 0 (alignment h+2*pairCount n h+(n+2-(alignment h+2*pairCount n h))) by
    simpa only [Nat.zero_add] using (List.range'_append_1 (s:=0)
      (m:=alignment h+2*pairCount n h) (n:=n+2-(alignment h+2*pairCount n h)))]
  rw [Nat.add_sub_of_le hb]

/-- The ordered identity is valid for arbitrary labels or transfer factors. -/
theorem source_values_partition {A : Type*} (n h : ℕ) (f : ℕ→A) :
    (List.range (n+2)).map f=(headIndices h).map f ++
      (List.range (pairCount n h)).flatMap (fun k=>[f (alignment h+2*k),f (alignment h+2*k+1)]) ++
      (tailIndices n h).map f := by
  rw [source_indices n h]
  simp [pairIndices,List.map_append,List.map_flatMap,Function.comp_def]

/-- A retained pair has both of its original source positions in bounds. -/
lemma pair_index_bounds (n h k : ℕ) (hk : k<pairCount n h) :
    alignment h+2*k<n+2 ∧ alignment h+2*k+1<n+2 := by
  have:=tailStart_le n h
  unfold tailStart at this
  omega

def pairEven (n h : ℕ) (k : Fin (pairCount n h)) : Fin (n+2) :=
  ⟨alignment h+2*k.val,(pair_index_bounds n h k.val k.isLt).1⟩
def pairOdd (n h : ℕ) (k : Fin (pairCount n h)) : Fin (n+2) :=
  ⟨alignment h+2*k.val+1,(pair_index_bounds n h k.val k.isLt).2⟩

/-- Zero deletion filters original positions, leaving endpoint identities and
unpaired head/tail pieces intact; no window is converted to a dummy vertex. -/
theorem source_indices_without_zero (n h z : ℕ) :
    (List.range (n+2)).filter (fun i => decide (i ≠ z))=
      (headIndices h).filter (fun i => decide (i ≠ z)) ++
      (pairIndices (alignment h) (pairCount n h)).filter (fun i => decide (i ≠ z)) ++
      (tailIndices n h).filter (fun i => decide (i ≠ z)) := by
  rw [source_indices n h]
  simp only [List.filter_append]

#print axioms source_indices
#print axioms source_values_partition
#print axioms source_indices_without_zero
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionFixedPhase
