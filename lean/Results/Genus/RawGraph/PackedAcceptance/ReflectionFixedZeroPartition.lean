import Results.Genus.RawGraph.PackedAcceptance.ReflectionFixedOrdinaryPartition

namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionFixedZeroPartition
open ReflectionFixedPhase

def leftHead (h : ℕ) := min (h-2) (2-alignment h)
def leftPairs (h : ℕ) := (h-2-leftHead h)/2
def leftEnd (h : ℕ) := leftHead h+2*leftPairs h
def rightStart (n h : ℕ) := min n (h+2)
def rightPairs (n h : ℕ) := (n-rightStart n h)/2
def rightEnd (n h : ℕ) := rightStart n h+2*rightPairs n h
def leftOffset (h : ℕ) := ordinaryPairOffset h
def rightOffset (h : ℕ) := (h+3)/2

theorem bounds (n h : ℕ) (hh : h≤n) :
    leftHead h≤leftEnd h ∧ leftEnd h≤rightStart n h ∧ rightStart n h≤rightEnd n h ∧
    rightEnd n h≤n ∧ leftHead h≤2 ∧ rightStart n h-leftEnd h≤5 ∧ n-rightEnd n h≤1 := by
  have ha:=alignment_le_one h
  simp only [leftEnd,leftPairs,leftHead,rightEnd,rightPairs,rightStart]
  omega

lemma segment_split (a b c : ℕ) (hab : a≤b) (hbc : b≤c) :
    List.range' a (c-a)=List.range' a (b-a)++List.range' b (c-b) := by
  have he : a+(b-a)=b := by omega
  calc
    List.range' a (c-a)=List.range' a ((b-a)+(c-b)) := by congr 1;omega
    _=List.range' a (b-a)++List.range' (a+(b-a)) (c-b) := List.range'_append_1.symm
    _=List.range' a (b-a)++List.range' b (c-b) := by rw [he]

/-- Two complete pair windows, separated by at most five literal steps.
The middle includes both retained pins, the deleted-zero gap, and alignment
remainders. The actual terminal vertex is outside the ordinary-factor list. -/
theorem indices (n h : ℕ) (hh : h≤n) :
    List.range n=List.range (leftHead h)++pairIndices (leftHead h) (leftPairs h)++
      List.range' (leftEnd h) (rightStart n h-leftEnd h)++
      pairIndices (rightStart n h) (rightPairs n h)++
      List.range' (rightEnd n h) (n-rightEnd n h) := by
  have hb:=bounds n h hh
  rw [pairIndices_range,pairIndices_range,List.range_eq_range',List.range_eq_range']
  rw [show List.range' 0 n=List.range' 0 (leftHead h)++List.range' (leftHead h) (n-leftHead h) by
    simpa using segment_split 0 (leftHead h) n (by omega) (by omega)]
  rw [segment_split (leftHead h) (leftEnd h) n hb.1 (by omega)]
  rw [segment_split (leftEnd h) (rightStart n h) n hb.2.1 (by omega)]
  rw [segment_split (rightStart n h) (rightEnd n h) n hb.2.2.1 hb.2.2.2.1]
  simp only [Nat.sub_zero,show leftEnd h-leftHead h=2*leftPairs h by unfold leftEnd;omega,
    show rightEnd n h-rightStart n h=2*rightPairs n h by unfold rightEnd;omega,List.append_assoc]

theorem values {A : Type*} (n h : ℕ) (hh : h≤n) (f : ℕ→A) :
    (List.range n).map f=(List.range (leftHead h)).map f ++
      (List.range (leftPairs h)).flatMap (fun k=>[f (leftHead h+2*k),f (leftHead h+2*k+1)]) ++
      (List.range' (leftEnd h) (rightStart n h-leftEnd h)).map f ++
      (List.range (rightPairs n h)).flatMap (fun k=>[f (rightStart n h+2*k),f (rightStart n h+2*k+1)]) ++
      (List.range' (rightEnd n h) (n-rightEnd n h)).map f := by
  rw [indices n h hh]
  simp [pairIndices,List.map_append,List.map_flatMap]

lemma left_positions (h k : ℕ) (hk : k<leftPairs h) :
    leftHead h+2*k=alignment h+2*(leftOffset h+k) ∧
    0<leftHead h+2*k ∧ leftHead h+2*k+3<h := by
  have ha:=alignment_le_one h
  have hhead : leftHead h=2-alignment h := by unfold leftPairs leftHead at *;omega
  unfold leftOffset ordinaryPairOffset
  unfold leftPairs at hk
  omega

lemma right_positions (n h k : ℕ) (hk : k<rightPairs n h) :
    rightStart n h+2*k+1=alignment h+2*(rightOffset h+k) ∧
    h+1<rightStart n h+2*k+1 ∧ rightStart n h+2*k+2<n+1 := by
  have hs : rightStart n h=h+2 := by unfold rightPairs rightStart at *;omega
  have hm:=Nat.mod_lt h (by omega : 0<2)
  unfold rightPairs at hk
  unfold rightOffset alignment
  omega

#print axioms values
#print axioms left_positions
#print axioms right_positions
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionFixedZeroPartition
