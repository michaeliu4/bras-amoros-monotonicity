import Results.Genus.RawGraph.PackedAcceptance.ReflectionBitChunks

namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord

/-- Closed recursive word identity. The positive child keeps its first bit
fixed and reverses only its remaining macro-index order. -/
theorem bit_word_positive_remainder (L d q : ℕ) (hd : 0<d) (hdL : d<L) (hq : q≤L) :
    bitOrbitWord L d q = bitMacro L d q (bitLetter (q%d) (L%d) 0) ++
      (bitOrbitWord d (L%d) (q%d)).tail.reverse.flatMap (bitMacro L d q) := by
  rw [bit_word_negative_macros L d q hd hdL hq,List.flatMap_def]
  have he := negative_orbit_word_pos (fun t=>bitMacro L d q (bitLetter (q%d) (L%d) t)) d L hd
  simp only [Nat.mul_comm L] at he
  rw [he,List.flatten_cons]
  simp only [bitOrbitWord,←List.map_tail,List.tail_range,List.flatMap_def,
    List.map_reverse,List.map_map,Function.comp_def]

lemma bitMacro_ne_nil (L d q : ℕ) (b : BitLetter) : bitMacro L d q b ≠ [] := by
  unfold bitMacro
  generalize q/d+(if b.1 then 1 else 0)=A
  generalize L/d+(if b.2 then 1 else 0)=N
  unfold bitChunk
  split <;> simp

/-- Optional first-letter removal, followed by optional full reversal. -/
def wordMode {A : Type*} (tail rev : Bool) (w : List A) : List A :=
  let u := if tail then w.tail else w
  if rev then u.reverse else u

def wordValue {M : Type*} [Monoid M] (f : BitLetter→M) (w : List BitLetter) : M :=
  (w.map f).prod

/-- Constant-size power expression for each macro, including its headless
and reversed variants. No commutativity assumption is used. -/
def bitChunkValue {M : Type*} [Monoid M] (A N : ℕ) (f : BitLetter→M) (tail rev : Bool) : M :=
  let h := if tail then 1 else if A=0 then f (false,true) else f (true,true)
  if A=0 then
    if rev then f (false,false)^(N-1)*h else h*f (false,false)^(N-1)
  else
    if rev then f (false,false)^(N-A)*f (true,false)^(A-1)*h
    else h*(f (true,false)^(A-1)*f (false,false)^(N-A))

def bitMacroValue {M : Type*} [Monoid M] (L d q : ℕ) (f : BitLetter→M)
    (tail rev : Bool) (b : BitLetter) : M :=
  bitChunkValue (q/d+(if b.1 then 1 else 0)) (L/d+(if b.2 then 1 else 0)) f tail rev

lemma bitChunkValue_correct {M : Type*} [Monoid M] (A N : ℕ) (f : BitLetter→M)
    (tail rev : Bool) :
    bitChunkValue A N f tail rev = wordValue f (wordMode tail rev (bitChunk A N)) := by
  cases tail <;> cases rev <;> by_cases h : A=0 <;>
    simp [bitChunkValue,bitChunk,wordMode,wordValue,h,List.reverse_append,mul_assoc]

lemma bitMacroValue_correct {M : Type*} [Monoid M] (L d q : ℕ) (f : BitLetter→M)
    (tail rev : Bool) (b : BitLetter) :
    bitMacroValue L d q f tail rev b = wordValue f (wordMode tail rev (bitMacro L d q b)) :=
  bitChunkValue_correct _ _ _ _ _

lemma wordValue_append {M : Type*} [Monoid M] (f : BitLetter→M) (u v : List BitLetter) :
    wordValue f (u++v)=wordValue f u*wordValue f v := by
  simp [wordValue]

lemma wordValue_flatMap {M : Type*} [Monoid M] (f : BitLetter→M)
    (w : List BitLetter) (g : BitLetter→List BitLetter) :
    wordValue f (w.flatMap g)=wordValue (fun b=>wordValue f (g b)) w := by
  simp [wordValue,List.flatMap_def,List.prod_flatten,List.map_map,Function.comp_def]

#print axioms bit_word_positive_remainder
#print axioms bitChunkValue_correct
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord
