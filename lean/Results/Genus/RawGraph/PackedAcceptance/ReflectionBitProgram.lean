import Results.Genus.RawGraph.PackedAcceptance.ReflectionBitRecursion

namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord

/-- Expressions use four shared input registers. Natural exponents are
stored as powers rather than expanded into repeated factors. -/
inductive BitExpr where
  | one
  | atom (b : BitLetter)
  | mul (x y : BitExpr)
  | pow (x : BitExpr) (n : ℕ)

def BitExpr.eval {M : Type*} [Monoid M] (f : BitLetter→M) : BitExpr→M
  | .one=>1
  | .atom b=>f b
  | .mul x y=>x.eval f*y.eval f
  | .pow x n=>x.eval f^n

def BitExpr.size : BitExpr→ℕ
  | .one=>1
  | .atom _=>1
  | .mul x y=>1+x.size+y.size
  | .pow x _=>1+x.size

def chunkExpr (A N : ℕ) (tail rev : Bool) : BitExpr :=
  let h := if tail then .one else if A=0 then .atom (false,true) else .atom (true,true)
  if A=0 then
    if rev then .mul (.pow (.atom (false,false)) (N-1)) h
    else .mul h (.pow (.atom (false,false)) (N-1))
  else
    if rev then .mul (.mul (.pow (.atom (false,false)) (N-A)) (.pow (.atom (true,false)) (A-1))) h
    else .mul h (.mul (.pow (.atom (true,false)) (A-1)) (.pow (.atom (false,false)) (N-A)))

def macroExpr (L d q : ℕ) (tail rev : Bool) (b : BitLetter) : BitExpr :=
  chunkExpr (q/d+(if b.1 then 1 else 0)) (L/d+(if b.2 then 1 else 0)) tail rev

lemma chunkExpr_eval {M : Type*} [Monoid M] (f : BitLetter→M) (A N : ℕ) (tail rev : Bool) :
    (chunkExpr A N tail rev).eval f=bitChunkValue A N f tail rev := by
  cases tail <;> cases rev <;> by_cases h : A=0 <;> simp [chunkExpr,BitExpr.eval,bitChunkValue,h]

lemma chunkExpr_size (A N : ℕ) (tail rev : Bool) : (chunkExpr A N tail rev).size≤7 := by
  cases tail <;> cases rev <;> by_cases h : A=0 <;> simp [chunkExpr,BitExpr.size,h]

lemma macroExpr_eval {M : Type*} [Monoid M] (f : BitLetter→M) (L d q : ℕ)
    (tail rev : Bool) (b : BitLetter) :
    (macroExpr L d q tail rev b).eval f=bitMacroValue L d q f tail rev b :=
  chunkExpr_eval _ _ _ _ _

lemma macroExpr_size (L d q : ℕ) (tail rev : Bool) (b : BitLetter) :
    (macroExpr L d q tail rev b).size≤7 := chunkExpr_size _ _ _ _

/-- Cache all four macro values exactly once at every stage. -/
def cacheBits {M : Type*} (f : BitLetter→M) : BitLetter→M :=
  let ff:=f (false,false)
  let ft:=f (false,true)
  let tf:=f (true,false)
  let tt:=f (true,true)
  fun b=>if b.1 then (if b.2 then tt else tf) else (if b.2 then ft else ff)

lemma cacheBits_eq {M : Type*} (f : BitLetter→M) : cacheBits f=f := by
  funext b
  rcases b with ⟨x,y⟩
  cases x <;> cases y <;> rfl

/-- A shared dictionary stage has one recursive continuation. The Boolean
places that continuation before or after the pref, preserving order. -/
inductive BitProgram where
  | done (b : BitLetter) (n : ℕ)
  | stage (dictionary : BitLetter→BitExpr) (pref : BitExpr) (rev : Bool) (next : BitProgram)

def BitProgram.eval {M : Type*} [Monoid M] (f : BitLetter→M) : BitProgram→M
  | .done b n=>f b^n
  | .stage dictionary pref rev next=>
    let values:=cacheBits (fun b=>(dictionary b).eval f)
    let p:=pref.eval f
    let v:=next.eval values
    if rev then v*p else p*v

def BitProgram.depth : BitProgram→ℕ
  | .done _ _=>0
  | .stage _ _ _ next=>next.depth+1

/-- Counts every expression node in all four dictionary entries, every
pref, every combine node, and the final atom-power pair. Shared register
references are atom nodes; exponents are stored natural-number fields. -/
def BitProgram.size : BitProgram→ℕ
  | .done _ _=>2
  | .stage ds p _ next=>1+(ds (false,false)).size+(ds (false,true)).size+
    (ds (true,false)).size+(ds (true,true)).size+p.size+next.size

def bitCompile (L d q : ℕ) (tail rev : Bool) : BitProgram :=
  if h : 0<d ∧ d<L then
    .stage (macroExpr L d q false rev)
      (macroExpr L d q tail rev (bitLetter (q%d) (L%d) 0)) rev
      (bitCompile d (L%d) (q%d) true (!rev))
  else .done (bitLetter q d 0) (L-(if tail then 1 else 0))
termination_by L

lemma bitCompile_size (L d q : ℕ) (tail rev : Bool) :
    (bitCompile L d q tail rev).size≤36*(bitCompile L d q tail rev).depth+2 := by
  rw [bitCompile]
  split
  · rename_i h
    simp only [BitProgram.size,BitProgram.depth]
    have ih:=bitCompile_size d (L%d) (q%d) true (!rev)
    have a:=macroExpr_size L d q false rev (false,false)
    have b:=macroExpr_size L d q false rev (false,true)
    have c:=macroExpr_size L d q false rev (true,false)
    have e:=macroExpr_size L d q false rev (true,true)
    have p:=macroExpr_size L d q tail rev (bitLetter (q%d) (L%d) 0)
    omega
  · simp [BitProgram.size,BitProgram.depth]
termination_by L

#print axioms chunkExpr_eval
#print axioms bitCompile_size
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord
