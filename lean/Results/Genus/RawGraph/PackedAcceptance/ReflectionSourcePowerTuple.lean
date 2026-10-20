import Results.Genus.RawGraph.PackedAcceptance.ReflectionSourcePowerProgram

namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord

/-- Explicit materialized dictionary, used to distinguish register caching
from higher-order closure behavior in the retained cost control. -/
structure BitTable (M : Type*) where
  ff : M
  ft : M
  tf : M
  tt : M

def BitTable.lookup {M : Type*} (t : BitTable M) (b : BitLetter) : M :=
  if b.1 then (if b.2 then t.tt else t.tf) else (if b.2 then t.ft else t.ff)

def BitTable.ofFn {M : Type*} (f : BitLetter→M) : BitTable M :=
  ⟨f (false,false),f (false,true),f (true,false),f (true,true)⟩

lemma BitTable.lookup_ofFn {M : Type*} (f : BitLetter→M) :
    (BitTable.ofFn f).lookup=f := by
  funext b
  rcases b with ⟨x,y⟩
  cases x <;> cases y <;> rfl

def BitProgram.evalTuple {M : Type*} [Monoid M] (f : BitLetter→M) : BitProgram→M
  | .done b n=>f b^n
  | .stage ds p rev next=>
    let t:=BitTable.ofFn (fun b=>(ds b).eval f)
    let a:=p.eval f
    let b:=next.evalTuple t.lookup
    if rev then b*a else a*b

lemma BitProgram.evalTuple_eq {M : Type*} [Monoid M] (p : BitProgram) (f : BitLetter→M) :
    p.evalTuple f=p.eval f := by
  induction p generalizing f with
  | done b n=>rfl
  | stage ds p rev next ih=>
    simp only [evalTuple,eval,cacheBits_eq,BitTable.lookup_ofFn,ih]

def SourceProgram.evalTuple {M : Type*} [Monoid M] (p : SourceProgram) (f : Letter→M) : M :=
  let t:=BitTable.ofFn (fun b=>(p.dictionary b).eval f)
  t.lookup p.head*p.continuation.evalTuple t.lookup

lemma SourceProgram.evalTuple_eq {M : Type*} [Monoid M] (p : SourceProgram) (f : Letter→M) :
    p.evalTuple f=p.eval f := by
  simp [evalTuple,eval,cacheBits_eq,BitTable.lookup_ofFn,BitProgram.evalTuple_eq]

#print axioms SourceProgram.evalTuple_eq
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord
