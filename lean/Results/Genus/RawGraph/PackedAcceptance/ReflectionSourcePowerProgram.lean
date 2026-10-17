import Results.Genus.RawGraph.PackedAcceptance.ReflectionBitProgramSound
import Results.Genus.RawGraph.PackedAcceptance.ReflectionBitProgramBound

namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord

inductive LetterExpr where
  | atom (a : Letter)
  | mul (x y : LetterExpr)
  | pow (x : LetterExpr) (n : ℕ)

def LetterExpr.eval {M : Type*} [Monoid M] (f : Letter→M) : LetterExpr→M
  | .atom a=>f a
  | .mul x y=>x.eval f*y.eval f
  | .pow x n=>x.eval f^n

def LetterExpr.size : LetterExpr→ℕ
  | .atom _=>1
  | .mul x y=>1+x.size+y.size
  | .pow x _=>1+x.size

def sourceMacroWord (L d q : ℕ) (b : BitLetter) : List Letter :=
  let A:=q/d+(if b.1 then 1 else 0)
  let N:=L/d+(if b.2 then 1 else 0)
  List.replicate A .fullStrong ++ List.replicate (N-1-A) .carryCarry ++ [.carryStrong]

def sourceMacroExpr (L d q : ℕ) (b : BitLetter) : LetterExpr :=
  let A:=q/d+(if b.1 then 1 else 0)
  let N:=L/d+(if b.2 then 1 else 0)
  .mul (.mul (.pow (.atom .fullStrong) A) (.pow (.atom .carryCarry) (N-1-A))) (.atom .carryStrong)

lemma sourceMacroExpr_eval {M : Type*} [Monoid M] (f : Letter→M) (L d q : ℕ) (b : BitLetter) :
    (sourceMacroExpr L d q b).eval f=((sourceMacroWord L d q b).map f).prod := by
  simp [sourceMacroExpr,LetterExpr.eval,sourceMacroWord,mul_assoc]

lemma sourceMacroExpr_size (L d q : ℕ) (b : BitLetter) :
    (sourceMacroExpr L d q b).size=7 := by rfl

lemma quotientMacro_sourceBits (L d q t : ℕ) :
    quotientMacro L d q t=sourceMacroWord L d q (bitLetter (q%d) (L%d) t) := by
  simp [quotientMacro,sourceMacroWord,bitLetter]

theorem source_word_bit_continuation (L d q : ℕ) (hd : 0<d) (hdL : d<L) (hq : q≤L-d) :
    (List.range L).map (fun k=>reducedLetter L d q ((d*k)%L))=
      sourceMacroWord L d q (bitLetter (q%d) (L%d) 0) ++
        (bitOrbitWord d (L%d) (q%d)).tail.reverse.flatMap (sourceMacroWord L d q) := by
  rw [quotient_macros_positive_remainder L d q hd hdL hq]
  simp only [quotientMacro_sourceBits,bitOrbitWord,←List.map_tail,List.tail_range,
    List.flatMap_def,List.map_reverse,List.map_map,Function.comp_def]

/-- Four initial A/B/C power expressions feed one shared-register Euclidean
program. The head is retained separately from the reversed child tail. -/
structure SourceProgram where
  dictionary : BitLetter→LetterExpr
  head : BitLetter
  continuation : BitProgram

def SourceProgram.eval {M : Type*} [Monoid M] (f : Letter→M) (p : SourceProgram) : M :=
  let values:=cacheBits (fun b=>(p.dictionary b).eval f)
  values p.head*p.continuation.eval values

def SourceProgram.size (p : SourceProgram) : ℕ :=
  2+(p.dictionary (false,false)).size+(p.dictionary (false,true)).size+
    (p.dictionary (true,false)).size+(p.dictionary (true,true)).size+p.continuation.size

def sourceCompile (L d q : ℕ) : SourceProgram :=
  ⟨sourceMacroExpr L d q,bitLetter (q%d) (L%d) 0,bitCompile d (L%d) (q%d) true true⟩

/-- Source-exact arbitrary noncommutative monoid evaluation, without
expanding or validating the L individual letters. -/
theorem sourceCompile_correct {M : Type*} [Monoid M] (f : Letter→M)
    (L d q : ℕ) (hd : 0<d) (hdL : d<L) (hq : q≤L-d) :
    (sourceCompile L d q).eval f=
      (((List.range L).map (fun k=>reducedLetter L d q ((d*k)%L))).map f).prod := by
  simp only [sourceCompile,SourceProgram.eval,cacheBits_eq]
  rw [bitCompile_correct (fun b=>(sourceMacroExpr L d q b).eval f) d (L%d) (q%d)
    (Nat.mod_lt L hd) (Nat.le_of_lt (Nat.mod_lt q hd)) true true]
  rw [source_word_bit_continuation L d q hd hdL hq]
  simp [sourceMacroExpr_eval,wordValue,wordMode,List.flatMap_def,List.prod_flatten,
    List.map_map,Function.comp_def]

/-- Includes every initial expression node, each dictionary register
reference, every recursive stage, and the actual final source letter. -/
theorem sourceCompile_size_bound (L d q : ℕ) (hdL : d≤L) :
    (sourceCompile L d q).size≤72*L.log2+68 := by
  simp only [sourceCompile,SourceProgram.size,sourceMacroExpr_size]
  have hs:=bitCompile_size_logarithmic d (L%d) (q%d) true true
  have hm:=log2_mono_bound d L hdL
  omega

/-- Original modular-affine source letters, in their original orientation,
compile to the same reusable logarithmic power program. -/
theorem original_sourceCompile_correct {M : Type*} [Monoid M] (f : Letter→M)
    (g L r d a : ℕ) (hg : 0<g) (hd : 0<d) (hdL : d<L) (ha : a<g)
    (hp : r+g*d<g*L) :
    (sourceCompile L d (cut g a r)).eval f=
      (((List.range L).map (fun k=>letter (g*L) r (g*d) (a+g*((d*k)%L)))).map f).prod := by
  rw [affine_word_reduced g L r d a hg ha]
  exact sourceCompile_correct f L d (cut g a r) hd hdL (reduced_cut_bound g L r d a hg hp)

#print axioms sourceCompile_correct
#print axioms sourceCompile_size_bound
#print axioms original_sourceCompile_correct
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord
