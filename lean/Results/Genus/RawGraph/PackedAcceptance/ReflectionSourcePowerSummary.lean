import Results.Genus.RawGraph.PackedAcceptance.ReflectionPowerSummary
import Results.Genus.RawGraph.PackedAcceptance.ReflectionSourcePowerTuple

namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord

lemma freeMonoid_pow_word {A : Type*} (v : FreeMonoid A) (n : ℕ) :
    FreeMonoid.toList (v^n)=repeatWord v.toList n := by
  induction n with
  | zero=>simp [repeatWord,FreeMonoid.toList_one]
  | succ n ih=>rw [pow_succ',FreeMonoid.toList_mul,ih,repeatWord_succ]

lemma freeMonoid_word_product {A : Type*} (w : List A) :
    FreeMonoid.toList ((w.map FreeMonoid.of).prod)=w := by
  induction w with
  | nil=>rfl
  | cons a w ih=>simpa [FreeMonoid.toList_mul,FreeMonoid.toList_of] using congrArg (List.cons a) ih

def BitExpr.summary {M : Type*} [Monoid M] (inputs : BitLetter→PowerSummary M) : BitExpr→PowerSummary M
  | .one=>PowerSummary.empty
  | .atom b=>inputs b
  | .mul x y=>(x.summary inputs).mul (y.summary inputs)
  | .pow x n=>(x.summary inputs).pow n

lemma BitExpr.summary_rep {A M : Type*} [Monoid M] (f : A→M) (e : BitExpr)
    (inputs : BitLetter→PowerSummary M) (g : BitLetter→FreeMonoid A)
    (h : ∀b,(inputs b).Rep f (g b).toList) :
    (e.summary inputs).Rep f (e.eval g).toList := by
  induction e with
  | one=>exact PowerSummary.empty_rep f
  | atom b=>exact h b
  | mul x y hx hy=>
    simpa only [summary,eval,FreeMonoid.toList_mul] using PowerSummary.mul_rep f _ _ _ _ hx hy
  | pow x n hx=>
    simpa only [summary,eval,freeMonoid_pow_word] using PowerSummary.pow_rep f _ _ hx n

def BitProgram.summary {M : Type*} [Monoid M] (inputs : BitLetter→PowerSummary M) : BitProgram→PowerSummary M
  | .done b n=>(inputs b).pow n
  | .stage ds p rev next=>
    let table:=BitTable.ofFn (fun b=>(ds b).summary inputs)
    let a:=p.summary inputs
    let b:=next.summary table.lookup
    if rev then b.mul a else a.mul b

lemma BitProgram.summary_rep {A M : Type*} [Monoid M] (f : A→M) (p : BitProgram)
    (inputs : BitLetter→PowerSummary M) (g : BitLetter→FreeMonoid A)
    (h : ∀b,(inputs b).Rep f (g b).toList) :
    (p.summary inputs).Rep f (p.eval g).toList := by
  induction p generalizing inputs g with
  | done b n=>
    simpa only [summary,eval,freeMonoid_pow_word] using PowerSummary.pow_rep f _ _ (h b) n
  | stage ds p rev next ih=>
    have hp:=BitExpr.summary_rep f p inputs g h
    have hn:=ih (fun b=>(ds b).summary inputs) (fun b=>(ds b).eval g)
      (fun b=>BitExpr.summary_rep f (ds b) inputs g h)
    cases rev
    · simpa only [summary,eval,BitTable.lookup_ofFn,cacheBits_eq,Bool.false_eq_true,↓reduceIte,
        FreeMonoid.toList_mul] using PowerSummary.mul_rep f _ _ _ _ hp hn
    · simpa only [summary,eval,BitTable.lookup_ofFn,cacheBits_eq,↓reduceIte,
        FreeMonoid.toList_mul] using PowerSummary.mul_rep f _ _ _ _ hn hp

def LetterExpr.summary {M : Type*} [Monoid M] (f : Letter→M) : LetterExpr→PowerSummary M
  | .atom a=>PowerSummary.atom (f a)
  | .mul x y=>(x.summary f).mul (y.summary f)
  | .pow x n=>(x.summary f).pow n

lemma LetterExpr.summary_rep {M : Type*} [Monoid M] (f : Letter→M) (e : LetterExpr) :
    (e.summary f).Rep f (e.eval FreeMonoid.of).toList := by
  induction e with
  | atom a=>exact PowerSummary.atom_rep f a
  | mul x y hx hy=>
    simpa only [summary,eval,FreeMonoid.toList_mul] using PowerSummary.mul_rep f _ _ _ _ hx hy
  | pow x n hx=>
    simpa only [summary,eval,freeMonoid_pow_word] using PowerSummary.pow_rep f _ _ hx n

def SourceProgram.summary {M : Type*} [Monoid M] (p : SourceProgram) (f : Letter→M) : PowerSummary M :=
  let table:=BitTable.ofFn (fun b=>(p.dictionary b).summary f)
  (table.lookup p.head).mul (p.continuation.summary table.lookup)

lemma SourceProgram.summary_rep {M : Type*} [Monoid M] (p : SourceProgram) (f : Letter→M) :
    (p.summary f).Rep f (p.eval FreeMonoid.of).toList := by
  have hc:=BitProgram.summary_rep f p.continuation
    (fun b=>(p.dictionary b).summary f) (fun b=>(p.dictionary b).eval FreeMonoid.of)
    (fun b=>LetterExpr.summary_rep f (p.dictionary b))
  have hh:=LetterExpr.summary_rep f (p.dictionary p.head)
  simpa only [summary,eval,BitTable.lookup_ofFn,cacheBits_eq,FreeMonoid.toList_mul] using
    PowerSummary.mul_rep f _ _ _ _ hh hc

/-- A reusable materialized summary of the exact full source word. Queries
use cached whole factors and div/mod inside powers, never a source list. -/
def sourceSummary {M : Type*} [Monoid M] (f : Letter→M) (L d q : ℕ) : PowerSummary M :=
  (sourceCompile L d q).summary f

theorem sourceSummary_rep {M : Type*} [Monoid M] (f : Letter→M) (L d q : ℕ)
    (hd : 0<d) (hdL : d<L) (hq : q≤L-d) :
    (sourceSummary f L d q).Rep f
      ((List.range L).map (fun k=>reducedLetter L d q ((d*k)%L))) := by
  have h:=(sourceCompile L d q).summary_rep f
  rw [sourceCompile_correct FreeMonoid.of L d q hd hdL hq,freeMonoid_word_product] at h
  exact h

#print axioms SourceProgram.summary_rep
#print axioms sourceSummary_rep
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord
