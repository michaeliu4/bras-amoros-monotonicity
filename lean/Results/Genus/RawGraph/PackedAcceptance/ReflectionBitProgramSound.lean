import Results.Genus.RawGraph.PackedAcceptance.ReflectionBitProgram

namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord

lemma wordMode_substitution {M : Type*} [Monoid M] (f : BitLetter→M)
    (tail rev : Bool) (p w : List BitLetter) (g : BitLetter→List BitLetter) (hp : p≠[]) :
    wordValue f (wordMode tail rev (p++w.reverse.flatMap g))=
      if rev then
        wordValue (fun b=>wordValue f (g b).reverse) w * wordValue f (wordMode tail rev p)
      else wordValue f (wordMode tail rev p)*wordValue (fun b=>wordValue f (g b)) w.reverse := by
  cases tail <;> cases rev <;>
    simp [wordMode,List.tail_append_of_ne_nil hp,List.reverse_append,List.reverse_flatMap,
      wordValue_append,wordValue_flatMap,Function.comp_def]

lemma bit_word_recursive_value {M : Type*} [Monoid M] (f : BitLetter→M)
    (L d q : ℕ) (hd : 0<d) (hdL : d<L) (hq : q≤L) (tail rev : Bool) :
    wordValue f (wordMode tail rev (bitOrbitWord L d q))=
      if rev then
        wordValue (bitMacroValue L d q f false rev)
          (wordMode true (!rev) (bitOrbitWord d (L%d) (q%d))) *
            bitMacroValue L d q f tail rev (bitLetter (q%d) (L%d) 0)
      else bitMacroValue L d q f tail rev (bitLetter (q%d) (L%d) 0) *
        wordValue (bitMacroValue L d q f false rev)
          (wordMode true (!rev) (bitOrbitWord d (L%d) (q%d))) := by
  rw [bit_word_positive_remainder L d q hd hdL hq]
  rw [wordMode_substitution f tail rev _ _ _ (bitMacro_ne_nil _ _ _ _)]
  have hm : bitMacroValue L d q f false rev =
      (fun b=>wordValue f (wordMode false rev (bitMacro L d q b))) := by
    funext b
    exact bitMacroValue_correct _ _ _ _ _ _ _
  rw [hm]
  simp only [bitMacroValue_correct]
  cases rev <;> simp [wordMode]

/-- Exact source-order evaluator for every closed two-cut bit word. Its
single recursive child always has the positive Euclidean remainder step. -/
theorem bitCompile_correct {M : Type*} [Monoid M] (f : BitLetter→M)
    (L d q : ℕ) (hdL : d<L) (hq : q≤L) (tail rev : Bool) :
    (bitCompile L d q tail rev).eval f = wordValue f (wordMode tail rev (bitOrbitWord L d q)) := by
  by_cases hd : 0<d
  · rw [bitCompile,dif_pos ⟨hd,hdL⟩]
    simp only [BitProgram.eval,cacheBits_eq,macroExpr_eval]
    rw [bitCompile_correct (bitMacroValue L d q f false rev) d (L%d) (q%d)
      (Nat.mod_lt L hd) (Nat.le_of_lt (Nat.mod_lt q hd)) true (!rev)]
    exact (bit_word_recursive_value f L d q hd hdL hq tail rev).symm
  · have hz : d=0 := by omega
    subst d
    rw [bitCompile,dif_neg (by omega)]
    cases tail <;> cases rev <;>
      simp [BitProgram.eval,wordValue,wordMode,bitOrbitWord]
termination_by L

#print axioms bit_word_recursive_value
#print axioms bitCompile_correct
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord
