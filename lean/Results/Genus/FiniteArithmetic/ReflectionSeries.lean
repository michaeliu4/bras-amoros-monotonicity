import Results.Genus.FiniteArithmetic.ReflectionLanguage
import Results.Genus.FiniteArithmetic.GradedSources

namespace SubmittedGenus.FiniteArithmetic.Reflection

open scoped BigOperators
open PowerSeries

/-- An exact reflection language. Pair alphabets can be genuinely infinite;
positive total pair weight makes every weight fiber finite. -/
structure System where
  pairAllowed : ℕ → ℕ → Prop
  centerAllowed : ℕ → Prop
  pairPositive : ∀ a b, pairAllowed a b → 0 < a + b

abbrev System.pairAlphabet (S : System) : LocallyFinite.Alphabet where
  Letter := Pair S.pairAllowed
  weight := pairWeight
  positive p := S.pairPositive _ _ p.property
  finiteBelow n := by
    apply Finite.of_injective
      (fun p : {p : Pair S.pairAllowed // pairWeight p ≤ n} =>
        (⟨p.val.val.1, by have := p.property; dsimp [pairWeight] at this; omega⟩,
         ⟨p.val.val.2, by have := p.property; dsimp [pairWeight] at this; omega⟩) :
          {p : Pair S.pairAllowed // pairWeight p ≤ n} → Fin (n + 1) × Fin (n + 1))
    intro p q h
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun z : Fin (n + 1) × Fin (n + 1) => z.1.val) h
    · exact congrArg (fun z : Fin (n + 1) × Fin (n + 1) => z.2.val) h

abbrev PairWords (S : System) (n : ℕ) := LocallyFinite.Words S.pairAlphabet n

noncomputable instance pairWordsFintype (S : System) (n : ℕ) : Fintype (PairWords S n) :=
  LocallyFinite.wordsFintype S.pairAlphabet n

abbrev Centers (S : System) (n : ℕ) :=
  {c : Option (Center S.centerAllowed) // centerWeight c = n}

noncomputable instance centersFintype (S : System) (n : ℕ) : Fintype (Centers S n) := by
  apply Fintype.ofInjective (fun c : Centers S n => c.val.isSome)
  rintro ⟨c, hc⟩ ⟨d, hd⟩ h
  apply Subtype.ext
  cases c with
  | none => cases d <;> simp_all
  | some c =>
    cases d with
    | none => simp at h
    | some d =>
      exact congrArg Option.some (Subtype.ext (hc.trans hd.symm))

abbrev Blocks (S : System) (n : ℕ) :=
  {w : List ℕ // Language S.pairAllowed S.centerAllowed w ∧ w.sum = n}

abbrev Source (S : System) (n : ℕ) := Graded.Product (PairWords S) (Centers S) n

def sourceToBlock (S : System) (n : ℕ) (s : Source S n) : Blocks S n :=
  ⟨decode (s.2.1.val, s.2.2.val), decode_mem_language _, by
    change (decodePairs s.2.1.val s.2.2.val).sum = n
    rw [decode_weight, s.2.1.property, s.2.2.property]
    have := s.1.isLt
    omega⟩

theorem sourceToBlock_injective (S : System) (n : ℕ) :
    Function.Injective (sourceToBlock S n) := by
  rintro ⟨⟨i, hi⟩, ⟨ps, hps⟩, ⟨c, hc⟩⟩ ⟨⟨j, hj⟩, ⟨qs, hqs⟩, ⟨d, hd⟩⟩ h
  have he := decode_injective (congrArg Subtype.val h)
  change (ps, c) = (qs, d) at he
  have hp := congrArg Prod.fst he
  have hc' := congrArg Prod.snd he
  dsimp at hp hc'
  subst qs
  subst d
  have hij : i = j := hps.symm.trans hqs
  subst j
  rfl

theorem sourceToBlock_surjective (S : System) (n : ℕ) :
    Function.Surjective (sourceToBlock S n) := by
  rintro ⟨w, hw, hn⟩
  obtain ⟨⟨ps, c⟩, he⟩ := language_has_code hw
  have hs : (ps.map pairWeight).sum + centerWeight c = n := by
    rw [← decode_weight]
    change (decode (ps, c)).sum = n
    rw [he, hn]
  refine ⟨⟨⟨(ps.map pairWeight).sum, by omega⟩, ⟨ps, rfl⟩, ⟨c, ?_⟩⟩, ?_⟩
  · change centerWeight c = n - (ps.map pairWeight).sum
    omega
  · exact Subtype.ext he

noncomputable def sourceEquivBlock (S : System) (n : ℕ) : Source S n ≃ Blocks S n :=
  Equiv.ofBijective (sourceToBlock S n)
    ⟨sourceToBlock_injective S n, sourceToBlock_surjective S n⟩

noncomputable instance blocksFintype (S : System) (n : ℕ) : Fintype (Blocks S n) :=
  Fintype.ofEquiv (Source S n) (sourceEquivBlock S n)

noncomputable def blockSeries (S : System) : PowerSeries ℤ := Graded.series (Blocks S)
noncomputable def centerSeries (S : System) : PowerSeries ℤ := Graded.series (Centers S)

@[simp] theorem coeff_blockSeries (S : System) (n : ℕ) :
    coeff n (blockSeries S) = (Fintype.card (Blocks S n) : ℤ) := by simp [blockSeries]

/-- The product interpretation follows from the actual weight-preserving source
bijection. Each physical letter is represented exactly once. -/
theorem blockSeries_factorization (S : System) :
    blockSeries S = LocallyFinite.wordSeries S.pairAlphabet * centerSeries S := by
  unfold blockSeries centerSeries
  rw [Graded.series_congr (Blocks S) (Source S) (fun n => (sourceEquivBlock S n).symm)]
  rw [Graded.product_series]
  rfl

/-- The exact reflection-block generating identity, valid for bounded and
unbounded pair alphabets alike. -/
theorem blockSeries_identity (S : System) :
    (1 - LocallyFinite.letterSeries S.pairAlphabet) * blockSeries S = centerSeries S := by
  rw [blockSeries_factorization, ← mul_assoc, LocallyFinite.wordSeries_identity, one_mul]

#print axioms sourceEquivBlock
#print axioms blockSeries_identity

end SubmittedGenus.FiniteArithmetic.Reflection
