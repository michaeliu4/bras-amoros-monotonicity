import Results.Genus.Injection.PartialInjection

namespace SubmittedGenus.OriginalMaps

open OriginalSources Function

attribute [local instance] Classical.propDecidable

noncomputable def binaryJointEmbedding (g : ℕ) (fresh : DISources g ↪ BinaryEndTwo g)
    (hreserved : ∀ di b, fresh di ≠ BReserved g b) :
    SourceClass g .B ⊕ DISources g ↪ BinaryEndTwo g :=
  Allocation.joinEmbeddings (BReservedEmbedding g) fresh hreserved

/-- Among the full seven-class injection, precisely `B/D/I` use binary
end-`2` targets. This equality tracks the actual image, not an upper estimate. -/
theorem usedBinary_sum_iff (g : ℕ) (fresh : DISources g ↪ BinaryEndTwo g)
    (hreserved : ∀ di b, fresh di ≠ BReserved g b) (t : BinaryEndTwo g) :
    (∃ s : PartitionSum g, combinedEmbedding g fresh hreserved s = binaryToGenus g t) ↔
      t ∈ Set.range (binaryJointEmbedding g fresh hreserved) := by
  constructor
  · rintro ⟨s, hs⟩
    rcases s with (l | p | c | u | b) | di
    · exact (binaryToGenus_ne_LMap g t l hs.symm).elim
    · exact (binaryToGenus_ne_PMap g t p hs.symm).elim
    · exact (binaryToGenus_ne_CMap g t c hs.symm).elim
    · exact (binaryToGenus_ne_TMap g t u hs.symm).elim
    · refine ⟨Sum.inl b, ?_⟩
      exact binaryToGenus_injective g hs
    · refine ⟨Sum.inr di, ?_⟩
      exact binaryToGenus_injective g hs
  · rintro ⟨s, hs⟩
    rcases s with b | di
    · refine ⟨Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inr b)))), ?_⟩
      exact congrArg (binaryToGenus g) hs
    · refine ⟨Sum.inr di, ?_⟩
      exact congrArg (binaryToGenus g) hs

theorem usedBinary_iff (g : ℕ) (fresh : DISources g ↪ BinaryEndTwo g)
    (hreserved : ∀ di b, fresh di ≠ BReserved g b) (t : BinaryEndTwo g) :
    (∃ s : Nonexceptional g, partialEmbedding g fresh hreserved s = binaryToGenus g t) ↔
      t ∈ Set.range (binaryJointEmbedding g fresh hreserved) := by
  rw [← usedBinary_sum_iff g fresh hreserved t]
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨splitSource g s, hs⟩
  · rintro ⟨s, hs⟩
    refine ⟨joinSource g s, ?_⟩
    change combinedEmbedding g fresh hreserved (splitSource g (joinSource g s)) = _
    rw [splitSource_joinSource]
    exact hs

/-- The single unused binary set appearing in `cmb:binary-capacity`. -/
def UnusedBinary (g : ℕ) (fresh : DISources g ↪ BinaryEndTwo g)
    (hreserved : ∀ di b, fresh di ≠ BReserved g b) :=
  {t : BinaryEndTwo g //
    ¬ ∃ s : Nonexceptional g, partialEmbedding g fresh hreserved s = binaryToGenus g t}

noncomputable instance (g : ℕ) (fresh : DISources g ↪ BinaryEndTwo g)
    (hreserved : ∀ di b, fresh di ≠ BReserved g b) : Fintype (UnusedBinary g fresh hreserved) :=
  inferInstanceAs (Fintype {t : BinaryEndTwo g //
    ¬ ∃ s : Nonexceptional g, partialEmbedding g fresh hreserved s = binaryToGenus g t})

theorem unusedBinary_card (g : ℕ) (hg : 1 ≤ g) (fresh : DISources g ↪ BinaryEndTwo g)
    (hreserved : ∀ di b, fresh di ≠ BReserved g b) :
    Fintype.card (UnusedBinary g fresh hreserved) = Nat.fib g -
      (Fintype.card (SourceClass g .B) + Fintype.card (SourceClass g .D) +
        Fintype.card (SourceClass g .I)) := by
  have hcard := Fintype.card_congr (Equiv.subtypeEquivRight
    (fun t => not_congr (usedBinary_iff g fresh hreserved t)))
  change Fintype.card (UnusedBinary g fresh hreserved) = _ at hcard
  rw [hcard, Allocation.card_unused, binaryEndTwo_card hg]
  simp only [Fintype.card_sum]
  omega

theorem unusedBinary_balance (g : ℕ) (hg : 1 ≤ g) (fresh : DISources g ↪ BinaryEndTwo g)
    (hreserved : ∀ di b, fresh di ≠ BReserved g b) :
    Fintype.card (UnusedBinary g fresh hreserved) +
      (Fintype.card (SourceClass g .B) + Fintype.card (SourceClass g .D) +
        Fintype.card (SourceClass g .I)) = Nat.fib g := by
  have hfit := Fintype.card_le_of_embedding (binaryJointEmbedding g fresh hreserved)
  rw [binaryEndTwo_card hg] at hfit
  simp only [Fintype.card_sum] at hfit
  rw [unusedBinary_card g hg fresh hreserved]
  omega

/-- The exact original maximum lower bound on the same actual unused set.
Only the separately named majorant and numerical producer premises remain. -/
theorem unusedBinary_capacity (g W : ℕ) (hg : 1 ≤ g) (fresh : DISources g ↪ BinaryEndTwo g)
    (hreserved : ∀ di b, fresh di ≠ BReserved g b)
    (hmajorant : Fintype.card (SourceClass g .D) + Fintype.card (SourceClass g .I) +
      Fintype.card (SourceClass g .B) ≤ W)
    (hproportion : 25 * W ≤ 13 * Nat.fib g) :
    max ((12 * Nat.fib g + 24) / 25) (Nat.fib g - W) ≤
      Fintype.card (UnusedBinary g fresh hreserved) := by
  have hsum : Fintype.card (SourceClass g .B) + Fintype.card (SourceClass g .D) +
      Fintype.card (SourceClass g .I) ≤ W := by omega
  exact Allocation.binary_unused_lower_bound _ _ _ _
    (unusedBinary_balance g hg fresh hreserved) hsum
    ((Nat.mul_le_mul_left 25 hsum).trans hproportion)

theorem unusedBinary_sharp_capacity (g W : ℕ) (hg : 1 ≤ g)
    (fresh : DISources g ↪ BinaryEndTwo g)
    (hreserved : ∀ di b, fresh di ≠ BReserved g b)
    (hmajorant : Fintype.card (SourceClass g .D) + Fintype.card (SourceClass g .I) +
      Fintype.card (SourceClass g .B) ≤ W)
    (hproportion : 1000 * W ≤ 13 * Nat.fib g) :
    987 * Nat.fib g ≤ 1000 * Fintype.card (UnusedBinary g fresh hreserved) := by
  have hsum : Fintype.card (SourceClass g .B) + Fintype.card (SourceClass g .D) +
      Fintype.card (SourceClass g .I) ≤ W := by omega
  exact Allocation.binary_unused_sharp_bound _ _ _
    (unusedBinary_balance g hg fresh hreserved)
    ((Nat.mul_le_mul_left 1000 hsum).trans hproportion)

end SubmittedGenus.OriginalMaps
