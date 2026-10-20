import Results.Genus.Injection.UnusedBinary

set_option maxHeartbeats 400000
noncomputable section
namespace SubmittedGenus.OriginalMaps
open OriginalSources
attribute [local instance] Classical.propDecidable

abbrev AllUnused (g : ℕ) (fresh : DISources g ↪ BinaryEndTwo g)
    (hreserved : ∀ di b, fresh di ≠ BReserved g b) :=
  {t : NumericalSemigroup.GenusFibre (g + 1) // t ∉ Set.range (partialEmbedding g fresh hreserved)}

def unusedBinaryIntoAll (g : ℕ) (fresh : DISources g ↪ BinaryEndTwo g)
    (hreserved : ∀ di b, fresh di ≠ BReserved g b) :
    UnusedBinary g fresh hreserved ↪ AllUnused g fresh hreserved where
  toFun t := ⟨binaryToGenus g t.val, t.property⟩
  inj' := by
    intro t u h
    exact Subtype.ext (binaryToGenus_injective g (congrArg Subtype.val h))

/-- Exact counting identity for the source-correct partial injection. -/
theorem fundamental_balance (g : ℕ) (fresh : DISources g ↪ BinaryEndTwo g)
    (hreserved : ∀ di b, fresh di ≠ BReserved g b) :
    NumericalSemigroup.count (g + 1) + Fintype.card (SourceClass g .E) =
      NumericalSemigroup.count g + Fintype.card (AllUnused g fresh hreserved) := by
  have h := Allocation.partial_injection_balance
    (fun d : KunzData.WeightFibre g => sector d.val = .E) (partialEmbedding g fresh hreserved)
  have he : Fintype.card {d : KunzData.WeightFibre g // sector d.val = .E} =
      Fintype.card (SourceClass g .E) := Fintype.card_congr (Equiv.refl _)
  rw [he] at h
  rw [KunzData.count_eq_card_weightFibre g]
  simp only [NumericalSemigroup.count, AllUnused, ← Nat.card_eq_fintype_card] at h ⊢
  refine h.trans (congrArg (fun n => Nat.card (KunzData.WeightFibre g) + n) ?_)
  apply Nat.card_congr
  refine Equiv.subtypeEquivRight (fun t => ?_)
  constructor
  · intro hn hmem
    apply hn
    obtain ⟨s, hs⟩ := hmem
    exact ⟨s, hs⟩
  · intro hn hmem
    apply hn
    obtain ⟨s, hs⟩ := hmem
    exact ⟨s, hs⟩

/-- Any proved lower bound on actual unused binary targets yields the
fundamental inequality for genuine numerical-semigroup counts. -/
theorem fundamental_binary_lower_bound (g L : ℕ) (fresh : DISources g ↪ BinaryEndTwo g)
    (hreserved : ∀ di b, fresh di ≠ BReserved g b)
    (hL : L ≤ Fintype.card (UnusedBinary g fresh hreserved)) :
    NumericalSemigroup.count g + L ≤ NumericalSemigroup.count (g + 1) +
      Fintype.card (SourceClass g .E) := by
  have hu := Fintype.card_le_of_embedding (unusedBinaryIntoAll g fresh hreserved)
  have hb := fundamental_balance g fresh hreserved
  omega

/-- Covering the exact exceptional population suffices for monotonicity. -/
theorem monotone_of_unused_binary_covers (g : ℕ) (fresh : DISources g ↪ BinaryEndTwo g)
    (hreserved : ∀ di b, fresh di ≠ BReserved g b)
    (hcover : Fintype.card (SourceClass g .E) ≤ Fintype.card (UnusedBinary g fresh hreserved)) :
    NumericalSemigroup.count g ≤ NumericalSemigroup.count (g + 1) := by
  have h := fundamental_binary_lower_bound g (Fintype.card (SourceClass g .E)) fresh hreserved hcover
  omega

/-- The original numerical binary lower bound, now attached to the actual
semigroup counts rather than an abstract cardinality schema. -/
theorem fundamental_original_binary_bound (g W : ℕ) (hg : 1 ≤ g)
    (fresh : DISources g ↪ BinaryEndTwo g) (hreserved : ∀ di b, fresh di ≠ BReserved g b)
    (hmajorant : Fintype.card (SourceClass g .D) + Fintype.card (SourceClass g .I) +
      Fintype.card (SourceClass g .B) ≤ W)
    (hproportion : 25 * W ≤ 13 * Nat.fib g) :
    NumericalSemigroup.count g + max ((12 * Nat.fib g + 24) / 25) (Nat.fib g - W) ≤
      NumericalSemigroup.count (g + 1) + Fintype.card (SourceClass g .E) :=
  fundamental_binary_lower_bound g _ fresh hreserved
    (unusedBinary_capacity g W hg fresh hreserved hmajorant hproportion)

end SubmittedGenus.OriginalMaps
