import Results.Genus.Injection.ReservoirSources.Candidates
import Results.Genus.Injection.ReservoirSources.LowDepthAccounting

noncomputable section
namespace SubmittedGenus.OriginalReservoir
open OriginalMaps OriginalSources
attribute [local instance] Classical.propDecidable

lemma witnessedTarget_depth (g : ℕ) (s : WitnessedBase g) :
    (witnessedTarget g s).val.kunzDepth = 3 :=
  append_two_depth_three _ s.property.2.1

/-- Every witnessed physical base supplies its actual unused low target. -/
def witnessedIntoUnusedLow (g : ℕ) (fresh : DISources g ↪ BinaryEndTwo g)
    (hreserved : ∀ di b, fresh di ≠ BReserved g b) :
    WitnessedBase g ↪ UnusedLow g fresh hreserved where
  toFun s := ⟨⟨witnessedTarget g s, by rw [witnessedTarget_depth]⟩, by
    rintro ⟨t,ht⟩
    exact witnessedTarget_unused g fresh hreserved s t ht⟩
  inj' a b h := witnessedTarget_injective g
    (congrArg (fun t : UnusedLow g fresh hreserved => t.val.val) h)

def goodIntoUnusedLow (g : ℕ) (fresh : DISources g ↪ BinaryEndTwo g)
    (hreserved : ∀ di b, fresh di ≠ BReserved g b) :
    GoodCandidate safeFamily g ⊕ GoodCandidate earlyFamily g ↪ UnusedLow g fresh hreserved :=
  (goodJointEmbedding g).trans (witnessedIntoUnusedLow g fresh hreserved)

/-- The separately clipped two-family lower bound counts genuine unused
nonbinary targets of the actual original partial injection. -/
lemma nonbinaryLowerBound_le_unusedLow (g : ℕ) (fresh : DISources g ↪ BinaryEndTwo g)
    (hreserved : ∀ di b, fresh di ≠ BReserved g b) :
    nonbinaryLowerBound g ≤ Fintype.card (UnusedLow g fresh hreserved) :=
  (nonbinaryLowerBound_le_good_sum g).trans
    (Fintype.card_le_of_embedding (goodIntoUnusedLow g fresh hreserved))

def binaryIntoUnusedLow (g : ℕ) (fresh : DISources g ↪ BinaryEndTwo g)
    (hreserved : ∀ di b, fresh di ≠ BReserved g b) :
    UnusedBinary g fresh hreserved ↪ UnusedLow g fresh hreserved where
  toFun t := ⟨⟨binaryToGenus g t.val, (binaryEndTwo_depth g t.val).trans (by omega)⟩,t.property⟩
  inj' a b h := by
    apply Subtype.ext
    exact binaryToGenus_injective g
      (congrArg (fun t : UnusedLow g fresh hreserved => t.val.val) h)

lemma binary_good_disjoint (g : ℕ) (fresh : DISources g ↪ BinaryEndTwo g)
    (hreserved : ∀ di b, fresh di ≠ BReserved g b)
    (b : UnusedBinary g fresh hreserved)
    (s : GoodCandidate safeFamily g ⊕ GoodCandidate earlyFamily g) :
    binaryIntoUnusedLow g fresh hreserved b ≠ goodIntoUnusedLow g fresh hreserved s := by
  intro h
  have he := congrArg (fun t : UnusedLow g fresh hreserved => t.val.val.val.kunzDepth) h
  change (binaryToGenus g b.val).val.kunzDepth =
    (witnessedTarget g (goodJointEmbedding g s)).val.kunzDepth at he
  have hb := binaryEndTwo_depth g b.val
  rw [witnessedTarget_depth] at he
  omega

/-- Binary and witnessed nonbinary reservoirs add only after the two
actual image populations have been proved disjoint by depth. -/
def jointUnusedLowEmbedding (g : ℕ) (fresh : DISources g ↪ BinaryEndTwo g)
    (hreserved : ∀ di b, fresh di ≠ BReserved g b) :
    UnusedBinary g fresh hreserved ⊕
      (GoodCandidate safeFamily g ⊕ GoodCandidate earlyFamily g) ↪
        UnusedLow g fresh hreserved :=
  Allocation.joinEmbeddings (binaryIntoUnusedLow g fresh hreserved)
    (goodIntoUnusedLow g fresh hreserved) (fun s b h => binary_good_disjoint g fresh hreserved b s h.symm)

lemma binary_add_nonbinary_le_unusedLow (g : ℕ) (fresh : DISources g ↪ BinaryEndTwo g)
    (hreserved : ∀ di b, fresh di ≠ BReserved g b) :
    Fintype.card (UnusedBinary g fresh hreserved) + nonbinaryLowerBound g ≤
      Fintype.card (UnusedLow g fresh hreserved) := by
  have hc := Fintype.card_le_of_embedding (jointUnusedLowEmbedding g fresh hreserved)
  rw [Fintype.card_sum] at hc
  exact (Nat.add_le_add_left (nonbinaryLowerBound_le_good_sum g) _).trans hc

/-- The source-correct original capacity inequality, with the numerical W
producer explicitly isolated and physical reservoir counts already proved. -/
lemma original_capacity_bound (g W : ℕ) (hg : 1 ≤ g)
    (fresh : DISources g ↪ BinaryEndTwo g) (hreserved : ∀ di b, fresh di ≠ BReserved g b)
    (hmajorant : Fintype.card (SourceClass g .D) + Fintype.card (SourceClass g .I) +
      Fintype.card (SourceClass g .B) ≤ W)
    (hproportion : 25 * W ≤ 13 * Nat.fib g) :
    max ((12 * Nat.fib g + 24) / 25) (Nat.fib g - W) + nonbinaryLowerBound g ≤
      Fintype.card (UnusedLow g fresh hreserved) :=
  (Nat.add_le_add_right
    (unusedBinary_capacity g W hg fresh hreserved hmajorant hproportion) _).trans
      (binary_add_nonbinary_le_unusedLow g fresh hreserved)

lemma original_fundamental_bound (g W : ℕ) (hg : 1 ≤ g)
    (fresh : DISources g ↪ BinaryEndTwo g) (hreserved : ∀ di b, fresh di ≠ BReserved g b)
    (hmajorant : Fintype.card (SourceClass g .D) + Fintype.card (SourceClass g .I) +
      Fintype.card (SourceClass g .B) ≤ W)
    (hproportion : 25 * W ≤ 13 * Nat.fib g) :
    NumericalSemigroup.count g +
      (max ((12 * Nat.fib g + 24) / 25) (Nat.fib g - W) + nonbinaryLowerBound g) ≤
      NumericalSemigroup.count (g+1) + Fintype.card (SourceClass g .E) :=
  fundamental_low_bound g _ fresh hreserved
    (original_capacity_bound g W hg fresh hreserved hmajorant hproportion)

#print axioms witnessedIntoUnusedLow
#print axioms binary_good_disjoint
#print axioms original_capacity_bound
#print axioms original_fundamental_bound
end SubmittedGenus.OriginalReservoir
