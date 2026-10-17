import Results.Genus.Injection.OriginalCapacity
import Results.Genus.Injection.WitnessedTargets

/-!
# A single original partial map at every genus

This is an endpoint packaging of the submitted partial-map proposition and
witnessed-unused lemma. The positive-genus source estimates are already
proved. The only additional boundary argument is that a binary word ending
in two cannot have weight one. No source-array or prefix acceptance is used.
-/

noncomputable section
namespace SubmittedGenus.OriginalMaps
open OriginalSources
attribute [local instance] Classical.propDecidable

/-- There is no binary end-two target at genus one. -/
theorem binaryEndTwo_zero_empty : IsEmpty (BinaryEndTwo 0) := by
  refine ⟨fun t => ?_⟩
  obtain ⟨w, hw⟩ := t.property.2
  have h := t.val.property
  rw [← KunzData.sum_toList, hw, List.sum_append] at h
  simp only [List.sum_cons, List.sum_nil, Nat.add_zero] at h
  omega

/-- The original Fibonacci supply formula, including its zero endpoint. -/
theorem binaryEndTwo_card_all (g : ℕ) :
    Fintype.card (BinaryEndTwo g) = Nat.fib g := by
  by_cases hg : g = 0
  · subst g
    letI := binaryEndTwo_zero_empty
    simp
  · exact binaryEndTwo_card (by omega)

/-- The actual source majorant gives a reservation-avoiding allocation for
all genera, including genus zero with empty demand and supply. -/
theorem original_allocation_all (g : ℕ) :
    ∃ fresh : DISources g ↪ BinaryEndTwo g,
      ∀ di b, fresh di ≠ BReserved g b := by
  apply Allocation.exists_embedding_avoiding_reserved (BReservedEmbedding g)
  rw [binaryEndTwo_card_all, Fintype.card_sum]
  have h := FiniteArithmetic.original_binary_source_capacity g
  omega

/-- Choose once, so all ensuing unused-target statements refer to the same
partial map rather than separate existential choices. -/
def originalFresh (g : ℕ) : DISources g ↪ BinaryEndTwo g :=
  Classical.choose (original_allocation_all g)

theorem originalFresh_reserved (g : ℕ) :
    ∀ di b, originalFresh g di ≠ BReserved g b :=
  Classical.choose_spec (original_allocation_all g)

/-- One original partial injection on genuine numerical semigroups. -/
def originalPhi (g : ℕ) :
    ActualNonexceptional g ↪ NumericalSemigroup.GenusFibre (g+1) :=
  (actualToWord g).trans (partialEmbedding g (originalFresh g) (originalFresh_reserved g))

/-- The genuine and Kunz nonexceptional domains have exactly the same image. -/
theorem actualToWord_surjective (g : ℕ) : Function.Surjective (actualToWord g) := by
  intro s
  refine ⟨⟨KunzData.equivGenusFibre g s.val, ?_⟩, ?_⟩
  · simpa only [Equiv.symm_apply_apply] using s.property
  · apply Subtype.ext
    exact (KunzData.equivGenusFibre g).symm_apply_apply s.val

theorem originalPhi_range (g : ℕ) :
    Set.range (originalPhi g) =
      Set.range (partialEmbedding g (originalFresh g) (originalFresh_reserved g)) := by
  ext t
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨actualToWord g s, rfl⟩
  · rintro ⟨s, hs⟩
    obtain ⟨S, hS⟩ := actualToWord_surjective g s
    exact ⟨S, by change partialEmbedding g (originalFresh g) (originalFresh_reserved g) (actualToWord g S) = t; rw [hS, hs]⟩

/-- The actual binary targets outside this one chosen genuine-semigroup map. -/
def OriginalUnusedBinary (g : ℕ) :=
  {t : BinaryEndTwo g // binaryToGenus g t ∉ Set.range (originalPhi g)}

instance (g : ℕ) : Fintype (OriginalUnusedBinary g) :=
  inferInstanceAs (Fintype {t : BinaryEndTwo g //
    binaryToGenus g t ∉ Set.range (originalPhi g)})

def originalUnusedBinaryEquiv (g : ℕ) :
    OriginalUnusedBinary g ≃ UnusedBinary g (originalFresh g) (originalFresh_reserved g) :=
  Equiv.subtypeEquivRight (fun t => by
    rw [originalPhi_range]
    rfl)

/-- Exact cardinality of the binary complement of the chosen actual map. -/
theorem originalUnusedBinary_card (g : ℕ) :
    Fintype.card (OriginalUnusedBinary g) = Nat.fib g -
      (Fintype.card (SourceClass g .B) + Fintype.card (SourceClass g .D) +
        Fintype.card (SourceClass g .I)) := by
  by_cases hg : g = 0
  · subst g
    letI := binaryEndTwo_zero_empty
    letI : IsEmpty (OriginalUnusedBinary 0) := ⟨fun t => isEmptyElim t.val⟩
    simp
  · rw [Fintype.card_congr (originalUnusedBinaryEquiv g)]
    exact unusedBinary_card g (by omega) (originalFresh g) (originalFresh_reserved g)

/-- The two lower bounds apply to this same unused set, hence their maximum. -/
theorem originalPhi_binary_capacity (g : ℕ) :
    max ((12*Nat.fib g+24)/25) (Nat.fib g-originalDemand g) ≤
      Fintype.card (OriginalUnusedBinary g) := by
  by_cases hg : g = 0
  · subst g
    simp
  · rw [Fintype.card_congr (originalUnusedBinaryEquiv g)]
    exact unusedBinary_capacity g (originalDemand g) (by omega)
      (originalFresh g) (originalFresh_reserved g)
      (originalDemand_majorant g) (originalDemand_weak g)

/-- The sharper supply estimate refers to the same selected partial map. -/
theorem originalPhi_sharp_binary_capacity (g : ℕ) (hg : 141 ≤ g) :
    987*Nat.fib g ≤ 1000*Fintype.card (OriginalUnusedBinary g) := by
  rw [Fintype.card_congr (originalUnusedBinaryEquiv g)]
  exact unusedBinary_sharp_capacity g (originalDemand g) (by omega)
    (originalFresh g) (originalFresh_reserved g)
    (originalDemand_majorant g) (originalDemand_sharp g hg)

/-- Every carried-witness base supplies a target outside this same map. -/
theorem originalPhi_witnessed_unused (g : ℕ) (d : WitnessedBase g) :
    witnessedTarget g d ∉ Set.range (originalPhi g) := by
  rintro ⟨s, hs⟩
  exact witnessedTarget_unused g (originalFresh g) (originalFresh_reserved g)
    d (actualToWord g s) hs

/-- The original proposition is uniform in every genus, with no capacity
or allocation premise, and its witness targets use the very same injection. -/
theorem original_partial_map_all (g : ℕ) :
    ∃ phi : ActualNonexceptional g ↪ NumericalSemigroup.GenusFibre (g+1),
      max ((12*Nat.fib g+24)/25) (Nat.fib g-originalDemand g) ≤
        Fintype.card {t : BinaryEndTwo g // binaryToGenus g t ∉ Set.range phi} ∧
      (∀ d : WitnessedBase g, witnessedTarget g d ∉ Set.range phi) ∧
      (141 ≤ g → 987*Nat.fib g ≤
        1000*Fintype.card {t : BinaryEndTwo g // binaryToGenus g t ∉ Set.range phi}) := by
  exact ⟨originalPhi g, originalPhi_binary_capacity g,
    originalPhi_witnessed_unused g, originalPhi_sharp_binary_capacity g⟩

end SubmittedGenus.OriginalMaps
