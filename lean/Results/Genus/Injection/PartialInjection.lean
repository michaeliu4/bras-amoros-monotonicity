import Results.Genus.Injection.JointAllocation

namespace SubmittedGenus.OriginalMaps

open OriginalSources Function

attribute [local instance] Classical.propDecidable

/-- Exactly the complement of the ordered exceptional class at weight `g`. -/
def Nonexceptional (g : ℕ) := {d : KunzData.WeightFibre g // sector d.val ≠ .E}

abbrev PartitionSum (g : ℕ) := ElementarySources g ⊕ DISources g

noncomputable def splitSource (g : ℕ) (s : Nonexceptional g) : PartitionSum g :=
  match hs : sector s.val.val with
  | .L => Sum.inl (Sum.inl ⟨s.val, hs⟩)
  | .P => Sum.inl (Sum.inr (Sum.inl ⟨s.val, hs⟩))
  | .C => Sum.inl (Sum.inr (Sum.inr (Sum.inl ⟨s.val, hs⟩)))
  | .T => Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨s.val, hs⟩))))
  | .D => Sum.inr (Sum.inl ⟨s.val, hs⟩)
  | .I => Sum.inr (Sum.inr ⟨s.val, hs⟩)
  | .B => Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inr ⟨s.val, hs⟩))))
  | .E => (s.property hs).elim

def forgetClass {g : ℕ} {c : Sector} (hc : c ≠ .E) (s : SourceClass g c) : Nonexceptional g :=
  ⟨s.val, fun h => hc (s.property.symm.trans h)⟩

def joinSource (g : ℕ) : PartitionSum g → Nonexceptional g :=
  Sum.elim
    (Sum.elim (forgetClass (by decide))
      (Sum.elim (forgetClass (by decide))
        (Sum.elim (forgetClass (by decide))
          (Sum.elim (forgetClass (by decide)) (forgetClass (by decide))))))
    (Sum.elim (forgetClass (by decide)) (forgetClass (by decide)))

theorem joinSource_splitSource (g : ℕ) (s : Nonexceptional g) :
    joinSource g (splitSource g s) = s := by
  unfold splitSource
  split <;> first | rfl | exact (s.property (by assumption)).elim

theorem splitSource_joinSource (g : ℕ) (s : PartitionSum g) :
    splitSource g (joinSource g s) = s := by
  rcases s with (l | p | c | t | b) | (d | i)
  · have hs := l.property
    simp only [joinSource, Sum.elim_inl, Sum.elim_inr, forgetClass]
    unfold splitSource
    split <;> simp_all
  · have hs := p.property
    simp only [joinSource, Sum.elim_inl, Sum.elim_inr, forgetClass]
    unfold splitSource
    split <;> simp_all
  · have hs := c.property
    simp only [joinSource, Sum.elim_inl, Sum.elim_inr, forgetClass]
    unfold splitSource
    split <;> simp_all
  · have hs := t.property
    simp only [joinSource, Sum.elim_inl, Sum.elim_inr, forgetClass]
    unfold splitSource
    split <;> simp_all
  · have hs := b.property
    simp only [joinSource, Sum.elim_inl, Sum.elim_inr, forgetClass]
    unfold splitSource
    split <;> simp_all
  · have hs := d.property
    simp only [joinSource, Sum.elim_inl, Sum.elim_inr, forgetClass]
    unfold splitSource
    split <;> simp_all
  · have hs := i.property
    simp only [joinSource, Sum.elim_inl, Sum.elim_inr, forgetClass]
    unfold splitSource
    split <;> simp_all

noncomputable def sourcePartitionEquiv (g : ℕ) : Nonexceptional g ≃ PartitionSum g where
  toFun := splitSource g
  invFun := joinSource g
  left_inv := joinSource_splitSource g
  right_inv := splitSource_joinSource g

/-- The actual original partial map after a jointly allocated `D/I`
matching is supplied. Every image-disjointness premise is proved above. -/
noncomputable def partialEmbedding (g : ℕ) (fresh : DISources g ↪ BinaryEndTwo g)
    (hreserved : ∀ di b, fresh di ≠ BReserved g b) :
    Nonexceptional g ↪ NumericalSemigroup.GenusFibre (g + 1) :=
  (sourcePartitionEquiv g).toEmbedding.trans (combinedEmbedding g fresh hreserved)

/-- Conditional only on the stated actual binary capacity inequality. No
source inclusion or analytic bound is silently accepted by this interface. -/
theorem exists_partialEmbedding_of_capacity (g : ℕ) (hg : 1 ≤ g)
    (hcapacity : Fintype.card (SourceClass g .D) + Fintype.card (SourceClass g .I) +
      Fintype.card (SourceClass g .B) ≤ Nat.fib g) :
    Nonempty (Nonexceptional g ↪ NumericalSemigroup.GenusFibre (g + 1)) := by
  obtain ⟨fresh, hreserved⟩ := exists_joint_DI_allocation g hg hcapacity
  exact ⟨partialEmbedding g fresh hreserved⟩

/-- The same source condition on actual numerical semigroups, through the
proved genus-preserving Kunz equivalence. -/
def ActualNonexceptional (g : ℕ) :=
  {S : NumericalSemigroup.GenusFibre g //
    sector ((KunzData.equivGenusFibre g).symm S).val ≠ .E}

noncomputable def actualToWord (g : ℕ) : ActualNonexceptional g ↪ Nonexceptional g where
  toFun S := ⟨(KunzData.equivGenusFibre g).symm S.val, S.property⟩
  inj' := by
    intro S T h
    exact Subtype.ext ((KunzData.equivGenusFibre g).symm.injective (congrArg Subtype.val h))

/-- A genuine-semigroup partial injection with the exact ordered
exceptional set, once the manuscript's capacity producers are discharged. -/
theorem exists_actual_partialEmbedding_of_capacity (g : ℕ) (hg : 1 ≤ g)
    (hcapacity : Fintype.card (SourceClass g .D) + Fintype.card (SourceClass g .I) +
      Fintype.card (SourceClass g .B) ≤ Nat.fib g) :
    Nonempty (ActualNonexceptional g ↪ NumericalSemigroup.GenusFibre (g + 1)) := by
  obtain ⟨e⟩ := exists_partialEmbedding_of_capacity g hg hcapacity
  exact ⟨(actualToWord g).trans e⟩

end SubmittedGenus.OriginalMaps
