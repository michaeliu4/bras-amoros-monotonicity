import Results.Genus.Injection.ElementaryInjection

namespace SubmittedGenus.OriginalMaps

open OriginalSources Function

attribute [local instance] Classical.propDecidable

/-- Forget the binary-sector property without changing the actual target. -/
def binaryToGenus (g : ℕ) (t : BinaryEndTwo g) : NumericalSemigroup.GenusFibre (g + 1) :=
  KunzData.toGenusFibre (g + 1) t.val

theorem binaryToGenus_injective (g : ℕ) : Function.Injective (binaryToGenus g) := by
  intro x y h
  exact Subtype.ext (KunzData.toGenusFibre_injective (g + 1) h)

def binaryToGenusEmbedding (g : ℕ) : BinaryEndTwo g ↪ NumericalSemigroup.GenusFibre (g + 1) :=
  ⟨binaryToGenus g, binaryToGenus_injective g⟩

@[simp] theorem binaryToGenus_BReserved (g : ℕ) (s : SourceClass g .B) :
    binaryToGenus g (BReserved g s) = BMap g s := rfl

theorem binaryEndTwo_depth (g : ℕ) (t : BinaryEndTwo g) :
    (binaryToGenus g t).val.kunzDepth ≤ 2 := by
  change t.val.val.toSemigroup.kunzDepth ≤ 2
  rw [NumericalSemigroup.kunzDepth_toSemigroup]
  apply (KunzWord.depth_le_iff _).mpr
  intro i
  have h := t.property.1 _ ((KunzData.mem_toList _ _).mpr ⟨i, rfl⟩)
  omega

theorem binaryEndTwo_lastLetter (g : ℕ) (t : BinaryEndTwo g) : t.val.val.lastLetter = 2 := by
  obtain ⟨pre, hpre⟩ := t.property.2
  have hb : ∀ a ∈ pre ++ [2], a = 1 ∨ a = 2 := by
    rw [← hpre]
    exact t.property.1
  let d := KunzWord.binaryData (pre ++ [2]) hb
  have heq : t.val.val = d := KunzData.toList_injective
    (hpre.trans (KunzWord.toList_binaryData _ hb).symm)
  rw [heq]
  simp [d, KunzData.lastLetter, KunzWord.binaryData, KunzWord.coord, KunzWord.ofList]

theorem binaryToGenus_ne_LMap (g : ℕ) (t : BinaryEndTwo g) (s : SourceClass g .L) :
    binaryToGenus g t ≠ LMap g s := by
  intro h
  have hdata := KunzData.toSemigroup_injective (congrArg Subtype.val h)
  have hlast := congrArg KunzData.lastLetter hdata
  change t.val.val.lastLetter = (lowAppend 1 (by omega) (by omega)
    ⟨s.val.val, (sector_L_iff s.val.val).mp s.property⟩).lastLetter at hlast
  rw [binaryEndTwo_lastLetter, lowAppend_lastLetter] at hlast
  omega

theorem binaryToGenus_ne_PMap (g : ℕ) (t : BinaryEndTwo g) (s : SourceClass g .P) :
    binaryToGenus g t ≠ PMap g s := by
  intro h
  have hb := binaryEndTwo_depth g t
  have hp := PMap_high g s
  rw [h] at hb
  omega

theorem binaryToGenus_ne_CMap (g : ℕ) (t : BinaryEndTwo g) (s : SourceClass g .C) :
    binaryToGenus g t ≠ CMap g s := by
  intro h
  have hb := binaryEndTwo_depth g t
  have hc := CMap_depth g s
  rw [h] at hb
  omega

theorem binaryToGenus_ne_TMap (g : ℕ) (t : BinaryEndTwo g) (s : SourceClass g .T) :
    binaryToGenus g t ≠ TMap g s := by
  intro h
  have hdata := KunzData.toSemigroup_injective (congrArg Subtype.val h)
  have hlast := congrArg KunzData.lastLetter hdata
  change t.val.val.lastLetter = (TTarget ⟨s.val.val, s.property⟩).lastLetter at hlast
  rw [binaryEndTwo_lastLetter, TTarget_lastLetter] at hlast
  omega

abbrev DISources (g : ℕ) := SourceClass g .D ⊕ SourceClass g .I

abbrev ElementarySources (g : ℕ) := SourceClass g .L ⊕
  (SourceClass g .P ⊕ (SourceClass g .C ⊕ (SourceClass g .T ⊕ SourceClass g .B)))

def BReservedEmbedding (g : ℕ) : SourceClass g .B ↪ BinaryEndTwo g :=
  ⟨BReserved g, BReserved_injective g⟩

/-- Semantic finite allocation for the actual ordered populations. This is
an interface lemma: the original majorant and numerical bound must supply
`hcapacity`; it is not asserted here without those producer proofs. -/
theorem exists_joint_DI_allocation (g : ℕ) (hg : 1 ≤ g)
    (hcapacity : Fintype.card (SourceClass g .D) + Fintype.card (SourceClass g .I) +
      Fintype.card (SourceClass g .B) ≤ Nat.fib g) :
    ∃ fresh : DISources g ↪ BinaryEndTwo g, ∀ di b, fresh di ≠ BReserved g b := by
  apply Allocation.exists_embedding_avoiding_reserved (BReservedEmbedding g)
  rw [binaryEndTwo_card hg, Fintype.card_sum]
  omega

/-- Join a supplied fresh allocation to the five genuine elementary maps.
Its disjointness proof excludes the actual reserved `B` image. -/
noncomputable def combinedEmbedding (g : ℕ) (fresh : DISources g ↪ BinaryEndTwo g)
    (hreserved : ∀ di b, fresh di ≠ BReserved g b) :
    ElementarySources g ⊕ DISources g ↪ NumericalSemigroup.GenusFibre (g + 1) :=
  Allocation.joinEmbeddings (elementaryEmbedding g)
    (fresh.trans (binaryToGenusEmbedding g)) (by
      rintro di (l | p | c | t | b) h
      · exact binaryToGenus_ne_LMap g (fresh di) l h
      · exact binaryToGenus_ne_PMap g (fresh di) p h
      · exact binaryToGenus_ne_CMap g (fresh di) c h
      · exact binaryToGenus_ne_TMap g (fresh di) t h
      · apply hreserved di b
        apply binaryToGenus_injective g
        exact h)

end SubmittedGenus.OriginalMaps
