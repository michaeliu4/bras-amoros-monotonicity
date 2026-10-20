import Results.Genus.Injection.Fundamental

noncomputable section
namespace SubmittedGenus.OriginalMaps
open OriginalSources
attribute [local instance] Classical.propDecidable

/-- All genuine low-depth targets at the indicated genus. -/
abbrev LowTargets (g : ℕ) :=
  {t : NumericalSemigroup.GenusFibre g // t.val.kunzDepth ≤ 3}

/-- The exact low-depth count denoted `t_g` in the submitted manuscript. -/
def lowCount (g : ℕ) : ℕ := Fintype.card (LowTargets g)

def lowSourceEquiv (g : ℕ) : SourceClass g .L ≃ LowTargets g where
  toFun s := ⟨KunzData.toGenusFibre g s.val, by
    change s.val.val.toSemigroup.kunzDepth ≤ 3
    rw [NumericalSemigroup.kunzDepth_toSemigroup]
    exact (sector_L_iff _).mp s.property⟩
  invFun t := ⟨(KunzData.equivGenusFibre g).symm t.val, by
    apply (sector_L_iff _).mpr
    change ((KunzData.equivGenusFibre g).symm t.val).val.depth ≤ 3
    have ht := t.property
    have he := (KunzData.equivGenusFibre g).apply_symm_apply t.val
    have hd := congrArg (fun x : NumericalSemigroup.GenusFibre g => x.val.kunzDepth) he
    rw [← hd] at ht
    change ((KunzData.equivGenusFibre g).symm t.val).val.toSemigroup.kunzDepth ≤ 3 at ht
    rw [NumericalSemigroup.kunzDepth_toSemigroup] at ht
    exact ht⟩
  left_inv s := by apply Subtype.ext; exact (KunzData.equivGenusFibre g).symm_apply_apply s.val
  right_inv t := by apply Subtype.ext; exact (KunzData.equivGenusFibre g).apply_symm_apply t.val

lemma card_low_source (g : ℕ) : Fintype.card (SourceClass g .L) = lowCount g :=
  Fintype.card_congr (lowSourceEquiv g)

/-- Precisely the six source sectors whose actual maps have low-depth images. -/
abbrev LowImageSources (g : ℕ) := SourceClass g .L ⊕
  (SourceClass g .C ⊕ (SourceClass g .T ⊕ (SourceClass g .B ⊕ DISources g)))

def lowSourcePartition (g : ℕ) : LowImageSources g → PartitionSum g
  | .inl l => .inl (.inl l)
  | .inr (.inl c) => .inl (.inr (.inr (.inl c)))
  | .inr (.inr (.inl t)) => .inl (.inr (.inr (.inr (.inl t))))
  | .inr (.inr (.inr (.inl b))) => .inl (.inr (.inr (.inr (.inr b))))
  | .inr (.inr (.inr (.inr di))) => .inr di

lemma lowSourcePartition_injective (g : ℕ) : Function.Injective (lowSourcePartition g) := by
  intro x y h
  rcases x with l | c | t | b | di <;>
    rcases y with l' | c' | t' | b' | di' <;>
    simp_all only [lowSourcePartition, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq]

lemma lowSourcePartition_low (g : ℕ) (fresh : DISources g ↪ BinaryEndTwo g)
    (hreserved : ∀ di b, fresh di ≠ BReserved g b) (s : LowImageSources g) :
    (combinedEmbedding g fresh hreserved (lowSourcePartition g s)).val.kunzDepth ≤ 3 := by
  rcases s with l | c | t | b | di
  · exact LMap_low g l
  · exact CMap_low g c
  · exact TMap_low g t
  · exact (BMap_depth g b).trans (by omega)
  · exact (binaryEndTwo_depth g (fresh di)).trans (by omega)

def lowCombinedEmbedding (g : ℕ) (fresh : DISources g ↪ BinaryEndTwo g)
    (hreserved : ∀ di b, fresh di ≠ BReserved g b) :
    LowImageSources g ↪ LowTargets (g+1) where
  toFun s := ⟨combinedEmbedding g fresh hreserved (lowSourcePartition g s),
    lowSourcePartition_low g fresh hreserved s⟩
  inj' a b h := lowSourcePartition_injective g
    ((combinedEmbedding g fresh hreserved).injective (congrArg Subtype.val h))

/-- A genuine low target is used exactly when it belongs to the six-sector
low-image embedding; the high ordinary-child image is excluded by depth. -/
lemma usedLow_iff (g : ℕ) (fresh : DISources g ↪ BinaryEndTwo g)
    (hreserved : ∀ di b, fresh di ≠ BReserved g b) (t : LowTargets (g+1)) :
    t.val ∈ Set.range (partialEmbedding g fresh hreserved) ↔
      t ∈ Set.range (lowCombinedEmbedding g fresh hreserved) := by
  constructor
  · rintro ⟨s,hs⟩
    have hs' : combinedEmbedding g fresh hreserved (splitSource g s) = t.val := hs
    rcases h : splitSource g s with (l | p | c | u | b) | di <;> rw [h] at hs'
    · exact ⟨.inl l, Subtype.ext (by exact hs')⟩
    · have hh : PMap g p = t.val := by exact hs'
      have hp := PMap_high g p
      rw [hh] at hp
      have := t.property
      omega
    · exact ⟨.inr (.inl c), Subtype.ext (by exact hs')⟩
    · exact ⟨.inr (.inr (.inl u)), Subtype.ext (by exact hs')⟩
    · exact ⟨.inr (.inr (.inr (.inl b))), Subtype.ext (by exact hs')⟩
    · exact ⟨.inr (.inr (.inr (.inr di))), Subtype.ext (by exact hs')⟩
  · rintro ⟨s,hs⟩
    refine ⟨joinSource g (lowSourcePartition g s), ?_⟩
    change combinedEmbedding g fresh hreserved
      (splitSource g (joinSource g (lowSourcePartition g s))) = _
    rw [splitSource_joinSource]
    exact congrArg Subtype.val hs

/-- The actual low-depth unused set, without replacing it by any bound. -/
abbrev UnusedLow (g : ℕ) (fresh : DISources g ↪ BinaryEndTwo g)
    (hreserved : ∀ di b, fresh di ≠ BReserved g b) :=
  {t : LowTargets (g+1) // t.val ∉ Set.range (partialEmbedding g fresh hreserved)}

/-- Exact integer accounting `cmb:exact-capacity`, before lower bounds. -/
lemma unusedLow_card (g : ℕ) (fresh : DISources g ↪ BinaryEndTwo g)
    (hreserved : ∀ di b, fresh di ≠ BReserved g b) :
    Fintype.card (UnusedLow g fresh hreserved) = lowCount (g+1) - lowCount g -
      Fintype.card (SourceClass g .C) - Fintype.card (SourceClass g .T) -
      Fintype.card (SourceClass g .D) - Fintype.card (SourceClass g .I) -
      Fintype.card (SourceClass g .B) := by
  have he := Fintype.card_congr (Equiv.subtypeEquivRight
    (fun t => not_congr (usedLow_iff g fresh hreserved t)))
  change Fintype.card (UnusedLow g fresh hreserved) = _ at he
  rw [he]
  simp only [Fintype.card_subtype_compl, Fintype.card_range]
  simp only [Fintype.card_sum, card_low_source]
  change lowCount (g+1) - _ = _
  omega

lemma unusedLow_balance (g : ℕ) (fresh : DISources g ↪ BinaryEndTwo g)
    (hreserved : ∀ di b, fresh di ≠ BReserved g b) :
    Fintype.card (UnusedLow g fresh hreserved) + lowCount g +
      Fintype.card (SourceClass g .C) + Fintype.card (SourceClass g .T) +
      Fintype.card (SourceClass g .D) + Fintype.card (SourceClass g .I) +
      Fintype.card (SourceClass g .B) = lowCount (g+1) := by
  have hfit := Fintype.card_le_of_embedding (lowCombinedEmbedding g fresh hreserved)
  simp only [Fintype.card_sum, card_low_source] at hfit
  rw [unusedLow_card]
  change _ ≤ lowCount (g+1) at hfit
  omega

def unusedLowIntoAll (g : ℕ) (fresh : DISources g ↪ BinaryEndTwo g)
    (hreserved : ∀ di b, fresh di ≠ BReserved g b) :
    UnusedLow g fresh hreserved ↪ AllUnused g fresh hreserved where
  toFun t := ⟨t.val.val,t.property⟩
  inj' a b h := by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : AllUnused g fresh hreserved => x.val) h

lemma fundamental_low_bound (g L : ℕ) (fresh : DISources g ↪ BinaryEndTwo g)
    (hreserved : ∀ di b, fresh di ≠ BReserved g b)
    (hL : L ≤ Fintype.card (UnusedLow g fresh hreserved)) :
    NumericalSemigroup.count g + L ≤ NumericalSemigroup.count (g+1) +
      Fintype.card (SourceClass g .E) := by
  have hu := Fintype.card_le_of_embedding (unusedLowIntoAll g fresh hreserved)
  have hb := fundamental_balance g fresh hreserved
  omega

#print axioms unusedLow_card
#print axioms unusedLow_balance
#print axioms fundamental_low_bound
end SubmittedGenus.OriginalMaps
