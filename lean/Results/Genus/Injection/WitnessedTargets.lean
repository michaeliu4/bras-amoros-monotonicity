import Results.Genus.Injection.UnusedBinary

namespace SubmittedGenus.OriginalMaps

open OriginalSources

/-- Every `3` has an actual carried `1+1` witness; self-pairs are allowed.
For the paper's prefix/tail notation this is exactly `j+k=ell+1-d`. -/
def CarryWitnessed (d : KunzData) : Prop :=
  ∀ i : ℕ, 0 < i → i < d.1.val → KunzWord.coord d.2.val i = 3 →
    ∃ j k : ℕ, 0 < j ∧ j < d.1.val ∧ 0 < k ∧ k < d.1.val ∧
      KunzWord.coord d.2.val j = 1 ∧ KunzWord.coord d.2.val k = 1 ∧
      j + k = d.1.val + i

/-- A fully witnessed low-depth parent has no high-depth ordinary child.
This is proved by the genuine restoration bridge and a violated carry
inequality, rather than by an abstract exclusion premise. -/
theorem no_high_child_of_carryWitnessed (d c : KunzData) (hd : low d)
    (hw : CarryWitnessed d) (hhigh : 4 ≤ c.depth)
    (hchild : d.toSemigroup.IsOrdinaryChild c.toSemigroup) : False := by
  obtain ⟨p, hpdepth, hright⟩ := KunzWord.exists_rightmost_maximum c.2.val
    (by change 0 < c.depth; omega)
  have hp : 4 ≤ c.2.val p := by change c.2.val p = c.depth at hpdepth; omega
  have hmax : ∀ i, c.2.val i ≤ c.2.val p := by
    intro i
    rw [hpdepth]
    exact KunzWord.le_depth c.2.val i
  let P : KunzData := ⟨c.1,
    ⟨KunzWord.lowerAt c.2.val p, c.2.property.lowerMaximum (by omega) hmax⟩⟩
  have hparent : P.toSemigroup.IsOrdinaryChild c.toSemigroup :=
    KunzWord.lowerAt_isOrdinaryParent c.2.val c.1.property c.2.property p
      (by omega) hmax hright
  have heq : P = d := KunzData.toSemigroup_injective
    (NumericalSemigroup.ordinaryParent_unique hparent hchild)
  have hPdepth : P.depth ≤ 3 := by rw [heq]; exact hd
  have hcrit := (KunzWord.lowerAt_depth_le_three_iff c.2.val p hp).mp hPdepth
  have hPcoord : KunzWord.coord P.2.val (p.val + 1) = 3 := by
    change KunzWord.coord (KunzWord.lowerAt c.2.val p) (p.val + 1) = 3
    rw [KunzWord.coord_index, KunzWord.lowerAt_self, hcrit.1]
  have hwP : CarryWitnessed P := by rw [heq]; exact hw
  obtain ⟨j, k, hj0, hjm, hk0, hkm, hj, hk, hjk⟩ :=
    hwP (p.val + 1) (by omega) (by change p.val + 1 < c.1.val; omega) hPcoord
  have hjne : j ≠ p.val + 1 := by
    intro h
    subst j
    rw [hPcoord] at hj
    omega
  have hkne : k ≠ p.val + 1 := by
    intro h
    subst k
    rw [hPcoord] at hk
    omega
  change KunzWord.coord (KunzWord.lowerAt c.2.val p) j = 1 at hj
  change KunzWord.coord (KunzWord.lowerAt c.2.val p) k = 1 at hk
  rw [KunzWord.coord_lowerAt, if_neg hjne] at hj
  rw [KunzWord.coord_lowerAt, if_neg hkne] at hk
  change j + k = c.1.val + (p.val + 1) at hjk
  have hcarry := c.2.property.carry j k hj0 hjm hk0 hkm (by omega)
  have hindex : j + k - c.1.val = p.val + 1 := by omega
  rw [hindex, KunzWord.coord_index, hcrit.1, hj, hk] at hcarry
  omega

theorem append_two_depth_three (d : LowSource) (hdepth : d.val.depth = 3) :
    (lowAppend 2 (by omega) (by omega) d).toSemigroup.kunzDepth = 3 := by
  rw [NumericalSemigroup.kunzDepth_toSemigroup]
  change KunzWord.depth (KunzWord.append d.val.2.val 2) = 3
  rw [KunzWord.depth_append _ d.val.1.property]
  change max d.val.depth 2 = 3
  rw [hdepth]
  decide

/-- The witnessed append-`2` target misses every elementary image and the
joint binary allocation, with each exclusion tied to its actual image. -/
theorem witnessed_append_two_not_in_combined (g : ℕ)
    (fresh : DISources g ↪ BinaryEndTwo g) (hreserved : ∀ di b, fresh di ≠ BReserved g b)
    (d : LowSource) (hdepth : d.val.depth = 3) (hw : CarryWitnessed d.val)
    (s : PartitionSum g) :
    (combinedEmbedding g fresh hreserved s).val ≠
      (lowAppend 2 (by omega) (by omega) d).toSemigroup := by
  intro h
  rcases s with (l | p | c | t | b) | di
  · have hlast := lowAppend_letter_eq_of_semigroup_eq
      ⟨l.val.val, (sector_L_iff l.val.val).mp l.property⟩ d h
    omega
  · have hP := PMap_high g p
    have hd := append_two_depth_three d hdepth
    change (PMap g p).val = (lowAppend 2 (by omega) (by omega) d).toSemigroup at h
    rw [h] at hP
    omega
  · have hparents := lowAppend_semigroup_injective 2 (by omega) (by omega) h
    have hparent := CParent_isOrdinaryParent ⟨c.val.val, c.property⟩
    rw [hparents] at hparent
    have hhigh : 4 ≤ c.val.val.depth := by
      have hlow := ((sector_C_iff _).mp c.property).1
      unfold low at hlow
      omega
    exact no_high_child_of_carryWitnessed d.val c.val.val d.property hw hhigh hparent
  · have hdata := KunzData.toSemigroup_injective h
    have hlast := congrArg KunzData.lastLetter hdata
    change (TTarget ⟨t.val.val, t.property⟩).lastLetter =
      (lowAppend 2 (by omega) (by omega) d).lastLetter at hlast
    rw [TTarget_lastLetter, lowAppend_lastLetter] at hlast
    omega
  · have hb := BMap_depth g b
    have hd := append_two_depth_three d hdepth
    change (BMap g b).val = (lowAppend 2 (by omega) (by omega) d).toSemigroup at h
    rw [h] at hb
    omega
  · have hb := binaryEndTwo_depth g (fresh di)
    have hd := append_two_depth_three d hdepth
    change (binaryToGenus g (fresh di)).val = (lowAppend 2 (by omega) (by omega) d).toSemigroup at h
    rw [h] at hb
    omega

/-- Genus-`g-1` witnessed bases, matching the index shift in the manuscript. -/
def WitnessedBase (g : ℕ) :=
  {d : KunzData // d.weight + 1 = g ∧ d.depth = 3 ∧ CarryWitnessed d}

def witnessedTarget (g : ℕ) (d : WitnessedBase g) :
    NumericalSemigroup.GenusFibre (g + 1) :=
  ⟨(lowAppend 2 (by omega) (by omega)
    ⟨d.val, by unfold low; have := d.property.2.1; omega⟩).toSemigroup, by
      rw [lowAppend_genus]
      change d.val.weight + 2 = g + 1
      have := d.property.1
      omega⟩

theorem witnessedTarget_injective (g : ℕ) : Function.Injective (witnessedTarget g) := by
  intro d e h
  have hlow := lowAppend_semigroup_injective 2 (by omega) (by omega) (congrArg Subtype.val h)
  exact Subtype.ext (congrArg (fun z : LowSource => z.val) hlow)

/-- Lemma `cmb:witness-unused`: distinct witnessed bases supply distinct
actual unused genus-`g+1` targets of the complete partial map. -/
theorem witnessedTarget_unused (g : ℕ)
    (fresh : DISources g ↪ BinaryEndTwo g) (hreserved : ∀ di b, fresh di ≠ BReserved g b)
    (d : WitnessedBase g) (s : Nonexceptional g) :
    partialEmbedding g fresh hreserved s ≠ witnessedTarget g d := by
  intro h
  exact witnessed_append_two_not_in_combined g fresh hreserved
    ⟨d.val, by unfold low; have := d.property.2.1; omega⟩
    d.property.2.1 d.property.2.2 (splitSource g s) (congrArg Subtype.val h)

end SubmittedGenus.OriginalMaps
