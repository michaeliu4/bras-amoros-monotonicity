import Results.Genus.Injection.Residual
import Results.Genus.CapFiveMass.Source

/-! Genuine populations and the original unique-five parent reduction.
The shifted parent image has a `1`, but no final-one exclusion is imposed. -/

noncomputable section
namespace SubmittedGenus.OriginalPopulations
open OriginalSources

/-- The manuscript's unrestricted genuine population A. -/
def HasMultipleFour (d : KunzData) : Prop :=
  (∀ i, d.2.val i ≤ 4) ∧ twoLetters d 4
abbrev GenuineFour := {d : KunzData // HasMultipleFour d}
abbrev GenuineFourAt (g : ℕ) := {d : KunzData.WeightFibre g // HasMultipleFour d.val}
instance (g : ℕ) : Fintype (GenuineFourAt g) := by
  classical
  exact inferInstanceAs (Fintype {d : KunzData.WeightFibre g // HasMultipleFour d.val})
def countFour (g : ℕ) : ℕ := Fintype.card (GenuineFourAt g)
def massFour (z : ℝ) : ℝ := ∑' g, (countFour g : ℝ) * z ^ g

lemma genuineFour_depth (d : GenuineFour) : d.val.depth = 4 := by
  apply le_antisymm
  · exact (KunzWord.depth_le_iff _).mpr d.property.1
  · obtain ⟨p, q, hpq, hp, hq⟩ := d.property.2
    exact hp ▸ KunzWord.le_depth d.val.2.val p

/-- Exactly the first residual sector, with all its source restrictions. -/
def IsFirstResidual (d : KunzData) : Prop :=
  d.toSemigroup.IsLeaf ∧ hasOne d ∧ d.depth = 4 ∧
    twoLetters d 4 ∧ ¬ soleOneFinal d
/-- Exactly the unique-five residual sector. -/
def IsUniqueFiveResidual (d : KunzData) : Prop :=
  d.toSemigroup.IsLeaf ∧ hasOne d ∧ d.depth = 5 ∧ uniqueFive d ∧ hasFour d
abbrev FirstResidual := {d : KunzData // IsFirstResidual d}
abbrev UniqueFiveResidual := {d : KunzData // IsUniqueFiveResidual d}

lemma firstResidual_exceptional (d : FirstResidual) : sector d.val = .E :=
  (exceptional_iff_three_sectors _).mpr
    ⟨d.property.1, d.property.2.1, Or.inl d.property.2.2⟩
lemma uniqueFiveResidual_exceptional (d : UniqueFiveResidual) : sector d.val = .E :=
  (exceptional_iff_three_sectors _).mpr
    ⟨d.property.1, d.property.2.1, Or.inr (Or.inl d.property.2.2)⟩

def firstIntoFour (d : FirstResidual) : GenuineFour :=
  ⟨d.val, (KunzWord.depth_le_iff _).mp (le_of_eq d.property.2.2.1), d.property.2.2.2.1⟩
lemma firstIntoFour_injective : Function.Injective firstIntoFour :=
  fun _ _ h => Subtype.ext (congrArg (fun z : GenuineFour => z.val) h)

def uniquePivot (d : UniqueFiveResidual) : Fin (d.val.1.val - 1) :=
  d.property.2.2.2.1.choose
lemma uniquePivot_value (d : UniqueFiveResidual) : d.val.2.val (uniquePivot d) = 5 :=
  d.property.2.2.2.1.choose_spec.1
lemma uniquePivot_unique (d : UniqueFiveResidual) (i) (hi : d.val.2.val i = 5) :
    i = uniquePivot d := d.property.2.2.2.1.choose_spec.2 i hi
lemma uniquePivot_max (d : UniqueFiveResidual) (i) :
    d.val.2.val i ≤ d.val.2.val (uniquePivot d) := by
  rw [uniquePivot_value]
  exact (KunzWord.depth_le_iff _).mp (le_of_eq d.property.2.2.1) i
lemma uniquePivot_other_le (d : UniqueFiveResidual) (i) (hi : i ≠ uniquePivot d) :
    d.val.2.val i ≤ 4 := by
  have hb := uniquePivot_max d i
  rw [uniquePivot_value] at hb
  have hn : d.val.2.val i ≠ 5 := fun he => hi (uniquePivot_unique d i he)
  omega
lemma uniquePivot_right (d : UniqueFiveResidual) (i : ℕ)
    (hi : (uniquePivot d).val + 1 < i) (him : i < d.val.1.val) :
    KunzWord.coord d.val.2.val i < d.val.2.val (uniquePivot d) := by
  let j : Fin (d.val.1.val - 1) := ⟨i - 1, by omega⟩
  have hj : j.val + 1 = i := by dsimp [j]; omega
  have hne : j ≠ uniquePivot d := by intro h; have := congrArg Fin.val h; dsimp [j] at this; omega
  rw [← hj, KunzWord.coord_index, uniquePivot_value]
  have := uniquePivot_other_le d j hne
  omega

/-- Restore the unique maximal gap, literally lowering its coordinate. -/
def uniqueFiveParent (d : UniqueFiveResidual) : KunzData :=
  ⟨d.val.1, ⟨KunzWord.lowerAt d.val.2.val (uniquePivot d),
    d.val.2.property.lowerMaximum (by rw [uniquePivot_value]; omega) (uniquePivot_max d)⟩⟩

lemma uniqueFiveParent_isOrdinaryParent (d : UniqueFiveResidual) :
    (uniqueFiveParent d).toSemigroup.IsOrdinaryChild d.val.toSemigroup :=
  KunzWord.lowerAt_isOrdinaryParent d.val.2.val d.val.1.property d.val.2.property
    (uniquePivot d) (by rw [uniquePivot_value]; omega) (uniquePivot_max d) (uniquePivot_right d)

lemma uniqueFiveParent_weight (d : UniqueFiveResidual) :
    (uniqueFiveParent d).weight + 1 = d.val.weight := by
  have h := NumericalSemigroup.genus_of_ordinaryChild (uniqueFiveParent_isOrdinaryParent d)
  simpa only [KunzData.genus_toSemigroup] using h.symm

lemma uniqueFiveParent_nonleaf (d : UniqueFiveResidual) :
    ¬ (uniqueFiveParent d).toSemigroup.IsLeaf := by
  obtain ⟨a, ha, _⟩ := uniqueFiveParent_isOrdinaryParent d
  exact fun h => h a ha

lemma uniqueFiveParent_hasOne (d : UniqueFiveResidual) : hasOne (uniqueFiveParent d) := by
  obtain ⟨i, hi⟩ := d.property.2.1
  have hne : i ≠ uniquePivot d := by intro h; rw [h, uniquePivot_value] at hi; omega
  refine ⟨i, ?_⟩
  change KunzWord.lowerAt d.val.2.val (uniquePivot d) i = 1
  rw [KunzWord.lowerAt_other _ _ _ hne, hi]

lemma uniqueFiveParent_multipleFour (d : UniqueFiveResidual) :
    HasMultipleFour (uniqueFiveParent d) := by
  constructor
  · intro i
    change Fin (d.val.1.val - 1) at i
    change KunzWord.lowerAt d.val.2.val (uniquePivot d) i ≤ 4
    by_cases hi : i = uniquePivot d
    · rw [hi, KunzWord.lowerAt_self, uniquePivot_value]
    · rw [KunzWord.lowerAt_other _ _ _ hi]
      exact uniquePivot_other_le d i hi
  · obtain ⟨q, hq⟩ := d.property.2.2.2.2
    have hne : q ≠ uniquePivot d := by intro h; rw [h, uniquePivot_value] at hq; omega
    refine ⟨uniquePivot d, q, Ne.symm hne, ?_, ?_⟩
    · change KunzWord.lowerAt d.val.2.val (uniquePivot d) (uniquePivot d) = 4
      rw [KunzWord.lowerAt_self, uniquePivot_value]
    · change KunzWord.lowerAt d.val.2.val (uniquePivot d) q = 4
      rw [KunzWord.lowerAt_other _ _ _ hne, hq]

lemma uniqueFiveParent_injective : Function.Injective uniqueFiveParent := by
  intro d e he
  have hd := uniqueFiveParent_isOrdinaryParent d
  rw [he] at hd
  exact Subtype.ext (KunzData.toSemigroup_injective
    (NumericalSemigroup.leafChild_unique hd (uniqueFiveParent_isOrdinaryParent e)
      d.property.1 e.property.1))

def uniqueIntoFour (d : UniqueFiveResidual) : GenuineFour :=
  ⟨uniqueFiveParent d, uniqueFiveParent_multipleFour d⟩
lemma uniqueIntoFour_injective : Function.Injective uniqueIntoFour :=
  fun _ _ h => uniqueFiveParent_injective (congrArg Subtype.val h)

lemma firstIntoFour_ne_uniqueIntoFour (d : FirstResidual) (e : UniqueFiveResidual) :
    firstIntoFour d ≠ uniqueIntoFour e := by
  intro h
  have he := congrArg Subtype.val h
  change d.val = uniqueFiveParent e at he
  exact uniqueFiveParent_nonleaf e (he ▸ d.property.1)

/-- The actual global injection in Lemma `cmb:compensation`. -/
def compensationEmbedding : FirstResidual ⊕ UniqueFiveResidual ↪ GenuineFour where
  toFun := Sum.elim firstIntoFour uniqueIntoFour
  inj' := by
    intro a b h
    rcases a with a | a <;> rcases b with b | b
    · exact congrArg Sum.inl (firstIntoFour_injective h)
    · exact (firstIntoFour_ne_uniqueIntoFour a b h).elim
    · exact (firstIntoFour_ne_uniqueIntoFour b a h.symm).elim
    · exact congrArg Sum.inr (uniqueIntoFour_injective h)

def residualWeight : FirstResidual ⊕ UniqueFiveResidual → ℕ :=
  Sum.elim (fun d => d.val.weight) (fun d => d.val.weight)

lemma compensationEmbedding_weight (d : FirstResidual ⊕ UniqueFiveResidual) :
    (compensationEmbedding d).val.weight ≤ residualWeight d := by
  rcases d with d | d
  · exact le_refl _
  · exact Nat.le_of_lt (by have := uniqueFiveParent_weight d; change (uniqueFiveParent d).weight < d.val.weight; omega)

end SubmittedGenus.OriginalPopulations
