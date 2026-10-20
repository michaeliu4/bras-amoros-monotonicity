import Results.Genus.Injection.SourceClasses

namespace SubmittedGenus
namespace KunzWord

theorem one_lt_multiplicity_of_depth_pos {m : ℕ} (x : KunzWord m)
    (hdepth : 0 < depth x) : 1 < m := by
  by_contra h
  have hm : m - 1 = 0 := by omega
  have hempty : (Finset.univ : Finset (Fin (m - 1))) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i _
    have := i.isLt
    omega
  simp [depth, hempty] at hdepth

/-- A finite index for the canonical rightmost maximum. -/
theorem exists_rightmost_maximum {m : ℕ} (x : KunzWord m)
    (hdepth : 0 < depth x) :
    ∃ p : Fin (m - 1), x p = depth x ∧
      ∀ i : ℕ, p.val + 1 < i → i < m → coord x i < x p := by
  have hm := one_lt_multiplicity_of_depth_pos x hdepth
  have hs := rightmostMaximum_spec x hm
  let p : Fin (m - 1) := ⟨rightmostMaximum x - 1, by omega⟩
  have hp : p.val + 1 = rightmostMaximum x := by dsimp [p]; omega
  have hvalue : x p = depth x := by
    rw [← hp, coord_index] at hs
    exact hs.2.2
  refine ⟨p, hvalue, ?_⟩
  intro i hi him
  rw [hvalue]
  exact coord_lt_depth_after_rightmost x (by simpa only [hp] using hi) him

end KunzWord

namespace OriginalSources

attribute [local instance] Classical.propDecidable

def hasOne (d : KunzData) : Prop := ∃ i, d.2.val i = 1

def uniqueFour (d : KunzData) : Prop :=
  ∃ p, d.2.val p = 4 ∧ ∀ i, i ≠ p → d.2.val i ≤ 3

def isolatedAnyFive (d : KunzData) : Prop :=
  ∃ p, d.2.val p = 5 ∧ ∀ i, i ≠ p → d.2.val i ≤ 3

def hasFour (d : KunzData) : Prop := ∃ i, d.2.val i = 4

def uniqueFive (d : KunzData) : Prop :=
  ∃ p, d.2.val p = 5 ∧ ∀ i, d.2.val i = 5 → i = p

def twoLetters (d : KunzData) (a : ℕ) : Prop :=
  ∃ p q, p ≠ q ∧ d.2.val p = a ∧ d.2.val q = a

theorem lowParent_iff_at_rightmost (d : KunzData) (p : Fin (d.1.val - 1))
    (hp : 4 ≤ d.2.val p) (hmax : ∀ i, d.2.val i ≤ d.2.val p)
    (hright : ∀ i : ℕ, p.val + 1 < i → i < d.1.val →
      KunzWord.coord d.2.val i < d.2.val p) :
    lowParent d ↔ d.2.val p = 4 ∧ ∀ i, i ≠ p → d.2.val i ≤ 3 := by
  let P : KunzData := ⟨d.1,
    ⟨KunzWord.lowerAt d.2.val p, d.2.property.lowerMaximum (by omega) hmax⟩⟩
  have hparent : P.toSemigroup.IsOrdinaryChild d.toSemigroup :=
    KunzWord.lowerAt_isOrdinaryParent d.2.val d.1.property d.2.property p
      (by omega) hmax hright
  have hcriterion : P.depth ≤ 3 ↔ d.2.val p = 4 ∧ ∀ i, i ≠ p → d.2.val i ≤ 3 :=
    KunzWord.lowerAt_depth_le_three_iff d.2.val p hp
  constructor
  · rintro ⟨Q, hQparent, hQdepth⟩
    have heq : Q = P.toSemigroup := NumericalSemigroup.ordinaryParent_unique hQparent hparent
    apply hcriterion.mp
    simpa only [heq, NumericalSemigroup.kunzDepth_toSemigroup] using hQdepth
  · intro h
    exact ⟨P.toSemigroup, hparent,
      by simpa only [NumericalSemigroup.kunzDepth_toSemigroup] using hcriterion.mpr h⟩

/-- The manuscript's low-parent characterization is connected to actual
ordinary parents and the canonical depth, not assumed as a population fact. -/
theorem lowParent_iff_uniqueFour {d : KunzData} (hhigh : 4 ≤ d.depth) :
    lowParent d ↔ uniqueFour d := by
  obtain ⟨p, hpdepth, hright⟩ := KunzWord.exists_rightmost_maximum d.2.val
    (by change 0 < d.depth; omega)
  have hp : 4 ≤ d.2.val p := by change d.2.val p = d.depth at hpdepth; omega
  have hmax : ∀ i, d.2.val i ≤ d.2.val p := by
    intro i
    rw [hpdepth]
    exact KunzWord.le_depth d.2.val i
  rw [lowParent_iff_at_rightmost d p hp hmax hright]
  constructor
  · exact fun h => ⟨p, h⟩
  · rintro ⟨q, hq, hother⟩
    have hpq : p = q := by
      by_contra hne
      have := hother p hne
      omega
    subst q
    exact ⟨hq, hother⟩

theorem noOne_iff_not_hasOne (d : KunzData) : noOne d ↔ ¬ hasOne d := by
  simp only [noOne, hasOne, not_exists]

theorem uniqueFour_depth (d : KunzData) (h : uniqueFour d) : d.depth = 4 := by
  rcases h with ⟨p, hp, hother⟩
  have hle : d.depth ≤ 4 := by
    apply (KunzWord.depth_le_iff d.2.val).mpr
    intro i
    by_cases hi : i = p
    · simp only [hi, hp, le_refl]
    · have := hother i hi; omega
  have hge := KunzWord.le_depth d.2.val p
  change d.2.val p ≤ d.depth at hge
  omega

/-- The fourth and sixth raw tests together remove every isolated `5`,
with the split made exactly at physical position one versus at least two. -/
theorem isolatedAnyFive_iff (d : KunzData) :
    isolatedAnyFive d ↔ initialFive d ∨ isolatedFive d := by
  constructor
  · rintro ⟨p, hp, hother⟩
    by_cases hp0 : p.val = 0
    · left
      constructor
      · have := KunzWord.coord_index d.2.val p
        simpa only [hp0, Nat.zero_add] using this.trans hp
      · intro i hi
        apply hother i
        intro hip
        have := congrArg Fin.val hip
        omega
    · right
      exact ⟨p, by omega, hp, hother⟩
  · rintro (⟨hfirst, htail⟩ | ⟨p, hp0, hp, hother⟩)
    · have hm : 1 < d.1.val := by
        by_contra h
        have hzero := KunzWord.coord_of_ge d.2.val (by omega : d.1.val ≤ 1)
        omega
      let p : Fin (d.1.val - 1) := ⟨0, by omega⟩
      have hp : d.2.val p = 5 := by
        have := KunzWord.coord_index d.2.val p
        simpa [p] using this.symm.trans hfirst
      refine ⟨p, hp, ?_⟩
      intro i hi
      apply htail i
      by_contra hn
      have hi0 : i.val = 0 := by omega
      exact hi (Fin.ext (by simpa [p] using hi0))
    · exact ⟨p, hp, hother⟩

theorem isolatedAnyFive_depth (d : KunzData) (h : isolatedAnyFive d) : d.depth = 5 := by
  rcases h with ⟨p, hp, hother⟩
  have hle : d.depth ≤ 5 := by
    apply (KunzWord.depth_le_iff d.2.val).mpr
    intro i
    by_cases hi : i = p
    · simp only [hi, hp, le_refl]
    · have := hother i hi; omega
  have hge := KunzWord.le_depth d.2.val p
  change d.2.val p ≤ d.depth at hge
  omega

theorem twoLetters_not_uniqueFour {d : KunzData} (h : twoLetters d 4) :
    ¬ uniqueFour d := by
  rintro ⟨p, hp, hother⟩
  rcases h with ⟨q, r, hqr, hq, hr⟩
  by_cases hqp : q = p
  · have hrp : r ≠ p := by intro h; exact hqr (hqp.trans h.symm)
    have := hother r hrp
    omega
  · have := hother q hqp
    omega

theorem depth_four_not_unique_iff {d : KunzData} (hd : d.depth = 4) :
    ¬ uniqueFour d ↔ twoLetters d 4 := by
  constructor
  · intro hnot
    obtain ⟨p, hp, _⟩ := KunzWord.exists_rightmost_maximum d.2.val
      (by change 0 < d.depth; omega)
    change d.2.val p = d.depth at hp
    have hp4 : d.2.val p = 4 := by omega
    by_contra htwo
    apply hnot
    refine ⟨p, hp4, ?_⟩
    intro i hi
    have hle := KunzWord.le_depth d.2.val i
    change d.2.val i ≤ d.depth at hle
    by_contra hn
    have hi4 : d.2.val i = 4 := by omega
    exact htwo ⟨p, i, Ne.symm hi, hp4, hi4⟩
  · exact twoLetters_not_uniqueFour

theorem twoFives_not_isolated {d : KunzData} (h : twoLetters d 5) :
    ¬ isolatedAnyFive d := by
  rintro ⟨p, hp, hother⟩
  rcases h with ⟨q, r, hqr, hq, hr⟩
  by_cases hqp : q = p
  · have hrp : r ≠ p := by intro h; exact hqr (hqp.trans h.symm)
    have := hother r hrp
    omega
  · have := hother q hqp
    omega

theorem hasFour_not_isolated {d : KunzData} (h : hasFour d) : ¬ isolatedAnyFive d := by
  rintro ⟨p, hp, hother⟩
  rcases h with ⟨q, hq⟩
  have hqp : q ≠ p := by intro he; subst q; omega
  have := hother q hqp
  omega

theorem depth_five_not_isolated_iff {d : KunzData} (hd : d.depth = 5) :
    ¬ isolatedAnyFive d ↔ (uniqueFive d ∧ hasFour d) ∨ twoLetters d 5 := by
  constructor
  · intro hnot
    obtain ⟨p, hp, _⟩ := KunzWord.exists_rightmost_maximum d.2.val
      (by change 0 < d.depth; omega)
    change d.2.val p = d.depth at hp
    have hp5 : d.2.val p = 5 := by omega
    by_cases hone : ∀ i, d.2.val i = 5 → i = p
    · left
      refine ⟨⟨p, hp5, hone⟩, ?_⟩
      by_contra hfour
      apply hnot
      refine ⟨p, hp5, ?_⟩
      intro i hi
      have hle := KunzWord.le_depth d.2.val i
      change d.2.val i ≤ d.depth at hle
      have hne5 : d.2.val i ≠ 5 := fun h => hi (hone i h)
      have hne4 : d.2.val i ≠ 4 := fun h => hfour ⟨i, h⟩
      omega
    · right
      push_neg at hone
      obtain ⟨q, hq, hqp⟩ := hone
      exact ⟨p, q, Ne.symm hqp, hp5, hq⟩
  · rintro (⟨_, hfour⟩ | htwo)
    · exact hasFour_not_isolated hfour
    · exact twoFives_not_isolated htwo

/-- First reduce the literal seven-test complement without changing its
semantic source set. -/
theorem exceptional_iff_reduced (d : KunzData) :
    sector d = .E ↔ d.toSemigroup.IsLeaf ∧ hasOne d ∧
      (d.depth = 4 ∨ d.depth = 5) ∧ ¬ uniqueFour d ∧
      ¬ isolatedAnyFive d ∧ ¬ finalOneFour d := by
  constructor
  · intro h
    have hbasic := exceptional_leaf_depth_and_one h
    rcases (sector_E_iff d).mp h with ⟨hL, hP, hC, hT, hD, hI, hB⟩
    refine ⟨hbasic.1, hbasic.2.2, hbasic.2.1, ?_, ?_, hB⟩
    · intro hfour
      exact hC ((lowParent_iff_uniqueFour (by rcases hbasic.2.1 with h | h <;> omega)).mpr hfour)
    · intro hfive
      rcases (isolatedAnyFive_iff d).mp hfive with ht | hi
      · exact hT ht
      · exact hI hi
  · rintro ⟨hleaf, hone, hdepth, hfour, hfive, hfinal⟩
    apply (sector_E_iff d).mpr
    have hhigh : 4 ≤ d.depth := by rcases hdepth with h | h <;> omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hfinal⟩
    · unfold low
      omega
    · exact fun h => h hleaf
    · exact fun h => hfour ((lowParent_iff_uniqueFour hhigh).mp h)
    · exact fun h => hfive ((isolatedAnyFive_iff d).mpr (Or.inl h))
    · rintro (hdeep | ⟨_, hno⟩)
      · rcases hdepth with h | h <;> omega
      · exact (noOne_iff_not_hasOne d).mp hno hone
    · exact fun h => hfive ((isolatedAnyFive_iff d).mpr (Or.inr h))

/-- Lemma `cmb:residual`, with the manuscript's three sectors exactly. -/
theorem exceptional_iff_three_sectors (d : KunzData) :
    sector d = .E ↔ d.toSemigroup.IsLeaf ∧ hasOne d ∧
      ((d.depth = 4 ∧ twoLetters d 4 ∧ ¬ soleOneFinal d) ∨
       (d.depth = 5 ∧ uniqueFive d ∧ hasFour d) ∨
       (d.depth = 5 ∧ twoLetters d 5)) := by
  rw [exceptional_iff_reduced]
  constructor
  · rintro ⟨hleaf, hone, hdepth, hfour, hfive, hfinal⟩
    refine ⟨hleaf, hone, ?_⟩
    rcases hdepth with hd | hd
    · left
      exact ⟨hd, (depth_four_not_unique_iff hd).mp hfour, fun h => hfinal ⟨hd, h⟩⟩
    · right
      rcases (depth_five_not_isolated_iff hd).mp hfive with h | h
      · exact Or.inl ⟨hd, h⟩
      · exact Or.inr ⟨hd, h⟩
  · rintro ⟨hleaf, hone, hsector⟩
    refine ⟨hleaf, hone, ?_⟩
    rcases hsector with ⟨hd, htwo, hfinal⟩ | ⟨hd, huniq, hfour⟩ | ⟨hd, htwo⟩
    · refine ⟨Or.inl hd, twoLetters_not_uniqueFour htwo, ?_, ?_⟩
      · intro h
        have := isolatedAnyFive_depth d h
        omega
      · exact fun h => hfinal h.2
    · refine ⟨Or.inr hd, ?_, hasFour_not_isolated hfour, ?_⟩
      · intro h
        have := uniqueFour_depth d h
        omega
      · intro h
        have := h.1
        omega
    · refine ⟨Or.inr hd, ?_, twoFives_not_isolated htwo, ?_⟩
      · intro h
        have := uniqueFour_depth d h
        omega
      · intro h
        have := h.1
        omega

/-- The actual reserved-code source has at least two `4`s, by its earlier
exclusion from `C`, rather than by an extra source assumption. -/
theorem B_two_fours {d : KunzData} (h : sector d = .B) : twoLetters d 4 := by
  rcases (sector_B_iff d).mp h with ⟨hL, hP, hC, hT, hD, hI, hB⟩
  apply (depth_four_not_unique_iff hB.1).mp
  intro hfour
  exact hC ((lowParent_iff_uniqueFour (by have := hB.1; omega)).mpr hfour)

end OriginalSources
end SubmittedGenus
