import Results.Genus.Kunz
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Nat.Choose.Basic

/-! Actual multiplicity-three counts in the original submitted introduction,
lines 119--124. The finite arithmetic is transported to genuine numerical
semigroups through the proved positive Kunz correspondence. -/
namespace SubmittedGenus.FiniteComparison.MultiplicityThree
open KunzWord

/-- The two literal inequalities, including the carry self-pair. -/
theorem valid_iff (x : KunzWord 3) :
    Valid x ↔ 0 < x 0 ∧ 0 < x 1 ∧ x 1 ≤ x 0 + x 0 ∧ x 0 ≤ x 1 + x 1 + 1 := by
  have h1 : coord x 1 = x 0 := coord_index x 0
  have h2 : coord x 2 = x 1 := coord_index x 1
  constructor
  · intro hx
    exact ⟨hx.positive 0, hx.positive 1,
      by simpa only [h1,h2] using hx.noncarry 1 1 (by decide) (by decide) (by decide) (by decide) (by decide),
      by simpa only [h1,h2] using hx.carry 2 2 (by decide) (by decide) (by decide) (by decide) (by decide)⟩
  · rintro ⟨ha,hb,hab,hba⟩
    constructor
    · intro i
      fin_cases i <;> assumption
    · intro i j hi hi' hj hj' hij
      have ei : i = 1 := by omega
      have ej : j = 1 := by omega
      subst i; subst j
      simpa only [h1,h2] using hab
    · intro i j hi hi' hj hj' hij
      have ei : i = 2 := by omega
      have ej : j = 2 := by omega
      subst i; subst j
      simpa only [h1,h2] using hba

lemma weight_eq (x : KunzWord 3) : weight x = x 0 + x 1 := by
  simp [weight, Fin.sum_univ_two]

/-- A genuinely finite enumeration of all positive admissible Kunz pairs. -/
def PairCondition (g : ℕ) (p : Fin (g+1) × Fin (g+1)) : Prop :=
  0 < p.1.val ∧ 0 < p.2.val ∧ p.1.val+p.2.val=g ∧
  p.2.val ≤ p.1.val+p.1.val ∧ p.1.val ≤ p.2.val+p.2.val+1

instance (g : ℕ) : DecidablePred (PairCondition g) := fun _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

abbrev Pairs (g : ℕ) := {p : Fin (g+1) × Fin (g+1) // PairCondition g p}

def word {g : ℕ} (p : Pairs g) : KunzWord 3 := ![p.val.1.val,p.val.2.val]

lemma word_valid {g : ℕ} (p : Pairs g) : Valid (word p) := by
  apply (valid_iff _).mpr
  exact ⟨p.property.1,p.property.2.1,p.property.2.2.2.1,p.property.2.2.2.2⟩

lemma word_weight {g : ℕ} (p : Pairs g) : weight (word p) = g := by
  rw [weight_eq]
  exact p.property.2.2.1

/-- Actual numerical semigroups of the indicated genus and multiplicity three. -/
abbrev Semigroups (g : ℕ) :=
  {S : NumericalSemigroup.GenusFibre g // S.val.IsMultiplicity 3}

noncomputable instance (g : ℕ) : Fintype (Semigroups g) := by
  classical
  exact inferInstanceAs (Fintype {_S : NumericalSemigroup.GenusFibre g // _})

def toSemigroups {g : ℕ} (p : Pairs g) : Semigroups g :=
  ⟨⟨toSemigroup (word p) (by decide) (word_valid p),
    (genus_toSemigroup (word p) (by decide) (word_valid p)).trans (word_weight p)⟩,
    isMultiplicity_toSemigroup (word p) (by decide) (word_valid p)⟩

lemma toSemigroups_injective (g : ℕ) : Function.Injective (@toSemigroups g) := by
  intro p q h
  have he := KunzWord.toSemigroup_injective (by decide) (word_valid p) (word_valid q)
    (congrArg (fun S : Semigroups g => S.val.val) h)
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext
  · exact congrFun he 0
  · exact congrFun he 1

lemma toSemigroups_surjective (g : ℕ) : Function.Surjective (@toSemigroups g) := by
  intro S
  let x := ofSemigroup S.val.val S.property
  have hx : Valid x := valid_ofSemigroup _ _
  have hw : weight x = g := by
    rw [←genus_toSemigroup x S.property.1 hx,toSemigroup_ofSemigroup]
    exact S.val.property
  have hw' : x 0 + x 1 = g := (weight_eq x).symm.trans hw
  have hp := (valid_iff x).mp hx
  let p : Pairs g := ⟨(⟨x 0,by omega⟩,⟨x 1,by omega⟩),hp.1,hp.2.1,hw',hp.2.2⟩
  have he : word p = x := by
    funext i
    fin_cases i <;> rfl
  refine ⟨p,Subtype.ext (Subtype.ext ?_)⟩
  change toSemigroup (word p) (by decide) (word_valid p) = S.val.val
  simpa only [he] using (toSemigroup_ofSemigroup S.val.val S.property)

noncomputable def pairEquivSemigroups (g : ℕ) : Pairs g ≃ Semigroups g :=
  Equiv.ofBijective toSemigroups ⟨toSemigroups_injective g,toSemigroups_surjective g⟩

noncomputable def count (g : ℕ) : ℕ := Fintype.card (Semigroups g)

lemma count_eq_pair_card (g : ℕ) : count g = Fintype.card (Pairs g) :=
  (Fintype.card_congr (pairEquivSemigroups g)).symm

lemma pair_card_nine : Fintype.card (Pairs 9) = 4 := by decide +kernel
lemma pair_card_ten : Fintype.card (Pairs 10) = 4 := by decide +kernel

/-- The actual count n(3,9), not a relaxed source count. -/
theorem count_nine : count 9 = 4 := (count_eq_pair_card 9).trans pair_card_nine

/-- The actual count n(3,10), not a relaxed source count. -/
theorem count_ten : count 10 = 4 := (count_eq_pair_card 10).trans pair_card_ten

lemma choose_four_two : Nat.choose 4 2 = 6 := by decide +kernel

/-- The counterexample concerns the cited counting inequality itself. -/
theorem cited_counting_inequality_false :
    count 9 ≥ 3 ∧ ¬ Nat.choose (count 9) (3-1) ≤ count 10 := by
  rw [count_nine,count_ten]
  decide +kernel

end SubmittedGenus.FiniteComparison.MultiplicityThree
