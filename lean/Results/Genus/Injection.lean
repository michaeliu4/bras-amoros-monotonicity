import Results.Genus.Semigroup
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# The submitted paper's ordinary-parent and allocation lemmas

This file follows `cmb:parent` in the immutable submitted manuscript
`e04fb276e8ceed829059cf724ead1e18e8bc9e9f`, lines 197–220.
The objects below are genuine additive submonoids of `ℕ` with finite
complement. The natural-valued `IsFrobenius` is only used for nonempty
complements; the genus-zero convention remains the foundation's integer −1.
No assertion about the later geometric or Fibonacci routes occurs here.
-/

namespace SubmittedGenus
namespace NumericalSemigroup

/-- A positive indecomposable element of a numerical semigroup. -/
def IsMinimalGenerator (S : NumericalSemigroup) (a : ℕ) : Prop :=
  a ∈ S ∧ a ≠ 0 ∧
    ∀ b c : ℕ, b ∈ S → c ∈ S → b + c = a → b = 0 ∨ c = 0

/-- A minimal generator larger than every gap. This definition also handles
`ℕ` directly, without an artificial natural-valued Frobenius of zero. -/
def IsEffectiveGenerator (S : NumericalSemigroup) (a : ℕ) : Prop :=
  S.IsMinimalGenerator a ∧ ∀ n : ℕ, n ∉ S → n < a

/-- A semigroup without effective generators. -/
def IsLeaf (S : NumericalSemigroup) : Prop :=
  ∀ a : ℕ, ¬ S.IsEffectiveGenerator a

/-- The largest gap of a positive-genus semigroup. -/
def IsFrobenius (S : NumericalSemigroup) (f : ℕ) : Prop :=
  f ∉ S ∧ ∀ n : ℕ, n ∉ S → n ≤ f

/-- An ordinary child is obtained by deleting one effective generator.
The membership formulation avoids choosing a particular representation. -/
def IsOrdinaryChild (S T : NumericalSemigroup) : Prop :=
  ∃ a : ℕ, S.IsEffectiveGenerator a ∧
    ∀ n : ℕ, n ∈ T ↔ n ∈ S ∧ n ≠ a

theorem IsFrobenius.unique {S : NumericalSemigroup} {f g : ℕ}
    (hf : S.IsFrobenius f) (hg : S.IsFrobenius g) : f = g :=
  Nat.le_antisymm (hg.2 f hf.1) (hf.2 g hg.1)

theorem IsFrobenius.pos {S : NumericalSemigroup} {f : ℕ}
    (hf : S.IsFrobenius f) : 0 < f := by
  have hz : (0 : ℕ) ∈ S := S.toAddSubmonoid.zero_mem
  have : f ≠ 0 := fun h => hf.1 (h ▸ hz)
  omega

/-- Deleting a minimal generator preserves addition and cofiniteness. -/
def removeGenerator (S : NumericalSemigroup) (a : ℕ)
    (ha : S.IsMinimalGenerator a) : NumericalSemigroup where
  toAddSubmonoid :=
    { carrier := {n : ℕ | n ∈ S ∧ n ≠ a}
      zero_mem' := ⟨S.toAddSubmonoid.zero_mem, Ne.symm ha.2.1⟩
      add_mem' := by
        intro b c hb hc
        refine ⟨S.toAddSubmonoid.add_mem hb.1 hc.1, ?_⟩
        intro h
        rcases ha.2.2 b c hb.1 hc.1 h with hb0 | hc0
        · exact hc.2 (by simpa [hb0] using h)
        · exact hb.2 (by simpa [hc0] using h) }
  finite_compl := by
    apply (S.finite_compl.insert a).subset
    intro n hn
    by_cases hna : n = a
    · exact Or.inl hna
    · exact Or.inr (fun hnS => hn ⟨hnS, hna⟩)

@[simp] theorem mem_removeGenerator {S : NumericalSemigroup} {a n : ℕ}
    {ha : S.IsMinimalGenerator a} :
    n ∈ S.removeGenerator a ha ↔ n ∈ S ∧ n ≠ a := Iff.rfl

/-- Restoring the largest gap preserves addition and cofiniteness. -/
def restoreFrobenius (S : NumericalSemigroup) (f : ℕ)
    (hf : S.IsFrobenius f) : NumericalSemigroup where
  toAddSubmonoid :=
    { carrier := {n : ℕ | n ∈ S ∨ n = f}
      zero_mem' := Or.inl S.toAddSubmonoid.zero_mem
      add_mem' := by
        intro b c hb hc
        rcases hb with hb | rfl <;> rcases hc with hc | rfl
        · exact Or.inl (S.toAddSubmonoid.add_mem hb hc)
        · by_cases hb0 : b = 0
          · exact Or.inr (by omega)
          · apply Or.inl
            by_contra h
            have := hf.2 _ h
            omega
        · by_cases hc0 : c = 0
          · exact Or.inr (by omega)
          · apply Or.inl
            by_contra h
            have := hf.2 _ h
            omega
        · apply Or.inl
          by_contra h
          have := hf.2 _ h
          have := hf.pos
          omega }
  finite_compl := by
    apply S.finite_compl.subset
    intro n hn hnS
    exact hn (Or.inl hnS)

@[simp] theorem mem_restoreFrobenius {S : NumericalSemigroup} {f n : ℕ}
    {hf : S.IsFrobenius f} :
    n ∈ S.restoreFrobenius f hf ↔ n ∈ S ∨ n = f := Iff.rfl

/-- The restored element is effective in the enlarged semigroup. -/
theorem effectiveGenerator_restoreFrobenius {S : NumericalSemigroup} {f : ℕ}
    (hf : S.IsFrobenius f) :
    (S.restoreFrobenius f hf).IsEffectiveGenerator f := by
  refine ⟨⟨Or.inr rfl, by have := hf.pos; omega, ?_⟩, ?_⟩
  · intro b c hb hc hsum
    rcases hb with hb | rfl <;> rcases hc with hc | rfl
    · exact (hf.1 (hsum ▸ S.toAddSubmonoid.add_mem hb hc)).elim
    · left; omega
    · right; omega
    · have := hf.pos; omega
  · intro n hn
    have hnS : n ∉ S := fun h => hn (Or.inl h)
    have hne : n ≠ f := fun h => hn (Or.inr h)
    have := hf.2 n hnS
    omega

/-- A positive-genus semigroup is a child of the semigroup obtained by
restoring its largest gap. -/
theorem isOrdinaryChild_restoreFrobenius {S : NumericalSemigroup} {f : ℕ}
    (hf : S.IsFrobenius f) :
    (S.restoreFrobenius f hf).IsOrdinaryChild S := by
  refine ⟨f, effectiveGenerator_restoreFrobenius hf, ?_⟩
  intro n
  constructor
  · intro hn
    exact ⟨Or.inl hn, fun h => hf.1 (h ▸ hn)⟩
  · rintro ⟨hn | hnf, hne⟩
    · exact hn
    · exact (hne hnf).elim

/-- An effective-generator deletion has exactly that generator as its
Frobenius number. -/
theorem frobenius_of_deletion {S T : NumericalSemigroup} {a : ℕ}
    (ha : S.IsEffectiveGenerator a)
    (hT : ∀ n : ℕ, n ∈ T ↔ n ∈ S ∧ n ≠ a) : T.IsFrobenius a := by
  constructor
  · intro haT
    exact ((hT a).mp haT).2 rfl
  · intro n hn
    by_cases hnS : n ∈ S
    · have hna : n = a := by
        by_contra hne
        exact hn ((hT n).mpr ⟨hnS, hne⟩)
      omega
    · exact Nat.le_of_lt (ha.2 n hnS)

/-- Restoring the deleted effective generator recovers the parent. -/
theorem parent_membership_of_deletion {S T : NumericalSemigroup} {a : ℕ}
    (ha : S.IsEffectiveGenerator a)
    (hT : ∀ n : ℕ, n ∈ T ↔ n ∈ S ∧ n ≠ a) (n : ℕ) :
    n ∈ S ↔ n ∈ T ∨ n = a := by
  constructor
  · intro hn
    by_cases hna : n = a
    · exact Or.inr hna
    · exact Or.inl ((hT n).mpr ⟨hn, hna⟩)
  · intro hn
    rcases hn with hn | rfl
    · exact ((hT n).mp hn).1
    · exact ha.1.1

/-- The ordinary parent is unique, by the child's intrinsic largest gap. -/
theorem ordinaryParent_unique {S U T : NumericalSemigroup}
    (hST : S.IsOrdinaryChild T) (hUT : U.IsOrdinaryChild T) : S = U := by
  rcases hST with ⟨a, ha, hTa⟩
  rcases hUT with ⟨b, hb, hTb⟩
  have hab : a = b :=
    (frobenius_of_deletion ha hTa).unique (frobenius_of_deletion hb hTb)
  subst b
  ext n
  exact (parent_membership_of_deletion ha hTa n).trans
    (parent_membership_of_deletion hb hTb n).symm

/-- A larger effective generator survives deletion of a smaller one. -/
theorem effectiveGenerator_survives_deletion {S T : NumericalSemigroup} {a b : ℕ}
    (ha : S.IsEffectiveGenerator a) (hb : S.IsEffectiveGenerator b)
    (hab : a < b) (hT : ∀ n : ℕ, n ∈ T ↔ n ∈ S ∧ n ≠ a) :
    T.IsEffectiveGenerator b := by
  refine ⟨⟨(hT b).mpr ⟨hb.1.1, by omega⟩, hb.1.2.1, ?_⟩, ?_⟩
  · intro c d hc hd hsum
    exact hb.1.2.2 c d ((hT c).mp hc).1 ((hT d).mp hd).1 hsum
  · intro n hn
    have := (frobenius_of_deletion ha hT).2 n hn
    omega

/-- A leaf child can only delete a largest effective generator. -/
theorem leaf_deletes_largest {S T : NumericalSemigroup} {a : ℕ}
    (ha : S.IsEffectiveGenerator a)
    (hT : ∀ n : ℕ, n ∈ T ↔ n ∈ S ∧ n ≠ a) (hLeaf : T.IsLeaf)
    {b : ℕ} (hb : S.IsEffectiveGenerator b) : b ≤ a := by
  by_contra h
  exact hLeaf b (effectiveGenerator_survives_deletion ha hb (by omega) hT)

/-- Every genuine numerical semigroup has at most one ordinary leaf child. -/
theorem leafChild_unique {S T U : NumericalSemigroup}
    (hST : S.IsOrdinaryChild T) (hSU : S.IsOrdinaryChild U)
    (hT : T.IsLeaf) (hU : U.IsLeaf) : T = U := by
  rcases hST with ⟨a, ha, hTa⟩
  rcases hSU with ⟨b, hb, hUb⟩
  have hab : a = b := Nat.le_antisymm
    (leaf_deletes_largest hb hUb hU ha)
    (leaf_deletes_largest ha hTa hT hb)
  subst b
  ext n
  exact (hTa n).trans (hUb n).symm

/-- Positive genus supplies an actual largest gap. -/
theorem exists_isFrobenius {S : NumericalSemigroup} (hgenus : 0 < S.genus) :
    ∃ f : ℕ, S.IsFrobenius f := by
  have hne := S.gaps_nonempty_iff.mpr hgenus
  refine ⟨S.gaps.max' hne, ?_, ?_⟩
  · exact (S.mem_gaps _).mp (Finset.max'_mem S.gaps hne)
  · intro n hn
    exact Finset.le_max' S.gaps n ((S.mem_gaps n).mpr hn)

/-- The natural largest-gap relation agrees with the signed Frobenius API. -/
theorem frobenius_eq_of_isFrobenius {S : NumericalSemigroup} {f : ℕ}
    (hf : S.IsFrobenius f) : S.frobenius = (f : ℤ) := by
  have hne : S.gaps.Nonempty := ⟨f, (S.mem_gaps f).mpr hf.1⟩
  rw [S.frobenius_eq_max hne]
  congr 1
  apply Nat.le_antisymm
  · exact hf.2 _ ((S.mem_gaps _).mp (Finset.max'_mem S.gaps hne))
  · exact Finset.le_max' S.gaps f ((S.mem_gaps f).mpr hf.1)

/-- Our effective-generator definition is exactly the manuscript's one:
minimal, and strictly above the signed Frobenius number. -/
theorem isEffectiveGenerator_iff {S : NumericalSemigroup} {a : ℕ} :
    S.IsEffectiveGenerator a ↔
      S.IsMinimalGenerator a ∧ S.frobenius < (a : ℤ) := by
  constructor
  · rintro ⟨ha, hgap⟩
    refine ⟨ha, ?_⟩
    by_cases hne : S.gaps.Nonempty
    · rw [S.frobenius_eq_max hne]
      exact_mod_cast hgap _ ((S.mem_gaps _).mp (Finset.max'_mem S.gaps hne))
    · simp only [frobenius, hne, dite_false]
      omega
  · rintro ⟨ha, hF⟩
    refine ⟨ha, ?_⟩
    intro n hn
    have hle := S.gap_le_frobenius hn
    omega

/-- Every positive-genus semigroup has a unique ordinary parent. -/
theorem existsUnique_ordinaryParent {S : NumericalSemigroup}
    (hgenus : 0 < S.genus) : ∃! P : NumericalSemigroup, P.IsOrdinaryChild S := by
  obtain ⟨f, hf⟩ := exists_isFrobenius hgenus
  refine ⟨S.restoreFrobenius f hf, isOrdinaryChild_restoreFrobenius hf, ?_⟩
  intro P hP
  exact ordinaryParent_unique hP (isOrdinaryChild_restoreFrobenius hf)

@[simp] theorem gaps_removeGenerator {S : NumericalSemigroup} {a : ℕ}
    (ha : S.IsMinimalGenerator a) :
    (S.removeGenerator a ha).gaps = insert a S.gaps := by
  classical
  ext n
  simp only [mem_gaps, mem_removeGenerator, Finset.mem_insert]
  tauto

@[simp] theorem genus_removeGenerator {S : NumericalSemigroup} {a : ℕ}
    (ha : S.IsMinimalGenerator a) :
    (S.removeGenerator a ha).genus = S.genus + 1 := by
  classical
  have hnot : a ∉ S.gaps := by simpa using ha.1
  simp [genus, gaps_removeGenerator, hnot]

@[simp] theorem gaps_restoreFrobenius {S : NumericalSemigroup} {f : ℕ}
    (hf : S.IsFrobenius f) :
    (S.restoreFrobenius f hf).gaps = S.gaps.erase f := by
  classical
  ext n
  simp only [mem_gaps, mem_restoreFrobenius, Finset.mem_erase]
  tauto

/-- Restoring the Frobenius removes exactly one gap. -/
theorem genus_restoreFrobenius_add_one {S : NumericalSemigroup} {f : ℕ}
    (hf : S.IsFrobenius f) :
    (S.restoreFrobenius f hf).genus + 1 = S.genus := by
  classical
  simpa only [genus, gaps_restoreFrobenius] using
    Finset.card_erase_add_one ((S.mem_gaps f).mpr hf.1)

/-- Ordinary children have genus exactly one greater than their parent. -/
theorem genus_of_ordinaryChild {S T : NumericalSemigroup}
    (hST : S.IsOrdinaryChild T) : T.genus = S.genus + 1 := by
  rcases hST with ⟨a, ha, hT⟩
  have heq : T = S.removeGenerator a ha.1 := by
    ext n
    exact hT n
  rw [heq, genus_removeGenerator]

end NumericalSemigroup
end SubmittedGenus
