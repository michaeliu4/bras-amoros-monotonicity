import Mathlib.Algebra.Group.Submonoid.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Ext
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.SplitIfs

/-!
# Actual numerical semigroups

Foundations for the submitted manuscript. A numerical semigroup is literally an
additive submonoid of the natural numbers with finite complement. No counting
surrogate occurs in these definitions.
-/

namespace SubmittedGenus

/-- A numerical semigroup, including the genus-zero semigroup `ℕ`. -/
structure NumericalSemigroup where
  toAddSubmonoid : AddSubmonoid ℕ
  finite_compl : Set.Finite (toAddSubmonoid : Set ℕ)ᶜ

namespace NumericalSemigroup

instance : Membership ℕ NumericalSemigroup := ⟨fun S n => n ∈ S.toAddSubmonoid⟩

@[simp] theorem mem_toAddSubmonoid (S : NumericalSemigroup) (n : ℕ) :
    n ∈ S.toAddSubmonoid ↔ n ∈ S := Iff.rfl

@[simp] theorem zero_mem (S : NumericalSemigroup) : 0 ∈ S :=
  S.toAddSubmonoid.zero_mem

theorem add_mem (S : NumericalSemigroup) {a b : ℕ} (ha : a ∈ S) (hb : b ∈ S) :
    a + b ∈ S := S.toAddSubmonoid.add_mem ha hb

theorem mul_mem (S : NumericalSemigroup) {a : ℕ} (ha : a ∈ S) (k : ℕ) : k * a ∈ S := by
  induction k with
  | zero => simpa using S.zero_mem
  | succ k ih => simpa only [Nat.succ_mul] using S.add_mem ih ha

@[ext] theorem ext {S T : NumericalSemigroup} (h : ∀ n : ℕ, n ∈ S ↔ n ∈ T) : S = T := by
  cases S with
  | mk S hS =>
    cases T with
    | mk T hT =>
      have hST : S = T := SetLike.ext h
      subst T
      rfl

/-- The actual finite complement, rather than a code or a proxy. -/
noncomputable def gaps (S : NumericalSemigroup) : Finset ℕ := S.finite_compl.toFinset

@[simp] theorem mem_gaps (S : NumericalSemigroup) (n : ℕ) : n ∈ S.gaps ↔ n ∉ S := by
  simp [gaps]

@[simp] theorem zero_not_mem_gaps (S : NumericalSemigroup) : 0 ∉ S.gaps := by simp

/-- Genus is the number of omitted natural numbers. -/
noncomputable def genus (S : NumericalSemigroup) : ℕ := S.gaps.card

/-- A convenient positive bound beyond every gap. -/
noncomputable def conductorBound (S : NumericalSemigroup) : ℕ := S.gaps.sup id + 1

theorem gap_lt_conductorBound (S : NumericalSemigroup) {n : ℕ} (hn : n ∉ S) :
    n < S.conductorBound := by
  have h := Finset.le_sup (f := id) ((S.mem_gaps n).mpr hn)
  exact Nat.lt_succ_of_le h

theorem mem_of_conductorBound_le (S : NumericalSemigroup) {n : ℕ}
    (hn : S.conductorBound ≤ n) : n ∈ S := by
  by_contra h
  exact (Nat.not_lt_of_ge hn) (S.gap_lt_conductorBound h)

/-- The signed Frobenius number is `-1` precisely for the empty gap set. -/
noncomputable def frobenius (S : NumericalSemigroup) : ℤ :=
  if h : S.gaps.Nonempty then (S.gaps.max' h : ℤ) else -1

/-- The full natural numbers form the unique genus-zero semigroup. -/
def full : NumericalSemigroup where
  toAddSubmonoid := ⊤
  finite_compl := by simp

@[simp] theorem mem_full (n : ℕ) : n ∈ full := by trivial

@[simp] theorem gaps_full : full.gaps = ∅ := by ext n; simp

@[simp] theorem genus_full : full.genus = 0 := by simp [genus]

@[simp] theorem frobenius_full : full.frobenius = -1 := by simp [frobenius]

theorem gaps_injective : Function.Injective gaps := by
  intro S T h
  apply ext
  intro n
  have hmem : n ∈ S.gaps ↔ n ∈ T.gaps := by rw [h]
  simpa only [mem_gaps, not_iff_not] using hmem

@[simp] theorem genus_eq_zero (S : NumericalSemigroup) : S.genus = 0 ↔ S = full := by
  constructor
  · intro h
    apply gaps_injective
    simpa [genus] using Finset.card_eq_zero.mp h
  · rintro rfl
    exact genus_full

theorem gaps_nonempty_iff (S : NumericalSemigroup) : S.gaps.Nonempty ↔ 0 < S.genus := by
  exact Finset.card_pos.symm

theorem frobenius_eq_max (S : NumericalSemigroup) (h : S.gaps.Nonempty) :
    S.frobenius = (S.gaps.max' h : ℤ) := by simp [frobenius, h]

theorem frobenius_nonneg (S : NumericalSemigroup) (h : 0 < S.genus) :
    0 ≤ S.frobenius := by
  rw [S.frobenius_eq_max ((S.gaps_nonempty_iff).mpr h)]
  exact_mod_cast Nat.zero_le _

theorem gap_le_frobenius (S : NumericalSemigroup) {n : ℕ} (hn : n ∉ S) :
    (n : ℤ) ≤ S.frobenius := by
  have hn' := (S.mem_gaps n).mpr hn
  have h : S.gaps.Nonempty := ⟨n, hn'⟩
  rw [S.frobenius_eq_max h]
  exact_mod_cast Finset.le_max' S.gaps n hn'

theorem frobenius_not_mem (S : NumericalSemigroup) (h : 0 < S.genus) :
    S.frobenius.toNat ∉ S := by
  rw [S.frobenius_eq_max ((S.gaps_nonempty_iff).mpr h)]
  simpa using (S.mem_gaps _).mp (Finset.max'_mem S.gaps _)

theorem frobenius_eq_of_greatest_gap (S : NumericalSemigroup) {f : ℕ} (hf : f ∉ S)
    (hmax : ∀ n : ℕ, n ∉ S → n ≤ f) : S.frobenius = (f : ℤ) := by
  have hmem := (S.mem_gaps f).mpr hf
  have hne : S.gaps.Nonempty := ⟨f, hmem⟩
  rw [S.frobenius_eq_max hne]
  congr 1
  exact Nat.le_antisymm (hmax _ ((S.mem_gaps _).mp (Finset.max'_mem _ _)))
    (Finset.le_max' _ _ hmem)

theorem mem_of_frobenius_lt (S : NumericalSemigroup) {n : ℕ}
    (hn : S.frobenius < (n : ℤ)) : n ∈ S := by
  by_contra h
  exact (not_le_of_gt hn) (S.gap_le_frobenius h)

/-- Reflection about any gap sends nongaps below it injectively into gaps.
This is the elementary bound underlying finiteness at fixed genus. -/
theorem gap_succ_le_two_genus (S : NumericalSemigroup) {n : ℕ} (hn : n ∉ S) :
    n + 1 ≤ 2 * S.genus := by
  classical
  have reflected_gap (i : Fin (n + 1)) (hi : (i : ℕ) ∈ S) : n - i ∉ S := by
    intro hc
    have hs := S.add_mem hi hc
    have he : (i : ℕ) + (n - i) = n := by omega
    exact hn (he ▸ hs)
  let f : Fin (n + 1) → Bool × {k : ℕ // k ∈ S.gaps} := fun i =>
    if hi : (i : ℕ) ∈ S then
      (true, ⟨n - i, (S.mem_gaps _).mpr (reflected_gap i hi)⟩)
    else (false, ⟨i, (S.mem_gaps _).mpr hi⟩)
  have hf : Function.Injective f := by
    intro i j h
    dsimp [f] at h
    split_ifs at h with hi hj hj
    · have he : n - (i : ℕ) = n - (j : ℕ) := congrArg (fun p => p.2.val) h
      apply Fin.ext
      omega
    · have := congrArg Prod.fst h
      contradiction
    · have := congrArg Prod.fst h
      contradiction
    · exact Fin.ext (congrArg (fun p => p.2.val) h)
  have hc := Fintype.card_le_of_injective f hf
  simpa [genus] using hc

theorem gap_lt_two_genus (S : NumericalSemigroup) {n : ℕ} (hn : n ∉ S) :
    n < 2 * S.genus := by
  have := S.gap_succ_le_two_genus hn
  omega

theorem gaps_subset_range (S : NumericalSemigroup) :
    S.gaps ⊆ Finset.range (2 * S.genus) := by
  intro n hn
  exact Finset.mem_range.mpr (S.gap_lt_two_genus ((S.mem_gaps n).mp hn))

/-- Fixed-genus numerical semigroups form a finite set of actual submonoids. -/
theorem finite_genus_fibre (g : ℕ) : Set.Finite {S : NumericalSemigroup | S.genus = g} := by
  classical
  apply Set.Finite.of_injOn (f := gaps)
    (s := {S : NumericalSemigroup | S.genus = g})
    (t := ↑((Finset.range (2 * g)).powerset))
  · intro S hS
    change S.genus = g at hS
    simp only [Finset.mem_coe, Finset.mem_powerset]
    simpa only [hS] using S.gaps_subset_range
  · exact gaps_injective.injOn
  · exact Finset.finite_toSet _

/-- The genuine genus fibre used in the submitted paper's count. -/
def GenusFibre (g : ℕ) := {S : NumericalSemigroup // S.genus = g}

noncomputable instance (g : ℕ) : Fintype (GenusFibre g) :=
  (finite_genus_fibre g).fintype

/-- Number of all numerical semigroups of genus `g`. -/
noncomputable def count (g : ℕ) : ℕ := Fintype.card (GenusFibre g)

instance : Unique (GenusFibre 0) where
  default := ⟨full, genus_full⟩
  uniq S := Subtype.ext ((genus_eq_zero S.val).mp S.property)

@[simp] theorem count_zero : count 0 = 1 := by simp [count]

/-- The ordinary semigroup with its sole gap at one. -/
def oneGap : NumericalSemigroup where
  toAddSubmonoid :=
    { carrier := {n | n ≠ 1}
      zero_mem' := by simp
      add_mem' := by intro a b ha hb; simp only [Set.mem_setOf_eq] at *; omega }
  finite_compl := by
    apply (Set.finite_singleton 1).subset
    intro n hn
    change ¬ n ≠ 1 at hn
    simpa using hn

@[simp] theorem mem_oneGap (n : ℕ) : n ∈ oneGap ↔ n ≠ 1 := Iff.rfl

@[simp] theorem gaps_oneGap : oneGap.gaps = {1} := by ext n; simp

@[simp] theorem genus_oneGap : oneGap.genus = 1 := by simp [genus]

@[simp] theorem genus_eq_one (S : NumericalSemigroup) : S.genus = 1 ↔ S = oneGap := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h
    have hgap : a ∉ S := (S.mem_gaps a).mp (by rw [ha]; simp)
    have habound := S.gap_lt_two_genus hgap
    have ha0 : a ≠ 0 := by intro he; subst a; exact hgap S.zero_mem
    have ha1 : a = 1 := by omega
    apply gaps_injective
    rw [ha, ha1, gaps_oneGap]
  · rintro rfl
    exact genus_oneGap

instance : Unique (GenusFibre 1) where
  default := ⟨oneGap, genus_oneGap⟩
  uniq S := Subtype.ext ((genus_eq_one S.val).mp S.property)

@[simp] theorem count_one : count 1 = 1 := by simp [count]

/-- Multiplicity is the least positive member, including one for `ℕ`. -/
def IsMultiplicity (S : NumericalSemigroup) (m : ℕ) : Prop :=
  0 < m ∧ m ∈ S ∧ ∀ n : ℕ, 0 < n → n ∈ S → m ≤ n

theorem exists_positive_mem (S : NumericalSemigroup) : ∃ n : ℕ, 0 < n ∧ n ∈ S := by
  refine ⟨S.conductorBound, ?_, S.mem_of_conductorBound_le le_rfl⟩
  simp [conductorBound]

noncomputable def multiplicity (S : NumericalSemigroup) : ℕ := by
  classical
  exact Nat.find S.exists_positive_mem

theorem isMultiplicity_multiplicity (S : NumericalSemigroup) :
    S.IsMultiplicity S.multiplicity := by
  classical
  refine ⟨(Nat.find_spec S.exists_positive_mem).1,
    (Nat.find_spec S.exists_positive_mem).2, ?_⟩
  intro n hn hnS
  exact Nat.find_min' S.exists_positive_mem ⟨hn, hnS⟩

theorem IsMultiplicity.unique {S : NumericalSemigroup} {m n : ℕ}
    (hm : S.IsMultiplicity m) (hn : S.IsMultiplicity n) : m = n :=
  Nat.le_antisymm (hm.2.2 n hn.1 hn.2.1) (hn.2.2 m hm.1 hm.2.1)

theorem exists_residue_mem (S : NumericalSemigroup) {m : ℕ} (hm : 0 < m) (r : ℕ) :
    ∃ k : ℕ, r + m * k ∈ S := by
  refine ⟨S.conductorBound, S.mem_of_conductorBound_le ?_⟩
  have h := Nat.mul_le_mul_right S.conductorBound hm
  omega

/-- The first admitted quotient in a residue class. -/
noncomputable def residueLevel (S : NumericalSemigroup) {m : ℕ} (hm : 0 < m) (r : ℕ) : ℕ := by
  classical
  exact Nat.find (S.exists_residue_mem hm r)

theorem residueLevel_mem (S : NumericalSemigroup) {m : ℕ} (hm : 0 < m) (r : ℕ) :
    r + m * S.residueLevel hm r ∈ S := by
  classical
  exact Nat.find_spec (S.exists_residue_mem hm r)

theorem residueLevel_le (S : NumericalSemigroup) {m r k : ℕ} (hm : 0 < m)
    (hk : r + m * k ∈ S) : S.residueLevel hm r ≤ k := by
  classical
  exact Nat.find_min' (S.exists_residue_mem hm r) hk

theorem residue_mem_iff (S : NumericalSemigroup) {m : ℕ} (hm : 0 < m) (hmS : m ∈ S)
    (r k : ℕ) : r + m * k ∈ S ↔ S.residueLevel hm r ≤ k := by
  constructor
  · exact S.residueLevel_le hm
  · intro hk
    have h := S.add_mem (S.residueLevel_mem hm r) (S.mul_mem hmS (k - S.residueLevel hm r))
    convert h using 1
    rw [Nat.mul_comm (k - S.residueLevel hm r) m, Nat.add_assoc, ← Nat.mul_add]
    rw [Nat.add_sub_of_le hk]

@[simp] theorem residueLevel_zero (S : NumericalSemigroup) {m : ℕ} (hm : 0 < m) :
    S.residueLevel hm 0 = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact S.residueLevel_le hm (by simpa using S.zero_mem)

end NumericalSemigroup
end SubmittedGenus
