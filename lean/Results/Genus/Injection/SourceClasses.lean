import Results.Genus.Injection.Restoration

/-!
# The exact ordered source tests of the submitted paper

The seven tests are evaluated in manuscript order `L/P/C/T/D/I/B`;
`E` is their common remainder. The underlying objects are the proved
all-multiplicity Kunz data, equivalent to genuine numerical semigroups.
These definitions do not insert cardinality or capacity assumptions.
-/

namespace SubmittedGenus

namespace NumericalSemigroup

/-- Depth transported through the proved genuine-semigroup correspondence. -/
noncomputable def kunzDepth (S : NumericalSemigroup) : ℕ :=
  (KunzData.equivNumericalSemigroup.symm S).depth

@[simp] theorem kunzDepth_toSemigroup (d : KunzData) :
    d.toSemigroup.kunzDepth = d.depth := by
  change (KunzData.equivNumericalSemigroup.symm
    (KunzData.equivNumericalSemigroup d)).depth = d.depth
  rw [Equiv.symm_apply_apply]

end NumericalSemigroup

namespace OriginalSources

attribute [local instance] Classical.propDecidable

/-- Names and order match the submitted source partition exactly. -/
inductive Sector
  | L | P | C | T | D | I | B | E
  deriving DecidableEq, Fintype

/-- First test: all depth-at-most-three words. -/
def low (d : KunzData) : Prop := d.depth ≤ 3

/-- Second test, applied only after low sources have been removed. -/
def nonleaf (d : KunzData) : Prop := ¬ d.toSemigroup.IsLeaf

/-- Third test uses a genuine ordinary parent. -/
def lowParent (d : KunzData) : Prop :=
  ∃ P : NumericalSemigroup, P.IsOrdinaryChild d.toSemigroup ∧ P.kunzDepth ≤ 3

/-- Fourth test: the literal word `(5,u)` with every letter of `u` at most three. -/
def initialFive (d : KunzData) : Prop :=
  KunzWord.coord d.2.val 1 = 5 ∧ ∀ i, 1 ≤ i.val → d.2.val i ≤ 3

/-- Every letter differs from `1`. -/
def noOne (d : KunzData) : Prop := ∀ i, d.2.val i ≠ 1

/-- Fifth test: depth at least six, or no-one depth four/five. -/
def deepOrNoOne (d : KunzData) : Prop :=
  6 ≤ d.depth ∨ ((d.depth = 4 ∨ d.depth = 5) ∧ noOne d)

/-- Sixth test: a unique isolated `5` at a physical position at least two. -/
def isolatedFive (d : KunzData) : Prop :=
  ∃ p, 1 ≤ p.val ∧ d.2.val p = 5 ∧ ∀ i, i ≠ p → d.2.val i ≤ 3

/-- The unique letter `1` occupies the final physical coordinate. -/
def soleOneFinal (d : KunzData) : Prop :=
  KunzWord.coord d.2.val (d.1.val - 1) = 1 ∧
    ∀ i, i.val + 1 ≠ d.1.val - 1 → d.2.val i ≠ 1

/-- Seventh test: depth four with sole final `1`. -/
def finalOneFour (d : KunzData) : Prop := d.depth = 4 ∧ soleOneFinal d

/-- Applying each test only to sources not selected earlier. -/
noncomputable def sector (d : KunzData) : Sector :=
  if low d then .L else
  if nonleaf d then .P else
  if lowParent d then .C else
  if initialFive d then .T else
  if deepOrNoOne d then .D else
  if isolatedFive d then .I else
  if finalOneFour d then .B else .E

/-- The exact finite genus-`g` source class. -/
def SourceClass (g : ℕ) (s : Sector) :=
  {d : KunzData.WeightFibre g // sector d.val = s}

noncomputable instance (g : ℕ) (s : Sector) : Fintype (SourceClass g s) :=
  inferInstanceAs (Fintype {d : KunzData.WeightFibre g // sector d.val = s})

@[simp] theorem sector_L_iff (d : KunzData) : sector d = .L ↔ low d := by
  simp only [sector]
  split_ifs <;> simp_all

theorem sector_P_iff (d : KunzData) :
    sector d = .P ↔ ¬ low d ∧ nonleaf d := by
  simp only [sector]
  split_ifs <;> simp_all

theorem sector_C_iff (d : KunzData) :
    sector d = .C ↔ ¬ low d ∧ ¬ nonleaf d ∧ lowParent d := by
  simp only [sector]
  split_ifs <;> simp_all

theorem sector_T_iff (d : KunzData) :
    sector d = .T ↔ ¬ low d ∧ ¬ nonleaf d ∧ ¬ lowParent d ∧ initialFive d := by
  simp only [sector]
  split_ifs <;> simp_all

theorem sector_D_iff (d : KunzData) :
    sector d = .D ↔ ¬ low d ∧ ¬ nonleaf d ∧ ¬ lowParent d ∧
      ¬ initialFive d ∧ deepOrNoOne d := by
  simp only [sector]
  split_ifs <;> simp_all

theorem sector_I_iff (d : KunzData) :
    sector d = .I ↔ ¬ low d ∧ ¬ nonleaf d ∧ ¬ lowParent d ∧
      ¬ initialFive d ∧ ¬ deepOrNoOne d ∧ isolatedFive d := by
  simp only [sector]
  split_ifs <;> simp_all

theorem sector_B_iff (d : KunzData) :
    sector d = .B ↔ ¬ low d ∧ ¬ nonleaf d ∧ ¬ lowParent d ∧
      ¬ initialFive d ∧ ¬ deepOrNoOne d ∧ ¬ isolatedFive d ∧ finalOneFour d := by
  simp only [sector]
  split_ifs <;> simp_all

theorem sector_E_iff (d : KunzData) :
    sector d = .E ↔ ¬ low d ∧ ¬ nonleaf d ∧ ¬ lowParent d ∧
      ¬ initialFive d ∧ ¬ deepOrNoOne d ∧ ¬ isolatedFive d ∧ ¬ finalOneFour d := by
  simp only [sector]
  split_ifs <;> simp_all

/-- Membership is disjoint by construction, with no informal tie-breaking. -/
theorem sectors_disjoint {d : KunzData} {s t : Sector}
    (hs : sector d = s) (ht : sector d = t) : s = t := hs.symm.trans ht

/-- Every source is assigned exactly once. -/
theorem existsUnique_sector (d : KunzData) : ∃! s : Sector, sector d = s := by
  exact ⟨sector d, rfl, fun _ h => h.symm⟩

/-- The residual is genuinely a high-depth leaf and contains at least one `1`. -/
theorem exceptional_leaf_depth_and_one {d : KunzData} (h : sector d = .E) :
    d.toSemigroup.IsLeaf ∧ (d.depth = 4 ∨ d.depth = 5) ∧ ∃ i, d.2.val i = 1 := by
  rcases (sector_E_iff d).mp h with ⟨hL, hP, hC, hT, hD, hI, hB⟩
  have hleaf : d.toSemigroup.IsLeaf := by simpa only [nonleaf, not_not] using hP
  have hhigh : ¬ d.depth ≤ 3 := hL
  have hnotdeep : ¬ 6 ≤ d.depth := fun hd => hD (Or.inl hd)
  have hdepth : d.depth = 4 ∨ d.depth = 5 := by omega
  have hOne : ¬ noOne d := fun hno => hD (Or.inr ⟨hdepth, hno⟩)
  refine ⟨hleaf, hdepth, ?_⟩
  simpa only [noOne, not_forall, not_not] using hOne

end OriginalSources
end SubmittedGenus
