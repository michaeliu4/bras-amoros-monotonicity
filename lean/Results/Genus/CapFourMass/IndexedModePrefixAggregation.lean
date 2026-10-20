import Results.Genus.CapFourMass.OriginalPrefixTargets
import Results.Genus.CapFourMass.IntervalCompute

/-! Source-exact indexed aggregation of the original pure and mixed prefixes.
The three bounded indices remain nested, so every original pivot pair and
base occurs exactly once by Finset/Fin indexing. No flattened coverage claim,
per-base expression, or expansion of the real source terms is needed.

The box function can be populated by compact certificate lookup. Its only
semantic obligation is Contains at the requested original (r,p-r,n). -/
open scoped BigOperators
namespace SubmittedGenus.CapFourMass.Interval.IndexedModePrefix

/-- Endpoint addition is exact; there is no rounding at an aggregation step. -/
def sumBox {ι : Type*} (s : Finset ι) (b : ι → Box) : Box :=
  ⟨∑ i ∈ s, (b i).lo, ∑ i ∈ s, (b i).hi⟩

theorem sumBox_contains {ι : Type*} (s : Finset ι) (b : ι → Box) (x : ι → ℝ)
    (h : ∀ i ∈ s, Contains (b i) (x i)) :
    Contains (sumBox s b) (∑ i ∈ s, x i) := by
  constructor
  · change ((∑ i ∈ s, (b i).lo : ℤ) : ℝ) ≤ (unit : ℝ) * ∑ i ∈ s, x i
    rw [Int.cast_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi => (h i hi).1
  · change (unit : ℝ) * (∑ i ∈ s, x i) ≤ ((∑ i ∈ s, (b i).hi : ℤ) : ℝ)
    rw [Int.cast_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi => (h i hi).2

@[simp] theorem sumBox_empty {ι : Type*} (b : ι → Box) :
    sumBox ∅ b = point 0 := by simp [sumBox, point]

theorem sumBox_union {ι : Type*} [DecidableEq ι] (s t : Finset ι) (b : ι → Box)
    (h : Disjoint s t) : sumBox (s ∪ t) b = add (sumBox s b) (sumBox t b) := by
  simp only [sumBox, add, Finset.sum_union h]

theorem sumBox_range_succ (b : ℕ → Box) (P : ℕ) :
    sumBox (Finset.range (P+1)) b = add (sumBox (Finset.range P) b) (b P) := by
  simp only [sumBox, add, Finset.sum_range_succ]

abbrev BaseBoxes := ℕ → ℕ → ℕ → Box

def pureNumerator (b : BaseBoxes) (r d : ℕ) : Box :=
  sumBox Finset.univ (fun n : Fin 2 => b r d n.val)

def mixedNumerator (b : BaseBoxes) (r d : ℕ) : Box :=
  sumBox Finset.univ (fun n : Fin (2*d) => b r d n.val)

def purePair (b : BaseBoxes) (den : Box) (r d : ℕ) : Box :=
  divPos (pureNumerator b r d) den

def mixedPair (b : BaseBoxes) (den : ℕ → Box) (r d : ℕ) : Box :=
  divPos (mixedNumerator b r d) (den d)

noncomputable def pureSourceRow (p : ℕ) : ℝ :=
  ∑ r ∈ Finset.Ico 1 p, (∑ n : Fin 2, sourcePureSeries r (p-r) n.val) /
    (1-(normalizer*lam)^2)

noncomputable def mixedSourceRow (p : ℕ) : ℝ :=
  ∑ r ∈ Finset.Ico 1 p, (∑ n : Fin (2*(p-r)), sourceMixedSeries r (p-r) n.val) /
    (1-(normalizer*lam)^(2*(p-r))*rho^2)

def pureRow (b : BaseBoxes) (den : Box) (p : ℕ) : Box :=
  sumBox (Finset.Ico 1 p) (fun r => purePair b den r (p-r))

def mixedRow (b : BaseBoxes) (den : ℕ → Box) (p : ℕ) : Box :=
  sumBox (Finset.Ico 1 p) (fun r => mixedPair b den r (p-r))

def pureRows (b : BaseBoxes) (den : Box) (rows : Finset ℕ) : Box :=
  sumBox rows (pureRow b den)

def mixedRows (b : BaseBoxes) (den : ℕ → Box) (rows : Finset ℕ) : Box :=
  sumBox rows (mixedRow b den)

def purePrefix (b : BaseBoxes) (den : Box) (P : ℕ) : Box :=
  pureRows b den (Finset.range (P+1))

def mixedPrefix (b : BaseBoxes) (den : ℕ → Box) (P : ℕ) : Box :=
  mixedRows b den (Finset.range (P+1))

theorem purePair_contains (b : BaseBoxes) (den : Box) (r d : ℕ)
    (hbase : ∀ n : Fin 2, Contains (b r d n.val) (sourcePureSeries r d n.val))
    (hden : Contains den (1-(normalizer*lam)^2)) (hpos : 0 < den.lo) :
    Contains (purePair b den r d)
      ((∑ n : Fin 2, sourcePureSeries r d n.val)/(1-(normalizer*lam)^2)) :=
  divPos_contains (sumBox_contains _ _ _ (fun n _ => hbase n)) hden hpos

theorem mixedPair_contains (b : BaseBoxes) (den : ℕ → Box) (r d : ℕ)
    (hbase : ∀ n : Fin (2*d), Contains (b r d n.val) (sourceMixedSeries r d n.val))
    (hden : Contains (den d) (1-(normalizer*lam)^(2*d)*rho^2))
    (hpos : 0 < (den d).lo) :
    Contains (mixedPair b den r d)
      ((∑ n : Fin (2*d), sourceMixedSeries r d n.val)/(1-(normalizer*lam)^(2*d)*rho^2)) :=
  divPos_contains (sumBox_contains _ _ _ (fun n _ => hbase n)) hden hpos

theorem pureRow_contains (b : BaseBoxes) (den : Box) (p : ℕ)
    (hbase : ∀ r ∈ Finset.Ico 1 p, ∀ n : Fin 2,
      Contains (b r (p-r) n.val) (sourcePureSeries r (p-r) n.val))
    (hden : Contains den (1-(normalizer*lam)^2)) (hpos : 0 < den.lo) :
    Contains (pureRow b den p) (pureSourceRow p) :=
  sumBox_contains _ _ _ (fun r hr => purePair_contains b den r (p-r) (hbase r hr) hden hpos)

theorem mixedRow_contains (b : BaseBoxes) (den : ℕ → Box) (p : ℕ)
    (hbase : ∀ r ∈ Finset.Ico 1 p, ∀ n : Fin (2*(p-r)),
      Contains (b r (p-r) n.val) (sourceMixedSeries r (p-r) n.val))
    (hden : ∀ r ∈ Finset.Ico 1 p, Contains (den (p-r))
      (1-(normalizer*lam)^(2*(p-r))*rho^2))
    (hpos : ∀ r ∈ Finset.Ico 1 p, 0 < (den (p-r)).lo) :
    Contains (mixedRow b den p) (mixedSourceRow p) :=
  sumBox_contains _ _ _ (fun r hr =>
    mixedPair_contains b den r (p-r) (hbase r hr) (hden r hr) (hpos r hr))

/-- Any finite collection of original rows may be certified independently. -/
theorem pureRows_contains (b : BaseBoxes) (den : Box) (rows : Finset ℕ)
    (hbase : ∀ p ∈ rows, ∀ r ∈ Finset.Ico 1 p, ∀ n : Fin 2,
      Contains (b r (p-r) n.val) (sourcePureSeries r (p-r) n.val))
    (hden : Contains den (1-(normalizer*lam)^2)) (hpos : 0 < den.lo) :
    Contains (pureRows b den rows) (∑ p ∈ rows, pureSourceRow p) :=
  sumBox_contains _ _ _ (fun p hp => pureRow_contains b den p (hbase p hp) hden hpos)

theorem mixedRows_contains (b : BaseBoxes) (den : ℕ → Box) (rows : Finset ℕ)
    (hbase : ∀ p ∈ rows, ∀ r ∈ Finset.Ico 1 p, ∀ n : Fin (2*(p-r)),
      Contains (b r (p-r) n.val) (sourceMixedSeries r (p-r) n.val))
    (hden : ∀ p ∈ rows, ∀ r ∈ Finset.Ico 1 p, Contains (den (p-r))
      (1-(normalizer*lam)^(2*(p-r))*rho^2))
    (hpos : ∀ p ∈ rows, ∀ r ∈ Finset.Ico 1 p, 0 < (den (p-r)).lo) :
    Contains (mixedRows b den rows) (∑ p ∈ rows, mixedSourceRow p) :=
  sumBox_contains _ _ _ (fun p hp =>
    mixedRow_contains b den p (hbase p hp) (hden p hp) (hpos p hp))

/-- Original bounds, original two bases, and original pure denominator. -/
theorem purePrefix_contains (b : BaseBoxes) (den : Box) (P : ℕ)
    (hbase : ∀ p ≤ P, ∀ r ∈ Finset.Ico 1 p, ∀ n : Fin 2,
      Contains (b r (p-r) n.val) (sourcePureSeries r (p-r) n.val))
    (hden : Contains den (1-(normalizer*lam)^2)) (hpos : 0 < den.lo) :
    Contains (purePrefix b den P) (originalPurePrefix P) :=
  pureRows_contains b den _
    (fun p hp => hbase p (Nat.le_of_lt_succ (Finset.mem_range.mp hp))) hden hpos

/-- Original bounds, original 2(p-r) bases, and original mixed denominator. -/
theorem mixedPrefix_contains (b : BaseBoxes) (den : ℕ → Box) (P : ℕ)
    (hbase : ∀ p ≤ P, ∀ r ∈ Finset.Ico 1 p, ∀ n : Fin (2*(p-r)),
      Contains (b r (p-r) n.val) (sourceMixedSeries r (p-r) n.val))
    (hden : ∀ p ≤ P, ∀ r ∈ Finset.Ico 1 p, Contains (den (p-r))
      (1-(normalizer*lam)^(2*(p-r))*rho^2))
    (hpos : ∀ p ≤ P, ∀ r ∈ Finset.Ico 1 p, 0 < (den (p-r)).lo) :
    Contains (mixedPrefix b den P) (originalMixedPrefix P) :=
  mixedRows_contains b den _
    (fun p hp => hbase p (Nat.le_of_lt_succ (Finset.mem_range.mp hp)))
    (fun p hp => hden p (Nat.le_of_lt_succ (Finset.mem_range.mp hp)))
    (fun p hp => hpos p (Nat.le_of_lt_succ (Finset.mem_range.mp hp)))

/-- Rows can be rounded/enlarged and stored as checked constants before final assembly. -/
theorem purePrefix_contains_of_rows (rows : ℕ → Box) (P : ℕ)
    (h : ∀ p ≤ P, Contains (rows p) (pureSourceRow p)) :
    Contains (sumBox (Finset.range (P+1)) rows) (originalPurePrefix P) :=
  sumBox_contains _ _ _ (fun p hp => h p (Nat.le_of_lt_succ (Finset.mem_range.mp hp)))

theorem mixedPrefix_contains_of_rows (rows : ℕ → Box) (P : ℕ)
    (h : ∀ p ≤ P, Contains (rows p) (mixedSourceRow p)) :
    Contains (sumBox (Finset.range (P+1)) rows) (originalMixedPrefix P) :=
  sumBox_contains _ _ _ (fun p hp => h p (Nat.le_of_lt_succ (Finset.mem_range.mp hp)))

end SubmittedGenus.CapFourMass.Interval.IndexedModePrefix
