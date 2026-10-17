import Results.Genus.RawGraph
import Results.Genus.WeightedSeries

/-!
# Genuine multiple-five population

This population consists of actual valid Kunz data (and therefore genuine
numerical semigroups), at depth five with at least two coordinates equal to
five. It is not defined by the raw two-pivot relaxation.
-/

noncomputable section
open scoped BigOperators
namespace SubmittedGenus.CapFiveMass

/-- Exactly the source population called B in the submitted manuscript. -/
def HasMultipleFive (d : KunzData) : Prop :=
  (∀ i, d.2.val i ≤ 5) ∧ ∃ i j, i ≠ j ∧ d.2.val i = 5 ∧ d.2.val j = 5

abbrev GenuineFive := {d : KunzData // HasMultipleFive d}
abbrev GenuineFiveAt (g : ℕ) := {d : KunzData.WeightFibre g // HasMultipleFive d.val}

noncomputable instance (g : ℕ) : Fintype (GenuineFiveAt g) := by
  classical
  exact inferInstanceAs (Fintype {d : KunzData.WeightFibre g // HasMultipleFive d.val})

/-- Actual finite source count B_g. -/
def count (g : ℕ) : ℕ := Fintype.card (GenuineFiveAt g)

/-- B(z) in coefficient order. Convergence is a separate, substantive claim. -/
def mass (z : ℝ) : ℝ := ∑' g : ℕ, (count g : ℝ) * z ^ g

lemma genuine_depth_five (d : GenuineFive) : d.val.depth = 5 := by
  apply le_antisymm
  · exact (KunzWord.depth_le_iff _).mpr d.property.1
  · obtain ⟨i, j, hij, hi, hj⟩ := d.property.2
    exact hi ▸ KunzWord.le_depth d.val.2.val i

/-- Inclusion chooses the true two rightmost fives of each genuine word.
The source may have additional fives before the left pivot. -/
lemma genuine_has_raw_pivots (d : GenuineFive) :
    ∃ r p, RawGraph.RawAdmissible r p 5 d.val.2.val :=
  RawGraph.exists_raw_of_kunz_two_maxima (Or.inr rfl) d.val.2.property
    d.property.1 d.property.2

lemma genuine_unique_raw_pivots (d : GenuineFive) :
    ∃! rp : ℕ × ℕ, RawGraph.RawAdmissible rp.1 rp.2 5 d.val.2.val := by
  obtain ⟨r, p, h⟩ := genuine_has_raw_pivots d
  refine ⟨(r, p), h, ?_⟩
  intro rp hrp
  exact Prod.ext (RawGraph.raw_parameters_unique hrp h).1 (RawGraph.raw_parameters_unique hrp h).2

/-- Exact change of variables for the three geometric sums in mass:five. -/
def pivotTriple (m r p : ℕ) : ℕ × ℕ × ℕ := (r - 1, p - r - 1, m - p - 1)

lemma pivotTriple_reconstruct {m r p : ℕ} (h : RawGraph.Parameters m r p 5) :
    r = 1 + (pivotTriple m r p).1 ∧
    p = 2 + (pivotTriple m r p).1 + (pivotTriple m r p).2.1 ∧
    m = 3 + (pivotTriple m r p).1 + (pivotTriple m r p).2.1 + (pivotTriple m r p).2.2 := by
  rcases h with ⟨hr, hrp, hpm, _⟩
  simp only [pivotTriple]
  omega

lemma triple_valid (i j l : ℕ) :
    RawGraph.Parameters (3 + i + j + l) (1 + i) (2 + i + j) 5 := by
  unfold RawGraph.Parameters
  omega

lemma pivotTriple_inverse (i j l : ℕ) :
    pivotTriple (3 + i + j + l) (1 + i) (2 + i + j) = (i, j, l) := by
  unfold pivotTriple
  simp only [Prod.mk.injEq]
  omega

/-- Equality of the genuine genus fiber with the fiber of its actual weight. -/
def sourceWeightFibreEquiv (g : ℕ) :
    {d : GenuineFive // d.val.weight = g} ≃ GenuineFiveAt g where
  toFun d := ⟨⟨d.val.val, d.property⟩, d.val.property⟩
  invFun d := ⟨⟨d.val.val, d.property⟩, d.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance (g : ℕ) : Fintype {d : GenuineFive // d.val.weight = g} :=
  Fintype.ofEquiv (GenuineFiveAt g) (sourceWeightFibreEquiv g).symm

lemma sourceWeightFibre_card (g : ℕ) :
    Fintype.card {d : GenuineFive // d.val.weight = g} = count g :=
  Fintype.card_congr (sourceWeightFibreEquiv g)

lemma sourceWeightFibre_sum (z : ℝ) (g : ℕ) :
    (∑' d : {d : GenuineFive // d.val.weight = g}, z ^ d.val.val.weight) = (count g : ℝ) * z ^ g := by
  simp only [show ∀ d : {d : GenuineFive // d.val.weight = g}, d.val.val.weight = g from fun d => d.property]
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, sourceWeightFibre_card, nsmul_eq_mul]

/-- Source-weight summability implies the actual coefficient series converges,
with exactly the same mass. This prevents a divergent-tsum default from being
used as a convergence argument. -/
lemma mass_eq_source_tsum {z : ℝ} (hs : Summable (fun d : GenuineFive => z ^ d.val.weight)) :
    Summable (fun g => (count g : ℝ) * z ^ g) ∧ mass z = ∑' d : GenuineFive, z ^ d.val.weight := by
  have h := hs.hasSum.tsum_fiberwise (fun d : GenuineFive => d.val.weight)
  have he (g : ℕ) : (∑' d : (fun d : GenuineFive => d.val.weight) ⁻¹' {g}, z ^ d.val.val.weight) =
      (count g : ℝ) * z ^ g := sourceWeightFibre_sum z g
  simp_rw [he] at h
  exact ⟨h.summable, h.tsum_eq⟩

end SubmittedGenus.CapFiveMass
