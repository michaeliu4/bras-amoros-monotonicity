import Results.Genus.CapFiveMass.Source
import Results.Genus.CapFiveMass.Geometric

/-!
# Exact genuine-source inclusion in the indexed finite raw partitions

The source embedding selects the unique actual two-rightmost fives. The
positive-Kunz validity is imposed before this inclusion, not replaced by
raw admissibility. This module separates the proved source/counting bridge
from the remaining analytic per-partition inequality.
-/

noncomputable section
open scoped BigOperators
namespace SubmittedGenus.CapFiveMass

structure PivotParameters where
  m : ℕ
  r : ℕ
  p : ℕ
  valid : RawGraph.Parameters m r p 5

@[ext] lemma PivotParameters.ext {a b : PivotParameters}
    (hm : a.m = b.m) (hr : a.r = b.r) (hp : a.p = b.p) : a = b := by
  cases a
  cases b
  simp_all

/-- A bijection of actual ordered multiplicity/pivot triples with N^3. -/
def parameterEquiv : PivotParameters ≃ ℕ × ℕ × ℕ where
  toFun q := pivotTriple q.m q.r q.p
  invFun q := ⟨3 + q.1 + q.2.1 + q.2.2, 1 + q.1, 2 + q.1 + q.2.1,
    triple_valid q.1 q.2.1 q.2.2⟩
  left_inv q := by
    have h := pivotTriple_reconstruct q.valid
    exact PivotParameters.ext h.2.2.symm h.1.symm h.2.1.symm
  right_inv q := pivotTriple_inverse q.1 q.2.1 q.2.2

abbrev RawFiveWord (q : PivotParameters) :=
  {x : RawGraph.Word q.m // RawGraph.RawAdmissible q.r q.p 5 x}

noncomputable instance (q : PivotParameters) : Fintype (RawFiveWord q) := by
  classical
  exact Fintype.ofEquiv
    {x : Fin (q.m - 1) → Fin 6 // RawGraph.RawAdmissible q.r q.p 5 (RawGraph.boundedWord x)}
    (RawGraph.boundedSourceEquiv q.m q.r q.p 5)

abbrev RawFivePopulation := Σ q : PivotParameters, RawFiveWord q

def rawWeight (d : RawFivePopulation) : ℕ := RawGraph.genus d.2.val

def rawPartition (q : PivotParameters) (z : ℝ) : ℝ :=
  ∑ x : RawFiveWord q, z ^ RawGraph.genus x.val

/-- These are canonical actual pivots by the proved uniqueness theorem. -/
def genuineParameters (d : GenuineFive) : PivotParameters :=
  let r := Classical.choose (genuine_has_raw_pivots d)
  let p := Classical.choose (Classical.choose_spec (genuine_has_raw_pivots d))
  let h := Classical.choose_spec (Classical.choose_spec (genuine_has_raw_pivots d))
  ⟨d.val.1.val, r, p, h.1⟩

lemma genuineParameters_raw (d : GenuineFive) :
    RawGraph.RawAdmissible (genuineParameters d).r (genuineParameters d).p 5 d.val.2.val :=
  Classical.choose_spec (Classical.choose_spec (genuine_has_raw_pivots d))

def sourceIntoRaw (d : GenuineFive) : RawFivePopulation :=
  ⟨genuineParameters d, ⟨d.val.2.val, genuineParameters_raw d⟩⟩

lemma sourceIntoRaw_weight (d : GenuineFive) : rawWeight (sourceIntoRaw d) = d.val.weight := rfl

/-- Forgetting the pivot labels does not merge distinct source data. -/
lemma sourceIntoRaw_injective : Function.Injective sourceIntoRaw := by
  intro d e h
  have hm : d.val.1.val = e.val.1.val := congrArg (fun q : RawFivePopulation => q.1.m) h
  rcases d with ⟨⟨⟨m, hmpos⟩, ⟨x, hx⟩⟩, hd⟩
  rcases e with ⟨⟨⟨n, hnpos⟩, ⟨y, hy⟩⟩, he⟩
  dsimp at hm
  subst n
  have hf := congrArg (fun q : RawFivePopulation =>
    (⟨q.1.m, q.2.val⟩ : Σ m : ℕ, RawGraph.Word m)) h
  change (⟨m, x⟩ : Σ m : ℕ, RawGraph.Word m) = ⟨m, y⟩ at hf
  have hword : x = y := eq_of_heq (Sigma.mk.inj_iff.mp hf).2

  subst y
  rfl

lemma rawPartition_nonneg {z : ℝ} (hz : 0 ≤ z) (q : PivotParameters) : 0 ≤ rawPartition q z :=
  Finset.sum_nonneg fun _ _ => pow_nonneg hz _

/-- Summability of all finite raw partitions lifts to summability of their
actual assignments. No default value of a divergent infinite sum is used. -/
lemma rawPopulation_summable {z : ℝ} (hz : 0 ≤ z)
    (hs : Summable (fun q => rawPartition q z)) :
    Summable (fun d : RawFivePopulation => z ^ rawWeight d) := by
  apply (summable_sigma_of_nonneg (fun d : RawFivePopulation => pow_nonneg hz (rawWeight d))).mpr
  refine ⟨fun _ => (hasSum_fintype _).summable, ?_⟩
  simpa only [rawWeight, tsum_fintype, rawPartition] using hs

/-- Canonical genuine-source inclusion plus exact finite-fiber summation. -/
lemma genuine_mass_le_raw {z : ℝ} (hz : 0 ≤ z)
    (hs : Summable (fun q => rawPartition q z)) :
    Summable (fun g => (count g : ℝ) * z ^ g) ∧ mass z ≤ ∑' q, rawPartition q z := by
  have hr := rawPopulation_summable hz hs
  have hg : Summable (fun d : GenuineFive => z ^ d.val.weight) := by
    simpa only [Function.comp_def, sourceIntoRaw_weight] using hr.comp_injective sourceIntoRaw_injective
  have he := mass_eq_source_tsum hg
  refine ⟨he.1, ?_⟩
  rw [he.2]
  calc
    (∑' d : GenuineFive, z ^ d.val.weight) ≤ ∑' d : RawFivePopulation, z ^ rawWeight d :=
      Summable.tsum_le_tsum_of_inj sourceIntoRaw sourceIntoRaw_injective
        (fun _ _ => pow_nonneg hz _) (fun d => by rw [sourceIntoRaw_weight]) hg hr
    _ = ∑' q, rawPartition q z := by
      rw [hr.tsum_sigma]
      simp only [rawWeight, tsum_fintype, rawPartition]

/-- Analytic composition interface. The hypothesis is the still-substantive
source-specific graph estimate, not a freely assumed numerical constant. -/
lemma mass_lt_113_of_partition_bounds
    (hpart : ∀ q : PivotParameters, rawPartition q radius ≤ geometricTerm (parameterEquiv q)) :
    Summable (fun g => (count g : ℝ) * radius ^ g) ∧ mass radius < 113 := by
  have hsgeo : Summable (fun q : PivotParameters => geometricTerm (parameterEquiv q)) :=
    parameterEquiv.summable_iff.mpr geometric_summable
  have hsraw : Summable (fun q : PivotParameters => rawPartition q radius) :=
    hsgeo.of_nonneg_of_le (rawPartition_nonneg radius_bounds.1.le) hpart
  have hg := genuine_mass_le_raw radius_bounds.1.le hsraw
  refine ⟨hg.1, hg.2.trans_lt ?_⟩
  have hle := hsraw.tsum_le_tsum hpart hsgeo
  rw [parameterEquiv.tsum_eq] at hle
  exact hle.trans_lt geometric_tsum_lt_113

/-- Evaluation of the original finite raw polynomial equals the sum of its
actual raw assignments. This connects LayoutCompiler to the mass partition. -/
lemma rawPartition_eq_eval (q : PivotParameters) (z : ℝ) :
    rawPartition q z = (RawGraph.rawPolynomial q.m q.r q.p 5).eval₂ (Nat.castRingHom ℝ) z := by
  classical
  let P (x : Fin (q.m - 1) → Fin 6) := RawGraph.RawAdmissible q.r q.p 5 (RawGraph.boundedWord x)
  calc
    rawPartition q z = ∑ x : {x : Fin (q.m - 1) → Fin 6 // P x},
        z ^ RawGraph.genus (RawGraph.boundedWord x.val) :=
      ((RawGraph.boundedSourceEquiv q.m q.r q.p 5).sum_comp
        (fun x : RawFiveWord q => z ^ RawGraph.genus x.val)).symm
    _ = ∑ x : Fin (q.m - 1) → Fin 6, if P x then z ^ RawGraph.genus (RawGraph.boundedWord x) else 0 := by
      change (∑ x : {x : Fin (q.m - 1) → Fin 6 // P x},
        (fun x => z ^ RawGraph.genus (RawGraph.boundedWord x)) x.val) = _
      rw [← Finset.sum_subtype (Finset.univ.filter P) (by simp)
        (fun x => z ^ RawGraph.genus (RawGraph.boundedWord x))]
      rw [Finset.sum_filter]
    _ = _ := by
      unfold RawGraph.rawPolynomial
      rw [Polynomial.eval₂_finsetSum]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : P x
      · simp only [P] at hx
        simp [hx, P]
      · simp only [P] at hx
        simp [hx, P]

end SubmittedGenus.CapFiveMass
