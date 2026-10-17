import Results.Genus.Injection.Compensation
import Results.Genus.CapFourMass.ActualContraction

/-! Genuine cap-four sources with validity retained before contraction. -/
noncomputable section
open scoped BigOperators
namespace SubmittedGenus.CapFourMass.GenuineSource
open OriginalPopulations

lemma genuine_has_raw_pivots (d : GenuineFour) :
    ∃ r p, RawGraph.RawAdmissible r p 4 d.val.2.val :=
  RawGraph.exists_raw_of_kunz_two_maxima (Or.inl rfl) d.val.2.property
    d.property.1 d.property.2

structure PivotParameters where
  m : ℕ
  r : ℕ
  p : ℕ
  valid : RawGraph.Parameters m r p 4

@[ext] lemma PivotParameters.ext {a b : PivotParameters}
    (hm : a.m = b.m) (hr : a.r = b.r) (hp : a.p = b.p) : a = b := by
  cases a
  cases b
  simp_all

abbrev ValidFourWord (q : PivotParameters) :=
  {x : RawGraph.Word q.m // RawGraph.RawAdmissible q.r q.p 4 x ∧ KunzWord.Valid x}

def boundedValidEquiv (q : PivotParameters) :
    {x : Fin (q.m-1) → Fin 5 // RawGraph.RawAdmissible q.r q.p 4 (RawGraph.boundedWord x) ∧
      KunzWord.Valid (RawGraph.boundedWord x)} ≃ ValidFourWord q where
  toFun x := ⟨RawGraph.boundedWord x.val, x.property⟩
  invFun x := ⟨fun i => ⟨x.val i, Nat.lt_succ_of_le (RawGraph.raw_coordinate_bounds x.property.1 i).2⟩,
    x.property⟩
  left_inv x := by apply Subtype.ext; funext i; apply Fin.ext; rfl
  right_inv x := by apply Subtype.ext; rfl

noncomputable instance (q : PivotParameters) : Fintype (ValidFourWord q) := by
  classical
  exact Fintype.ofEquiv _ (boundedValidEquiv q)

abbrev ValidFourPopulation := Σ q : PivotParameters, ValidFourWord q

def rawWeight (d : ValidFourPopulation) : ℕ := RawGraph.genus d.2.val

def rawPartition (q : PivotParameters) (z : ℝ) : ℝ :=
  ∑ x : ValidFourWord q, z ^ RawGraph.genus x.val

/-- These are canonical actual pivots by the proved uniqueness theorem. -/
def genuineParameters (d : GenuineFour) : PivotParameters :=
  let r := Classical.choose (genuine_has_raw_pivots d)
  let p := Classical.choose (Classical.choose_spec (genuine_has_raw_pivots d))
  let h := Classical.choose_spec (Classical.choose_spec (genuine_has_raw_pivots d))
  ⟨d.val.1.val, r, p, h.1⟩

lemma genuineParameters_raw (d : GenuineFour) :
    RawGraph.RawAdmissible (genuineParameters d).r (genuineParameters d).p 4 d.val.2.val :=
  Classical.choose_spec (Classical.choose_spec (genuine_has_raw_pivots d))

def sourceIntoRaw (d : GenuineFour) : ValidFourPopulation :=
  ⟨genuineParameters d, ⟨d.val.2.val, genuineParameters_raw d, d.val.2.property⟩⟩

lemma sourceIntoRaw_weight (d : GenuineFour) : rawWeight (sourceIntoRaw d) = d.val.weight := rfl

/-- Forgetting the pivot labels does not merge distinct source data. -/
lemma sourceIntoRaw_injective : Function.Injective sourceIntoRaw := by
  intro d e h
  have hm : d.val.1.val = e.val.1.val := congrArg (fun q : ValidFourPopulation => q.1.m) h
  rcases d with ⟨⟨⟨m, hmpos⟩, ⟨x, hx⟩⟩, hd⟩
  rcases e with ⟨⟨⟨n, hnpos⟩, ⟨y, hy⟩⟩, he⟩
  dsimp at hm
  subst n
  have hf := congrArg (fun q : ValidFourPopulation =>
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
    Summable (fun d : ValidFourPopulation => z ^ rawWeight d) := by
  apply (summable_sigma_of_nonneg (fun d : ValidFourPopulation => pow_nonneg hz (rawWeight d))).mpr
  refine ⟨fun _ => (hasSum_fintype _).summable, ?_⟩
  simpa only [rawWeight, tsum_fintype, rawPartition] using hs

/-- Canonical genuine-source inclusion plus exact finite-fiber summation. -/
lemma genuine_mass_le_raw {z : ℝ} (hz : 0 ≤ z)
    (hs : Summable (fun q => rawPartition q z)) :
    Summable (fun g => (countFour g : ℝ) * z ^ g) ∧ massFour z ≤ ∑' q, rawPartition q z := by
  have hr := rawPopulation_summable hz hs
  have hg : Summable (fun d : GenuineFour => z ^ d.val.weight) := by
    simpa only [Function.comp_def, sourceIntoRaw_weight] using hr.comp_injective sourceIntoRaw_injective
  have he := massFour_eq_source_tsum hg
  have hcount := hg.hasSum.tsum_fiberwise (fun d : GenuineFour => d.val.weight)
  have hsum (g : ℕ) : (∑' d : (fun d : GenuineFour => d.val.weight) ⁻¹' {g},
      z ^ d.val.val.weight) = (countFour g : ℝ) * z ^ g := fourWeightFibre_sum z g
  simp_rw [hsum] at hcount
  refine ⟨hcount.summable, ?_⟩
  rw [he]
  calc
    (∑' d : GenuineFour, z ^ d.val.weight) ≤ ∑' d : ValidFourPopulation, z ^ rawWeight d :=
      Summable.tsum_le_tsum_of_inj sourceIntoRaw sourceIntoRaw_injective
        (fun _ _ => pow_nonneg hz _) (fun d => by rw [sourceIntoRaw_weight]) hg hr
    _ = ∑' q, rawPartition q z := by
      rw [hr.tsum_sigma]
      simp only [rawWeight, tsum_fintype, rawPartition]


end SubmittedGenus.CapFourMass.GenuineSource
