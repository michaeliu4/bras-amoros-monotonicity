import Results.Genus.FinalAssembly.SubmittedPaperCertificates
import Results.Genus.CapFourMass.SourceMixed
import Results.Genus.CapFourMass.SpectralBlocks
import Results.Genus.GoldenTail.FiniteBound
import Results.Genus.FiniteComparison.RetainedPrefix
import Results.Genus.Injection.Residual
import Results.Genus.FiniteComparison.Acceptance
import Results.Genus.FiniteComparison.GoldenEnvelope

/-! # Coverage corollaries of the submitted certificate interface

Manuscript: Git blob `e04fb276e8ceed829059cf724ead1e18e8bc9e9f`; line numbers
refer to that blob.  The coverage audit (`COVERAGE.md`) found the statements
below proved in Lean only as internal steps, only conditionally, or only in a
different formulation.  Each is stated here with the framework's actual
objects (`SourceClass g .E` for `E_g`, `originalCapacity` for `L(g)`,
`rawFourCount`, `CapFiveMass.count`, `fixedPivotCoeff` for `[z^g]F_{r,p}`, ...).

Theorems that need the finite certificates take the hypothesis
`h : FinalAssembly.SubmittedPaperCertificates`; the native trust is carried by
that hypothesis only (`Native.submitted_certificates` supplies it in
`Native/Coverage.lean`).  Every theorem in this file uses only `propext`,
`Classical.choice` and `Quot.sound`. -/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.Native.Coverage
open OriginalSources OriginalPopulations FiniteArithmetic.Reservoir TailComparison
open FiniteComparison FiniteComparison.SourceBoxes FiniteComparison.AllGenusOmittedSource
open RawGraph RawGraph.SignedCounterexample

/-! ## (a) `mass:residual` -/

/-- **`mass:residual`** (blob e04fb276, lines 2370-2373): for every `g`,
`|E_g| < 2024 z₄^{-g} + 113 z₅^{-g}` with `z₄ = 1247/2000`, `z₅ = 633/1000`.
`E_g` is the exceptional source class `SourceClass g .E`; this is the step `he'`
of `FinalAssembly.exceptional_lt_capacity_from_837`, obtained from
`OriginalPopulations.exceptional_mass_extraction` (`cmb:mass-extraction`) and the
mass values `mass:values`. -/
theorem residual_mass_bound (h : FinalAssembly.SubmittedPaperCertificates) (g : ℕ) :
    (Fintype.card (SourceClass g .E) : ℝ) <
      2024 * z4 ^ (-(g : ℤ)) + 113 * z5 ^ (-(g : ℤ)) := by
  have hm := h.original_sharper_mass
  have hs4 : Summable (fun n => (countFour n : ℝ) * z4 ^ n) := by
    simpa only [z4] using hm.1
  have hm4 : massFour z4 < 2024 := by
    have h2 := hm.2
    rw [show z4 = (1247 : ℝ) / 2000 from rfl]
    linarith
  have he := exceptional_mass_extraction g z4_pos (by norm_num [z4])
    z5_pos (by norm_num [z5]) hs4 CapFiveMass.mass_five.1
  have he' : (Fintype.card (SourceClass g .E) : ℝ) < 2024 / z4 ^ g + 113 / z5 ^ g :=
    he.trans_lt (add_lt_add (div_lt_div_of_pos_right hm4 (pow_pos z4_pos g))
      (div_lt_div_of_pos_right CapFiveMass.mass_five.2 (pow_pos z5_pos g)))
  simpa only [zpow_neg, zpow_natCast, div_eq_mul_inv] using he'

/-! ## (b) `mass:tail` -/

/-- **`mass:tail`** (Proposition, blob e04fb276, lines 2375-2379): for every
source genus `g ≥ 837`, `|E_g| < L(g)`, where `L(g) = originalCapacity g` is the
unused-target capacity of `cmb:capacity`. -/
theorem mass_tail (h : FinalAssembly.SubmittedPaperCertificates) (g : ℕ) (hg : 837 ≤ g) :
    Fintype.card (SourceClass g .E) < originalCapacity g := by
  have hm := h.original_sharper_mass
  apply FinalAssembly.exceptional_lt_capacity_from_837 _ _ g hg
  · simpa only [z4] using hm.1
  · have h2 := hm.2
    rw [show z4 = (1247 : ℝ) / 2000 from rfl]
    linarith

/-! ## (d) `cmp:U`, `cmp:V`: the table-form upper bounds -/

/-- **`cmp:U`** (blob e04fb276, lines 2425-2437), identification of the table:
for `g ≤ 897` the literal Lean table value `upperFour g` is exactly
`U_g = C_g(300) + 1_{g ≥ 604} ⌊221715 F_g / 10^6⌋`, where
`C_g(300) = retainedPrefix g = ∑_{p ≤ 300} ∑_{1 ≤ r < p} [z^g] F_{r,p}` (all
multiplicities). -/
theorem upperFour_eq_source (h : FinalAssembly.SubmittedPaperCertificates)
    (g : ℕ) (hg : g ≤ 897) :
    upperFour g = retainedPrefix g + if 604 ≤ g then 221715 * Nat.fib g / 1000000 else 0 := by
  rw [upperFour, ← h.arrays.capFour g hg, RetainedPrefix.retainedFour_eq_prefix g hg,
    Nat.fastFib_eq]

/-- **`cmp:U`** (blob e04fb276, lines 2425-2437), upper-bound half: `U_g` is an
upper bound for the complete raw depth-four count, for every `g ≤ 897` (the
finite comparison uses `g ≤ 836`). -/
theorem rawFour_le_upperFour (h : FinalAssembly.SubmittedPaperCertificates)
    (g : ℕ) (hg : g ≤ 897) : rawFourCount g ≤ upperFour g := by
  rw [upperFour_eq_source h g hg, ← Nat.fastFib_eq]
  exact GoldenEnvelope.original_integer_envelope g

/-- **`cmp:V`** (blob e04fb276, lines 2441-2450), first line: for `g ≤ 300` the
table value `upperFive g` is the coefficient `C^{(5)}_g` of the complete raw
cap-five two-pivot population, i.e. `box 5 n g` for every box size
`n ≥ g + 2` (by support, no raw cap-five word of genus `g` has multiplicity or
pivot `≥ g + 2`). -/
theorem upperFive_eq_source (h : FinalAssembly.SubmittedPaperCertificates)
    (g : ℕ) (hg : g ≤ 300) (n : ℕ) (hn : g + 2 ≤ n) : upperFive g = box 5 n g := by
  rw [upperFive, if_pos hg, ← h.arrays.capFive g hg]
  apply triple_sum_same
  · exact coefficient_cube_support (by intro m hm; omega)
  · exact coefficient_cube_support (by intro m hm; omega)

/-- Natural division is the floor of real division. -/
lemma nat_div_eq_floor (a b : ℕ) (hb : 0 < b) : a / b = ⌊(a : ℝ) / b⌋₊ := by
  have hbr : (0 : ℝ) < b := by exact_mod_cast hb
  rw [eq_comm, Nat.floor_eq_iff (by positivity)]
  constructor
  · rw [le_div_iff₀ hbr]
    exact_mod_cast Nat.div_mul_le_self a b
  · rw [div_lt_iff₀ hbr]
    have h1 := Nat.div_add_mod a b
    have h2 := Nat.mod_lt a hb
    have h3 : a < (a / b + 1) * b := by nlinarith
    exact_mod_cast h3

/-- **`cmp:V`** (blob e04fb276, lines 2441-2450), second line: for `g ≥ 301`,
`V_g = ⌊113 (1000/633)^g⌋`. Standard axioms; no certificate is needed. -/
theorem upperFive_eq_floor (g : ℕ) (hg : 301 ≤ g) :
    upperFive g = ⌊(113 : ℝ) * (1000 / 633) ^ g⌋₊ := by
  rw [upperFive, if_neg (by omega), div_pow, ← mul_div_assoc]
  have h := nat_div_eq_floor (113 * 1000 ^ g) (633 ^ g) (by positivity)
  push_cast at h
  exact h

/-- **`cmp:V`** (blob e04fb276, lines 2441-2450), upper-bound half: `V_g ≥ B_g`
for every `g`, where `B_g = CapFiveMass.count g` is the genuine multiple-five
population (`def:A-B`). For `g ≤ 300` this uses the cap-five array certificate;
for `g ≥ 301` it is the weighted-mass bound `genuineFive_le_upperFive`. -/
theorem genuineFive_le_upperFive (h : FinalAssembly.SubmittedPaperCertificates)
    (g : ℕ) : CapFiveMass.count g ≤ upperFive g := by
  by_cases hg : g ≤ 300
  · exact h.arrays.sourceCertificates.genuineFiveLow g hg
  · exact FiniteComparison.genuineFive_le_upperFive g (by omega)

/-! ## (c) the finite comparison consequence -/

/-- **`cmp:finite`** consequence used in the proof of `thm:main` (blob e04fb276,
lines 2461-2464 and 2552-2558): for `1 ≤ g ≤ 836`, `|E_g| ≤ L(g)`. This is
`FiniteComparison.actual_finite_capacity` with its three source upper-bound
premises (`cmp:U` at `g` and `g-1`, `cmp:V` at `g`) discharged. -/
theorem finite_capacity (h : FinalAssembly.SubmittedPaperCertificates)
    (g : ℕ) (hg : 1 ≤ g) (hg' : g ≤ 836) :
    Fintype.card (SourceClass g .E) ≤ originalCapacity g :=
  actual_finite_capacity g hg hg' (rawFour_le_upperFour h g (by omega))
    (rawFour_le_upperFour h (g-1) (by omega)) (genuineFive_le_upperFive h g)

/-- Combined form used in the proof of `thm:main` (blob e04fb276, lines
2552-2558): `|E_g| ≤ L(g)` for every `g ≥ 1` (finite comparison for
`g ≤ 836`, `mass:tail` for `g ≥ 837`). -/
theorem exceptional_le_capacity (h : FinalAssembly.SubmittedPaperCertificates)
    (g : ℕ) (hg : 1 ≤ g) : Fintype.card (SourceClass g .E) ≤ originalCapacity g := by
  by_cases hg' : g ≤ 836
  · exact finite_capacity h g hg hg'
  · exact (mass_tail h g (by omega)).le

/-! ## (e) `raw:tail` / `raw:main` in the literal pivot-sum form -/

/-- Fixed-pivot coefficients vanish once the right pivot exceeds the genus
(every multiplicity `m ≤ g` in `fixedPivotCoeff` is then `≤ p`). -/
lemma fixedPivotCoeff_eq_zero_of_genus_lt {r p g : ℕ} (hp : g < p) :
    fixedPivotCoeff r p g = 0 := by
  unfold fixedPivotCoeff
  apply Finset.sum_eq_zero
  intro m hm
  have hm' := Finset.mem_range.mp hm
  have hi : ¬ Parameters m r p 4 := by unfold Parameters; omega
  simp [rawPolynomial_invalid hi]

/-- **`raw:tail`/`raw:main`** (Theorem, blob e04fb276, lines 780-788), every finite
pivot horizon: for all `g` and `N`,
`∑_{300 < p < N} ∑_{r=1}^{p-1} [z^g] F_{r,p} ≤ 0.221715 · F_g`, where
`[z^g] F_{r,p} = fixedPivotCoeff r p g` (sum over all multiplicities) and
`F_g = Nat.fib g`. No certificate is used. -/
theorem raw_tail_partial (g N : ℕ) :
    (∑ p ∈ Finset.Ico 301 N, ∑ r ∈ Finset.Ico 1 p, (fixedPivotCoeff r p g : ℝ)) ≤
      (221715 : ℝ) / 1000000 * Nat.fib g := by
  calc
    _ ≤ ∑ p ∈ Finset.Ico 301 N, ∑ r ∈ Finset.Ico 1 p,
          GoldenTail.coefficientMultiplier r p * (Nat.fib g : ℝ) := by
      apply Finset.sum_le_sum; intro p hp
      apply Finset.sum_le_sum; intro r hr
      have hrr := Finset.mem_Ico.mp hr
      exact GoldenTail.coefficientMultiplier_source_bound g p r hrr.1 hrr.2
    _ = (∑ p ∈ Finset.Ico 301 N, ∑ r ∈ Finset.Ico 1 p,
          GoldenTail.coefficientMultiplier r p) * (Nat.fib g : ℝ) := by
      simp only [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (GoldenTail.omitted_multiplier_sum_le N)
      (Nat.cast_nonneg _)

/-- The omitted pivot row `∑_{r=1}^{p-1} [z^g] F_{r,p}` for `p > 300`, and `0`
for `p ≤ 300`. -/
def omittedPivotRow (g p : ℕ) : ℝ :=
  if 300 < p then ∑ r ∈ Finset.Ico 1 p, (fixedPivotCoeff r p g : ℝ) else 0

lemma omittedPivotRow_eq_zero {g p : ℕ} (hp : g < p) : omittedPivotRow g p = 0 := by
  unfold omittedPivotRow
  split_ifs
  · exact Finset.sum_eq_zero (fun r _ => by rw [fixedPivotCoeff_eq_zero_of_genus_lt hp]; simp)
  · rfl

lemma omittedPivotRow_sum_range (g N : ℕ) :
    (∑ p ∈ Finset.range N, omittedPivotRow g p) =
      ∑ p ∈ Finset.Ico 301 N, ∑ r ∈ Finset.Ico 1 p, (fixedPivotCoeff r p g : ℝ) := by
  unfold omittedPivotRow
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext p
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  · intro p _; rfl

/-- **`raw:tail`/`raw:main`** (Theorem, blob e04fb276, lines 780-788), literal
statement: for every `g ≥ 0` the (finitely supported, hence summable) sum over
all pivots `p > 300` satisfies
`∑_{p>300} ∑_{r=1}^{p-1} [z^g] F_{r,p} ≤ (221715/10^6) F_g`. -/
theorem raw_tail (g : ℕ) :
    Summable (omittedPivotRow g) ∧
      (∑' p, omittedPivotRow g p) ≤ (221715 : ℝ) / 1000000 * Nat.fib g := by
  have hz : ∀ p ∉ Finset.range (g+1), omittedPivotRow g p = 0 := by
    intro p hp
    exact omittedPivotRow_eq_zero (by simpa using hp)
  refine ⟨summable_of_ne_finset_zero hz, ?_⟩
  rw [tsum_eq_sum hz, omittedPivotRow_sum_range]
  exact raw_tail_partial g (g+1)

/-- **`raw:tail`** (blob e04fb276, lines 786-787): the left side vanishes for
`g < 604`. -/
theorem raw_tail_zero (g : ℕ) (hg : g < 604) : (∑' p, omittedPivotRow g p) = 0 := by
  have hrow : ∀ p, omittedPivotRow g p = 0 := by
    intro p
    unfold omittedPivotRow
    split_ifs with hp
    · apply Finset.sum_eq_zero; intro r _
      have h0 : fixedPivotCoeff r p g = 0 := by
        unfold fixedPivotCoeff
        exact Finset.sum_eq_zero (fun m _ => omitted_pivot_coeff_zero hp hg)
      simp [h0]
    · rfl
  simp [hrow]

/-! ## (f) `mass:spectral-majorization` -/

/-- **`mass:spectral-majorization`** (blob e04fb276, lines 1888-1891), second
chain: for `m > 2p` (here `m = r + N`, `p = r + d`, so `m > 2p ↔ r + 2d < N`),
`0 ≤ Z_{m,r,p} ≤ P_{m,r,p} + M_{m,r,p} = A^{abs}_{m,r,p}` at `z₄ = 1247/2000`,
with `Z` the actual raw cap-four polynomial value, `P = sourcePure`,
`M = sourceMixed` (all assignments with a negative mode) and
`A^{abs} = sourceAbsolute` (`mass:mode-definitions`). -/
theorem raw_le_sourceAbsolute {r N d : ℕ} (hr : 0 < r) (hd : 0 < d) (hN : d < N)
    (hbig : r + 2 * d < N) :
    0 ≤ Polynomial.eval₂ (Nat.castRingHom ℝ) CapFourMass.radius
        (rawPolynomial (r+N) r (r+d) 4) ∧
      Polynomial.eval₂ (Nat.castRingHom ℝ) CapFourMass.radius
          (rawPolynomial (r+N) r (r+d) 4) ≤
        CapFourMass.sourcePure r N d hN + CapFourMass.sourceMixed r N d hN ∧
      CapFourMass.sourcePure r N d hN + CapFourMass.sourceMixed r N d hN =
        CapFourMass.sourceAbsolute r N d hN := by
  refine ⟨?_, CapFourMass.rawPolynomial_le_source_pure_mixed hr hd hN hbig,
    (CapFourMass.sourceAbsolute_eq_pure_add_mixed r N d hN).symm⟩
  rw [Polynomial.eval₂_eq_sum_range]
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (Nat.cast_nonneg _)
    (pow_nonneg CapFourMass.radius_pos.le _))

/-- The first chain of `mass:spectral-majorization` together with the second:
`0 ≤ P ≤ A^{abs}` and `Z ≤ A^{abs}` (blob e04fb276, lines 1888-1891). -/
theorem spectral_majorization {r N d : ℕ} (hr : 0 < r) (hd : 0 < d) (hN : d < N)
    (hbig : r + 2 * d < N) :
    0 ≤ CapFourMass.sourcePure r N d hN ∧
      CapFourMass.sourcePure r N d hN ≤ CapFourMass.sourceAbsolute r N d hN ∧
      Polynomial.eval₂ (Nat.castRingHom ℝ) CapFourMass.radius
          (rawPolynomial (r+N) r (r+d) 4) ≤ CapFourMass.sourceAbsolute r N d hN := by
  have h := raw_le_sourceAbsolute hr hd hN hbig
  exact ⟨CapFourMass.sourcePure_nonneg r N d hN, CapFourMass.sourcePure_le_absolute r N d hN,
    h.2.2 ▸ h.2.1⟩

/-! ## (g) The `(5,4,2,1)` example and the `n ≥ 1` remark -/

/-- The Kunz word `(5,4,2,1)` of multiplicity `5`. -/
def exampleChild : KunzWord 5 := ![5,4,2,1]

/-- The Kunz word `(4,4,2,1)` of multiplicity `5`. -/
def exampleParent : KunzWord 5 := ![4,4,2,1]

lemma exampleChild_valid : KunzWord.Valid exampleChild where
  positive := by decide
  noncarry := by
    intro i j hi hi' hj hj' hij
    interval_cases i <;> interval_cases j <;> first | omega | decide
  carry := by
    intro i j hi hi' hj hj' hij
    interval_cases i <;> interval_cases j <;> first | omega | decide

lemma exampleParent_valid : KunzWord.Valid exampleParent where
  positive := by decide
  noncarry := by
    intro i j hi hi' hj hj' hij
    interval_cases i <;> interval_cases j <;> first | omega | decide
  carry := by
    intro i j hi hi' hj hj' hij
    interval_cases i <;> interval_cases j <;> first | omega | decide

/-- `(5,4,2,1)` as Kunz data (multiplicity `5`). -/
def childData : KunzData := ⟨⟨5, by norm_num⟩, ⟨exampleChild, exampleChild_valid⟩⟩

/-- `(4,4,2,1)` as Kunz data (multiplicity `5`). -/
def parentData : KunzData := ⟨⟨5, by norm_num⟩, ⟨exampleParent, exampleParent_valid⟩⟩

lemma mem_child (n : ℕ) : n ∈ childData.toSemigroup ↔
    n % 5 = 0 ∨ (n % 5 = 1 ∧ 5 ≤ n / 5) ∨ (n % 5 = 2 ∧ 4 ≤ n / 5) ∨
      (n % 5 = 3 ∧ 2 ≤ n / 5) ∨ (n % 5 = 4 ∧ 1 ≤ n / 5) := by
  change KunzWord.coord exampleChild (n % 5) ≤ n / 5 ↔ _
  have hr : n % 5 < 5 := Nat.mod_lt _ (by norm_num)
  interval_cases h : n % 5
  · simp
  · rw [show KunzWord.coord exampleChild 1 = 5 by decide]; omega
  · rw [show KunzWord.coord exampleChild 2 = 4 by decide]; omega
  · rw [show KunzWord.coord exampleChild 3 = 2 by decide]; omega
  · rw [show KunzWord.coord exampleChild 4 = 1 by decide]; omega

lemma mem_parent (n : ℕ) : n ∈ parentData.toSemigroup ↔
    n % 5 = 0 ∨ (n % 5 = 1 ∧ 4 ≤ n / 5) ∨ (n % 5 = 2 ∧ 4 ≤ n / 5) ∨
      (n % 5 = 3 ∧ 2 ≤ n / 5) ∨ (n % 5 = 4 ∧ 1 ≤ n / 5) := by
  change KunzWord.coord exampleParent (n % 5) ≤ n / 5 ↔ _
  have hr : n % 5 < 5 := Nat.mod_lt _ (by norm_num)
  interval_cases h : n % 5
  · simp
  · rw [show KunzWord.coord exampleParent 1 = 4 by decide]; omega
  · rw [show KunzWord.coord exampleParent 2 = 4 by decide]; omega
  · rw [show KunzWord.coord exampleParent 3 = 2 by decide]; omega
  · rw [show KunzWord.coord exampleParent 4 = 1 by decide]; omega

/-- The semigroup of `(5,4,2,1)` is a leaf: it has no effective generator. -/
theorem childData_isLeaf : childData.toSemigroup.IsLeaf := by
  rintro a ⟨⟨ha, ha0, hmin⟩, hgap⟩
  have h21 : 21 < a := hgap 21 (by rw [mem_child]; omega)
  rw [mem_child] at ha
  by_cases h22 : a = 22
  · have := hmin 9 13 (by rw [mem_child]; omega) (by rw [mem_child]; omega) (by omega)
    omega
  by_cases h26 : a = 26
  · have := hmin 13 13 (by rw [mem_child]; omega) (by rw [mem_child]; omega) (by omega)
    omega
  · have := hmin 5 (a - 5) (by rw [mem_child]; omega) (by rw [mem_child]; omega) (by omega)
    omega

/-- `21` is an effective generator of the semigroup of `(4,4,2,1)`. -/
theorem parentData_effective_21 : parentData.toSemigroup.IsEffectiveGenerator 21 := by
  refine ⟨⟨by rw [mem_parent]; omega, by norm_num, ?_⟩, ?_⟩
  · intro b c hb hc hbc
    rw [mem_parent] at hb hc
    omega
  · intro n hn
    rw [mem_parent] at hn
    omega

/-- **Example after `cmb:Eupper`** (blob e04fb276, lines 720-723): `(5,4,2,1)` is a
leaf with ordinary parent `(4,4,2,1)`, whose sole `1` is final (the `B`-test
predicate `finalOneFour`); the parent has effective generator `21`, and deleting
it gives `(5,4,2,1)`.  In addition `(5,4,2,1)` (weight `12`) lies in the
exceptional class `E_12` (`sector = .E`, unique-five sector of `cmb:residual`). -/
theorem example_5421 :
    childData.toSemigroup.IsLeaf ∧
      parentData.toSemigroup.IsEffectiveGenerator 21 ∧
      (∀ n, n ∈ childData.toSemigroup ↔ n ∈ parentData.toSemigroup ∧ n ≠ 21) ∧
      parentData.toSemigroup.IsOrdinaryChild childData.toSemigroup ∧
      OriginalSources.finalOneFour parentData ∧
      childData.weight = 12 ∧ OriginalSources.sector childData = .E := by
  have hdel : ∀ n, n ∈ childData.toSemigroup ↔ n ∈ parentData.toSemigroup ∧ n ≠ 21 := by
    intro n
    rw [mem_child, mem_parent]
    omega
  refine ⟨childData_isLeaf, parentData_effective_21, hdel, ⟨21, parentData_effective_21, hdel⟩,
    ⟨by decide, by decide, by decide⟩, by decide, ?_⟩
  rw [OriginalSources.exceptional_iff_three_sectors]
  refine ⟨childData_isLeaf, ⟨(3 : Fin 4), rfl⟩,
    Or.inr (Or.inl ⟨by decide, ⟨(0 : Fin 4), rfl, by decide⟩, ⟨(1 : Fin 4), rfl⟩⟩)⟩

/-- **Remark after `mass:actual-block`** (blob e04fb276, lines 1987-1991):
`ν₂/R² > 3/25 > (u vᵀ)₂₂`, where `ν₂ = q₋ᵀ D² q₋` for the actual strong transfer
`D = strongMatrix` at `z₄`, `R = strongBound = 23389/25000` and `u, v` are
`modeU`, `modeV` (`mass:constants`); consequently the block bound fails at
`n = 0` (bare strong run), so the hypothesis `n ≥ 1` is essential. -/
theorem remark_bare_strong_run :
    (3 : ℝ) / 25 < (CapFourMass.qminus ⬝ᵥ
        ((CapFourMass.strongMatrix ^ 2) *ᵥ CapFourMass.qminus)) / CapFourMass.strongBound ^ 2 ∧
      CapFourMass.modeU 1 * CapFourMass.modeV 1 < 3 / 25 ∧
      ¬ (|CapFourMass.coupledBlock (CapFourMass.strongMatrix ^ 2) 0 1 1| ≤
          CapFourMass.strongBound ^ 2 * CapFourMass.lam ^ 0 *
            CapFourMass.modeU 1 * CapFourMass.modeV 1) := by
  have hR : (0 : ℝ) < CapFourMass.strongBound ^ 2 := by
    norm_num [CapFourMass.strongBound]
  have hnu : (3 : ℝ) / 25 < (CapFourMass.qminus ⬝ᵥ
      ((CapFourMass.strongMatrix ^ 2) *ᵥ CapFourMass.qminus)) / CapFourMass.strongBound ^ 2 := by
    rw [lt_div_iff₀ hR, CapFourMass.minus_moment_eq, lt_div_iff₀ CapFourMass.minusNorm_pos,
      CapFourMass.nu_two_polynomial, CapFourMass.minusNorm_eq]
    have hq := CapFourMass.lam_quadratic
    have hlo := CapFourMass.lam_bounds.1
    have hhi := CapFourMass.lam_bounds.2
    norm_num [CapFourMass.carryA, CapFourMass.carryB, CapFourMass.radius,
      CapFourMass.strongBound] at hq ⊢
    nlinarith
  have huv : CapFourMass.modeU 1 * CapFourMass.modeV 1 < 3 / 25 := by
    norm_num [CapFourMass.modeU, CapFourMass.modeV]
  refine ⟨hnu, huv, ?_⟩
  intro hb
  rw [CapFourMass.coupledBlock_entry] at hb
  have hv : CapFourMass.modeVector 1 = CapFourMass.qminus := rfl
  simp only [hv, pow_zero, mul_one] at hb
  have h1 := (le_abs_self _).trans hb
  have h2 := (lt_div_iff₀ hR).mp hnu
  nlinarith

end SubmittedGenus.Native.Coverage

namespace SubmittedGenus.Native.Coverage
#print axioms residual_mass_bound
#print axioms mass_tail
#print axioms upperFour_eq_source
#print axioms rawFour_le_upperFour
#print axioms upperFive_eq_source
#print axioms upperFive_eq_floor
#print axioms genuineFive_le_upperFive
#print axioms finite_capacity
#print axioms exceptional_le_capacity
#print axioms raw_tail_partial
#print axioms raw_tail
#print axioms raw_tail_zero
#print axioms raw_le_sourceAbsolute
#print axioms spectral_majorization
#print axioms example_5421
#print axioms remark_bare_strong_run
end SubmittedGenus.Native.Coverage

/-! Literal forms noted by the independent review (INDEPENDENT-REVIEW.md, points 1–2). -/
namespace SubmittedGenus.Native.Coverage

/-- `cmp:finite` (lines 2461–2464 of blob e04fb276), literal form: for 1 ≤ g ≤ 836,
0 ≤ E⁺_g ≤ L(g), with E⁺_g the signed integer residual of the tables. -/
theorem cmp_finite_literal (g : ℕ) (hg : 1 ≤ g) (hg' : g ≤ 836) :
    0 ≤ SubmittedGenus.FiniteComparison.residualUpper g (SubmittedGenus.FiniteComparison.upperFour g)
        (SubmittedGenus.FiniteComparison.upperFour (g-1)) (SubmittedGenus.FiniteComparison.upperFive g) ∧
    SubmittedGenus.FiniteComparison.residualUpper g (SubmittedGenus.FiniteComparison.upperFour g)
        (SubmittedGenus.FiniteComparison.upperFour (g-1)) (SubmittedGenus.FiniteComparison.upperFive g) ≤
      (SubmittedGenus.FiniteArithmetic.Reservoir.originalCapacity g : ℤ) :=
  SubmittedGenus.FiniteComparison.original_integer_comparisons g hg hg'

/-- `cmp:U` upper-bound half for every g (lines 2425–2437): the complete raw depth-four
count is at most C_g(300) + 1_{g≥604}⌊221715·F_g/10^6⌋. -/
theorem rawFour_envelope_all (g : ℕ) : SubmittedGenus.OriginalPopulations.rawFourCount g ≤
    SubmittedGenus.FiniteComparison.AllGenusOmittedSource.retainedPrefix g +
      if 604 ≤ g then 221715 * Nat.fastFib g / 1000000 else 0 :=
  SubmittedGenus.FiniteComparison.GoldenEnvelope.original_integer_envelope g

#print axioms cmp_finite_literal
#print axioms rawFour_envelope_all
end SubmittedGenus.Native.Coverage
