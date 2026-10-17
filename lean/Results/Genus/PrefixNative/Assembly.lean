import Results.Genus.CapFourMass.IndexedModePrefixChunks
import Results.Genus.CapFourMass.IntervalBounds
import Results.Genus.CapFourMass.IntervalPrefixRows

/-! Final assembly of the three prefix obligations from chunk theorems.

A chunk list `[(e₁,B₁),(e₂,B₂),…]` starting at pivot `a` asserts that `Bᵢ` encloses
the source sum over `[eᵢ₋₁, eᵢ)`.  The aggregate box is the exact (rounding-free) sum
of the chunk boxes.  The unit comparison against the submitted numerators is a plain
integer inequality, discharged by `decide +kernel`. -/
open scoped BigOperators
namespace SubmittedGenus.CapFourMass.Interval.PrefixNative.Assembly
open IndexedModePrefix

def ChunksOK (source : ℕ → ℝ) : ℕ → List (ℕ × Box) → Prop
  | _, [] => True
  | a, (e,b)::rest => a ≤ e ∧ Contains b (∑ p ∈ Finset.Ico a e, source p) ∧ ChunksOK source e rest

def lastEnd : ℕ → List (ℕ × Box) → ℕ
  | a, [] => a
  | _, (e,_)::rest => lastEnd e rest

def lastEnd' : ℕ → List (ℕ × ℤ) → ℕ
  | a, [] => a
  | _, (e,_)::rest => lastEnd' e rest

def totalBox : List (ℕ × Box) → Box
  | [] => point 0
  | (_,b)::rest => add b (totalBox rest)

theorem chunks_contains (source : ℕ → ℝ) : ∀ (l : List (ℕ × Box)) (a : ℕ),
    ChunksOK source a l → a ≤ lastEnd a l ∧
      Contains (totalBox l) (∑ p ∈ Finset.Ico a (lastEnd a l), source p) := by
  intro l
  induction l with
  | nil =>
    intro a _
    refine ⟨le_refl a, ?_⟩
    simpa [lastEnd, totalBox] using point_contains 0
  | cons x rest ih =>
    obtain ⟨e, b⟩ := x
    intro a h
    obtain ⟨hae, hb, hrest⟩ := h
    obtain ⟨hel, hc⟩ := ih e hrest
    refine ⟨hae.trans hel, ?_⟩
    have hsum := Finset.sum_Ico_consecutive source hae hel
    simp only [lastEnd, totalBox]
    rw [← hsum]
    exact add_contains hb hc

theorem prefix_of_chunks (source : ℕ → ℝ) {P : ℕ} {l : List (ℕ × Box)}
    (h : ChunksOK source 0 l) (hl : lastEnd 0 l = P+1) :
    Contains (totalBox l) (∑ p ∈ Finset.range (P+1), source p) := by
  have := (chunks_contains source l 0 h).2
  rw [hl] at this
  simpa only [Finset.range_eq_Ico] using this

/-- Generic form: the chunk boxes give `prefix ≤ n / 2^56` for any `n` with `hi · 2^56 ≤ n · unit`. -/
theorem short_prefix_le {l : List (ℕ × Box)} {P : ℕ} (h : ChunksOK originalShortRow 0 l)
    (hl : lastEnd 0 l = P+1) {n : ℤ}
    (hhi : (totalBox l).hi * 72057594037927936 ≤ n * unit) :
    originalShortPrefix P ≤ (n:ℝ) / 72057594037927936 := by
  have hc : Contains (totalBox l) (originalShortPrefix P) := by
    have := prefix_of_chunks originalShortRow h hl
    simpa only [originalShortPrefix, originalShortRow] using this
  exact upper_of_contains hc (by decide : (0:ℤ) < 72057594037927936) hhi

theorem pure_prefix_le {l : List (ℕ × Box)} {P : ℕ} (h : ChunksOK pureSourceRow 0 l)
    (hl : lastEnd 0 l = P+1) {n : ℤ}
    (hhi : (totalBox l).hi * 72057594037927936 ≤ n * unit) :
    originalPurePrefix P ≤ (n:ℝ) / 72057594037927936 :=
  upper_of_contains (prefix_of_chunks pureSourceRow h hl)
    (by decide : (0:ℤ) < 72057594037927936) hhi

theorem mixed_prefix_le {l : List (ℕ × Box)} {P : ℕ} (h : ChunksOK mixedSourceRow 0 l)
    (hl : lastEnd 0 l = P+1) {n : ℤ}
    (hhi : (totalBox l).hi * 72057594037927936 ≤ n * unit) :
    originalMixedPrefix P ≤ (n:ℝ) / 72057594037927936 :=
  upper_of_contains (prefix_of_chunks mixedSourceRow h hl)
    (by decide : (0:ℤ) < 72057594037927936) hhi

/-- Boolean comparison of a box against a numerator N / 2^56. -/
def leCheck (N : ℤ) (b : Box) : Bool := decide (b.hi * 72057594037927936 ≤ N * unit)

theorem le_of_contains_leCheck {b : Box} {x : ℝ} {N : ℤ} (hb : Contains b x)
    (h : leCheck N b = true) : x ≤ (N:ℝ) / 72057594037927936 :=
  upper_of_contains hb (by decide : (0:ℤ) < 72057594037927936) (of_decide_eq_true h)

/-- Upper-bound chunks: `(e, N)` asserts that the source sum over `[a, e)` is at most `N / 2^56`. -/
def ChunksLE (source : ℕ → ℝ) : ℕ → List (ℕ × ℤ) → Prop
  | _, [] => True
  | a, (e,N)::rest => a ≤ e ∧ (∑ p ∈ Finset.Ico a e, source p) ≤ (N:ℝ) / 72057594037927936 ∧
      ChunksLE source e rest

def totalN : List (ℕ × ℤ) → ℤ
  | [] => 0
  | (_,N)::rest => N + totalN rest

theorem chunksLE_bound (source : ℕ → ℝ) : ∀ (l : List (ℕ × ℤ)) (a : ℕ),
    ChunksLE source a l → a ≤ lastEnd' a l ∧
      (∑ p ∈ Finset.Ico a (lastEnd' a l), source p) ≤ (totalN l : ℝ) / 72057594037927936 := by
  intro l
  induction l with
  | nil =>
    intro a _
    refine ⟨le_refl a, ?_⟩
    simp [lastEnd', totalN]
  | cons x rest ih =>
    obtain ⟨e, N⟩ := x
    intro a h
    obtain ⟨hae, hb, hrest⟩ := h
    obtain ⟨hel, hc⟩ := ih e hrest
    refine ⟨hae.trans hel, ?_⟩
    have hsum := Finset.sum_Ico_consecutive source hae hel
    simp only [lastEnd', totalN, Int.cast_add]
    rw [← hsum, add_div]
    exact add_le_add hb hc

/-- Short: the 333,300 original graphs, pivots p ≤ 100. -/
theorem short100_units {l : List (ℕ × Box)} (h : ChunksOK originalShortRow 0 l)
    (hl : lastEnd 0 l = 101)
    (hhi : (totalBox l).hi * 72057594037927936 ≤ 3738038979785516612 * unit) :
    originalShortPrefix 100 ≤ shortPrefixUnits := by
  simpa only [shortPrefixUnits, intervalUnit, Int.cast_ofNat] using short_prefix_le h hl hhi

/-- Pure: pivots p ≤ 400, two bases per pair. -/
theorem pure400_units {l : List (ℕ × Box)} (h : ChunksOK pureSourceRow 0 l)
    (hl : lastEnd 0 l = 401)
    (hhi : (totalBox l).hi * 72057594037927936 ≤ 101235082714477743831 * unit) :
    originalPurePrefix 400 ≤ purePrefixUnits := by
  simpa only [purePrefixUnits, intervalUnit, Int.cast_ofNat] using pure_prefix_le h hl hhi

/-- Mixed: pivots p ≤ 100, 2(p-r) bases per pair. -/
theorem mixed100_units {l : List (ℕ × Box)} (h : ChunksOK mixedSourceRow 0 l)
    (hl : lastEnd 0 l = 101)
    (hhi : (totalBox l).hi * 72057594037927936 ≤ 36617965435406954 * unit) :
    originalMixedPrefix 100 ≤ mixedPrefixUnits := by
  simpa only [mixedPrefixUnits, intervalUnit, Int.cast_ofNat] using mixed_prefix_le h hl hhi

theorem short_prefix_le_of_chunks {l : List (ℕ × ℤ)} {P : ℕ} (h : ChunksLE originalShortRow 0 l)
    (hl : lastEnd' 0 l = P+1) {n : ℤ} (hn : totalN l ≤ n) :
    originalShortPrefix P ≤ (n:ℝ) / 72057594037927936 := by
  have := (chunksLE_bound originalShortRow l 0 h).2
  rw [hl] at this
  have h2 : originalShortPrefix P = ∑ p ∈ Finset.Ico 0 (P+1), originalShortRow p := by
    simp only [originalShortPrefix, originalShortRow, Finset.range_eq_Ico]
  rw [h2]
  exact this.trans (div_le_div_of_nonneg_right (by exact_mod_cast hn) (by norm_num))

theorem pure_prefix_le_of_chunks {l : List (ℕ × ℤ)} {P : ℕ} (h : ChunksLE pureSourceRow 0 l)
    (hl : lastEnd' 0 l = P+1) {n : ℤ} (hn : totalN l ≤ n) :
    originalPurePrefix P ≤ (n:ℝ) / 72057594037927936 := by
  have := (chunksLE_bound pureSourceRow l 0 h).2
  rw [hl] at this
  have h2 : originalPurePrefix P = ∑ p ∈ Finset.Ico 0 (P+1), pureSourceRow p := by
    simp only [originalPurePrefix, pureSourceRow, Finset.range_eq_Ico]
  rw [h2]
  exact this.trans (div_le_div_of_nonneg_right (by exact_mod_cast hn) (by norm_num))

theorem mixed_prefix_le_of_chunks {l : List (ℕ × ℤ)} {P : ℕ} (h : ChunksLE mixedSourceRow 0 l)
    (hl : lastEnd' 0 l = P+1) {n : ℤ} (hn : totalN l ≤ n) :
    originalMixedPrefix P ≤ (n:ℝ) / 72057594037927936 := by
  have := (chunksLE_bound mixedSourceRow l 0 h).2
  rw [hl] at this
  have h2 : originalMixedPrefix P = ∑ p ∈ Finset.Ico 0 (P+1), mixedSourceRow p := by
    simp only [originalMixedPrefix, mixedSourceRow, Finset.range_eq_Ico]
  rw [h2]
  exact this.trans (div_le_div_of_nonneg_right (by exact_mod_cast hn) (by norm_num))

theorem short100_units_of_chunks {l : List (ℕ × ℤ)} (h : ChunksLE originalShortRow 0 l)
    (hl : lastEnd' 0 l = 101) (hn : totalN l ≤ 3738038979785516612) :
    originalShortPrefix 100 ≤ shortPrefixUnits := by
  simpa only [shortPrefixUnits, intervalUnit, Int.cast_ofNat] using
    short_prefix_le_of_chunks h hl hn

theorem pure400_units_of_chunks {l : List (ℕ × ℤ)} (h : ChunksLE pureSourceRow 0 l)
    (hl : lastEnd' 0 l = 401) (hn : totalN l ≤ 101235082714477743831) :
    originalPurePrefix 400 ≤ purePrefixUnits := by
  simpa only [purePrefixUnits, intervalUnit, Int.cast_ofNat] using
    pure_prefix_le_of_chunks h hl hn

theorem mixed100_units_of_chunks {l : List (ℕ × ℤ)} (h : ChunksLE mixedSourceRow 0 l)
    (hl : lastEnd' 0 l = 101) (hn : totalN l ≤ 36617965435406954) :
    originalMixedPrefix 100 ≤ mixedPrefixUnits := by
  simpa only [mixedPrefixUnits, intervalUnit, Int.cast_ofNat] using
    mixed_prefix_le_of_chunks h hl hn

#print axioms chunks_contains
#print axioms short_prefix_le
#print axioms short100_units
#print axioms pure400_units
#print axioms mixed100_units

end SubmittedGenus.CapFourMass.Interval.PrefixNative.Assembly
