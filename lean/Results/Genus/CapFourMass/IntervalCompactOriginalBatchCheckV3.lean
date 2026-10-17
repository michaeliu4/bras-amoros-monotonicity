import Results.Genus.CapFourMass.IntervalCompactModeNumericCheck
import Results.Genus.CapFourMass.IndexedModePrefixChunks
import Results.Genus.CapFourMass.IntervalIndexedShortRows

/-! One numerical packet can serve many original rows. Physical layouts and
programs remain in the checked family; ordered component keys are used without
sorting or deduplication. Coverage checks bind each original coordinate to its
actual checked certificate and requested dyadic box. Short inputs retain their
source-polynomial proof obligation. No numerical acceptance is asserted here. V3 makes pure coverage an explicit
finite Boolean traversal. Every requested coordinate is extracted by a proved
List.all lemma; public soundness remains indexed by Fin 2. -/
open scoped BigOperators
namespace SubmittedGenus.CapFourMass.Interval.CompactOriginalBatchV3
open ActualComponent ExecutableModes RationalTables ModeSignatures IndexedModePrefix

structure NumericPacket where
  keys : Array (Array ℕ)
  pure : Array (Option Box)
  mixed : Array (Option Box)

namespace NumericPacket

def certificate (A : NumericPacket) (F : CompactModeFamily) (i : Fin F.size) :
    CompactCertificate :=
  ⟨F[i], A.keys[i.val]?.getD #[], A.pure[i.val]?.getD none,
    A.mixed[i.val]?.getD none⟩

def shapeCheck (A : NumericPacket) (F : CompactModeFamily) : Bool :=
  decide (A.keys.size = F.size ∧ A.pure.size = F.size ∧ A.mixed.size = F.size)

def check (A : NumericPacket) (F : CompactModeFamily) (hF : F.check = true)
    (C : CachedContext) {k : ℕ} (entries : Fin k → Entry) : Bool :=
  A.shapeCheck F && decide (∀ i : Fin F.size,
    (A.certificate F i).numericCheck C entries (F.accepted hF i) = true)

theorem shape_of_check {A : NumericPacket} {F : CompactModeFamily}
    {hF : F.check = true} {C : CachedContext} {k : ℕ} {entries : Fin k → Entry}
    (h : A.check F hF C entries = true) :
    A.keys.size = F.size ∧ A.pure.size = F.size ∧ A.mixed.size = F.size := by
  exact of_decide_eq_true (Bool.and_eq_true_iff.mp h).1

theorem accepted {A : NumericPacket} {F : CompactModeFamily}
    {hF : F.check = true} {C : CachedContext} {k : ℕ} {entries : Fin k → Entry}
    (h : A.check F hF C entries = true) (i : Fin F.size) :
    (A.certificate F i).check C entries = true := by
  have hn : ∀ i : Fin F.size,
      (A.certificate F i).numericCheck C entries (F.accepted hF i) = true :=
    of_decide_eq_true (Bool.and_eq_true_iff.mp h).2
  exact CompactCertificate.check_of_numeric C entries _ (F.accepted hF i) (hn i)

/-- The exact supplied sequence is retained, including every repeated key. -/
theorem keys_unchanged (A : NumericPacket) (F : CompactModeFamily) (i : Fin F.size) :
    (A.certificate F i).keys = A.keys[i.val]?.getD #[] := rfl

theorem pure_contains {A : NumericPacket} {F : CompactModeFamily}
    {hF : F.check = true} {C : CachedContext} {k : ℕ} {entries : Fin k → Entry}
    (h : A.check F hF C entries = true) (i : Fin F.size) {b : Box}
    (hb : (A.certificate F i).pure = some b) :
    Contains b (sourcePureSeries F[i].r F[i].d F[i].n) :=
  CompactCertificate.pure_contains C entries (accepted h i) hb

theorem mixed_contains {A : NumericPacket} {F : CompactModeFamily}
    {hF : F.check = true} {C : CachedContext} {k : ℕ} {entries : Fin k → Entry}
    (h : A.check F hF C entries = true) (i : Fin F.size) {b : Box}
    (hb : (A.certificate F i).mixed = some b) :
    Contains b (sourceMixedSeries F[i].r F[i].d F[i].n) :=
  CompactCertificate.mixed_contains C entries (accepted h i) hb

/-- Lookup sharing is allowed; original occurrence indices are never quotiented. -/
abbrev Lookup (F : CompactModeFamily) := ℕ → ℕ → ℕ → Fin F.size

/-- Explicit finite traversal avoids global quantified decidability inference. -/
def pureCoverageCheck (A : NumericPacket) (F : CompactModeFamily)
    (lookup : Lookup F) (b : BaseBoxes) (start stop : ℕ) : Bool :=
  (List.range stop).all fun p =>
    if start ≤ p then (List.range p).all fun r =>
      if 1 ≤ r then (List.range 2).all fun n =>
        let i := lookup p r n
        decide (F[i].r = r ∧ F[i].d = p-r ∧ F[i].n = n ∧
          (A.certificate F i).pure = some (b r (p-r) n))
      else true
    else true

/-- Every occurrence in the full original domain was checked by the traversal. -/
theorem pure_coordinates_of_coverage {A : NumericPacket} {F : CompactModeFamily}
    {lookup : Lookup F} {b : BaseBoxes} {start stop p r : ℕ}
    (hc : A.pureCoverageCheck F lookup b start stop = true)
    (hp : p ∈ Finset.Ico start stop) (hr : r ∈ Finset.Ico 1 p) (n : Fin 2) :
    let i := lookup p r n.val
    F[i].r = r ∧ F[i].d = p-r ∧ F[i].n = n.val ∧
      (A.certificate F i).pure = some (b r (p-r) n.val) := by
  unfold pureCoverageCheck at hc
  have hpcheck := List.all_eq_true.mp hc p (List.mem_range.mpr (Finset.mem_Ico.mp hp).2)
  rw [if_pos (Finset.mem_Ico.mp hp).1] at hpcheck
  have hrcheck := List.all_eq_true.mp hpcheck r
    (List.mem_range.mpr (Finset.mem_Ico.mp hr).2)
  rw [if_pos (Finset.mem_Ico.mp hr).1] at hrcheck
  have hncheck := List.all_eq_true.mp hrcheck n.val (List.mem_range.mpr n.isLt)
  exact of_decide_eq_true hncheck

def mixedCoverageCheck (A : NumericPacket) (F : CompactModeFamily)
    (lookup : Lookup F) (b : BaseBoxes) (start stop : ℕ) : Bool :=
  decide (∀ p ∈ Finset.Ico start stop, ∀ r ∈ Finset.Ico 1 p,
    ∀ n : Fin (2*(p-r)),
    let i := lookup p r n.val
    F[i].r = r ∧ F[i].d = p-r ∧ F[i].n = n.val ∧
      (A.certificate F i).mixed = some (b r (p-r) n.val))

theorem pure_bases_of_coverage {A : NumericPacket} {F : CompactModeFamily}
    {hF : F.check = true} {C : CachedContext} {k : ℕ} {entries : Fin k → Entry}
    (h : A.check F hF C entries = true) {lookup : Lookup F} {b : BaseBoxes}
    {start stop : ℕ} (hc : A.pureCoverageCheck F lookup b start stop = true) :
    ∀ p ∈ Finset.Ico start stop, ∀ r ∈ Finset.Ico 1 p, ∀ n : Fin 2,
      Contains (b r (p-r) n.val) (sourcePureSeries r (p-r) n.val) := by
  intro p hp r hr n
  have coords := pure_coordinates_of_coverage hc hp hr n
  have value := pure_contains h (lookup p r n.val) coords.2.2.2
  simpa only [coords.1, coords.2.1, coords.2.2.1] using value

theorem mixed_bases_of_coverage {A : NumericPacket} {F : CompactModeFamily}
    {hF : F.check = true} {C : CachedContext} {k : ℕ} {entries : Fin k → Entry}
    (h : A.check F hF C entries = true) {lookup : Lookup F} {b : BaseBoxes}
    {start stop : ℕ} (hc : A.mixedCoverageCheck F lookup b start stop = true) :
    ∀ p ∈ Finset.Ico start stop, ∀ r ∈ Finset.Ico 1 p, ∀ n : Fin (2*(p-r)),
      Contains (b r (p-r) n.val) (sourceMixedSeries r (p-r) n.val) := by
  intro p hp r hr n
  have coords := (of_decide_eq_true hc) p hp r hr n
  have value := mixed_contains h (lookup p r n.val) coords.2.2.2
  simpa only [coords.1, coords.2.1, coords.2.2.1] using value

theorem pure_chunk_contains {A : NumericPacket} {F : CompactModeFamily}
    {hF : F.check = true} {C : CachedContext} {k : ℕ} {entries : Fin k → Entry}
    (h : A.check F hF C entries = true) {lookup : Lookup F} {b : BaseBoxes}
    {start stop : ℕ} (hc : A.pureCoverageCheck F lookup b start stop = true)
    {den : Box} (hd : Contains den (1-(normalizer*lam)^2)) (hpos : 0 < den.lo) :
    Contains (pureChunk b den start stop)
      (∑ p ∈ Finset.Ico start stop, pureSourceRow p) :=
  IndexedModePrefix.pureChunk_contains b den start stop
    (pure_bases_of_coverage h hc) hd hpos

theorem mixed_chunk_contains {A : NumericPacket} {F : CompactModeFamily}
    {hF : F.check = true} {C : CachedContext} {k : ℕ} {entries : Fin k → Entry}
    (h : A.check F hF C entries = true) {lookup : Lookup F} {b : BaseBoxes}
    {start stop : ℕ} (hc : A.mixedCoverageCheck F lookup b start stop = true)
    {den : ℕ → Box}
    (hd : ∀ p ∈ Finset.Ico start stop, ∀ r ∈ Finset.Ico 1 p,
      Contains (den (p-r)) (1-(normalizer*lam)^(2*(p-r))*rho^2))
    (hpos : ∀ p ∈ Finset.Ico start stop, ∀ r ∈ Finset.Ico 1 p, 0 < (den (p-r)).lo) :
    Contains (mixedChunk b den start stop)
      (∑ p ∈ Finset.Ico start stop, mixedSourceRow p) :=
  IndexedModePrefix.mixedChunk_contains b den start stop
    (mixed_bases_of_coverage h hc) hd hpos

/-- The original pure target remains p ≤ 400, with exactly two bases per pair. -/
theorem original_pure400_contains {A : NumericPacket} {F : CompactModeFamily}
    {hF : F.check = true} {C : CachedContext} {k : ℕ} {entries : Fin k → Entry}
    (h : A.check F hF C entries = true) {lookup : Lookup F} {b : BaseBoxes}
    (hc : A.pureCoverageCheck F lookup b 0 401 = true)
    {den : Box} (hd : Contains den (1-(normalizer*lam)^2)) (hpos : 0 < den.lo) :
    Contains (purePrefix b den 400) (originalPurePrefix 400) := by
  have bases := pure_bases_of_coverage h hc
  apply IndexedModePrefix.purePrefix_contains b den 400 _ hd hpos
  intro p hp
  exact bases p (Finset.mem_Ico.mpr ⟨Nat.zero_le p, by omega⟩)

/-- The original mixed target remains p ≤ 100 and all 2(p-r) bases. -/
theorem original_mixed100_contains {A : NumericPacket} {F : CompactModeFamily}
    {hF : F.check = true} {C : CachedContext} {k : ℕ} {entries : Fin k → Entry}
    (h : A.check F hF C entries = true) {lookup : Lookup F} {b : BaseBoxes}
    (hc : A.mixedCoverageCheck F lookup b 0 101 = true) {den : ℕ → Box}
    (hd : ∀ p ≤ 100, ∀ r ∈ Finset.Ico 1 p,
      Contains (den (p-r)) (1-(normalizer*lam)^(2*(p-r))*rho^2))
    (hpos : ∀ p ≤ 100, ∀ r ∈ Finset.Ico 1 p, 0 < (den (p-r)).lo) :
    Contains (mixedPrefix b den 100) (originalMixedPrefix 100) := by
  have bases := mixed_bases_of_coverage h hc
  apply IndexedModePrefix.mixedPrefix_contains b den 100 _ hd hpos
  intro p hp
  exact bases p (Finset.mem_Ico.mpr ⟨Nat.zero_le p, by omega⟩)

/-- A malformed outer key table cannot be admitted through total accessors. -/
theorem rejects_wrong_key_count {A : NumericPacket} {F : CompactModeFamily}
    {hF : F.check = true} {C : CachedContext} {k : ℕ} {entries : Fin k → Entry}
    (hne : A.keys.size ≠ F.size) : A.check F hF C entries = false := by
  cases hc : A.check F hF C entries with
  | false => rfl
  | true => exact False.elim (hne (shape_of_check hc).1)

/-- Reusing a certificate at a different original pivot is rejected. -/
theorem rejects_wrong_pure_pivot (A : NumericPacket) (F : CompactModeFamily)
    (lookup : Lookup F) (b : BaseBoxes) {start stop p r : ℕ} (n : Fin 2)
    (hp : p ∈ Finset.Ico start stop) (hr : r ∈ Finset.Ico 1 p)
    (hne : F[lookup p r n.val].r ≠ r) :
    A.pureCoverageCheck F lookup b start stop = false := by
  cases hc : A.pureCoverageCheck F lookup b start stop with
  | false => rfl
  | true =>
    exact False.elim (hne (pure_coordinates_of_coverage hc hp hr n).1)

/-- An omitted or altered requested pure box is rejected at that occurrence. -/
theorem rejects_missing_pure_box (A : NumericPacket) (F : CompactModeFamily)
    (lookup : Lookup F) (b : BaseBoxes) {start stop p r : ℕ} (n : Fin 2)
    (hp : p ∈ Finset.Ico start stop) (hr : r ∈ Finset.Ico 1 p)
    (hne : (A.certificate F (lookup p r n.val)).pure ≠ some (b r (p-r) n.val)) :
    A.pureCoverageCheck F lookup b start stop = false := by
  cases hc : A.pureCoverageCheck F lookup b start stop with
  | false => rfl
  | true =>
    exact False.elim (hne (pure_coordinates_of_coverage hc hp hr n).2.2.2)

end NumericPacket

/-- Short entries are accepted only with their original source-polynomial theorem.
The generic adapter does not manufacture a five-state vector certificate. -/
structure ShortEntry where
  p : ℕ
  r : ℕ
  j : ℕ
  box : Box

abbrev ShortBoxes := ℕ → ℕ → ℕ → Box
abbrev ShortLookup (entries : Array ShortEntry) := ℕ → ℕ → ℕ → Fin entries.size

noncomputable def ShortEntry.source (e : ShortEntry) : ℝ :=
  Polynomial.eval₂ (Nat.castRingHom ℝ) radius
    (RawGraph.rawPolynomial (e.p+1+e.j) e.r e.p 4)

def shortCoverageCheck (entries : Array ShortEntry) (lookup : ShortLookup entries)
    (b : ShortBoxes) (start stop : ℕ) : Bool :=
  decide (∀ p ∈ Finset.Ico start stop, ∀ r : Fin (p-1), ∀ j : Fin p,
    let i := lookup p (r.val+1) j.val
    entries[i].p = p ∧ entries[i].r = r.val+1 ∧ entries[i].j = j.val ∧
      entries[i].box = b p (r.val+1) j.val)

def shortRow (b : ShortBoxes) (p : ℕ) : Box :=
  IndexedShort.rowBox (fun r : Fin (p-1) =>
    IndexedShort.pairBox (fun j : Fin p => b p (r.val+1) j.val))

def shortChunk (b : ShortBoxes) (start stop : ℕ) : Box :=
  sumBox (Finset.Ico start stop) (shortRow b)

theorem short_rows_of_coverage {entries : Array ShortEntry}
    (hs : ∀ i : Fin entries.size, Contains entries[i].box entries[i].source)
    {lookup : ShortLookup entries} {b : ShortBoxes} {start stop : ℕ}
    (hc : shortCoverageCheck entries lookup b start stop = true) :
    ∀ p ∈ Finset.Ico start stop, Contains (shortRow b p) (originalShortRow p) := by
  intro p hp
  apply IndexedShort.row_contains
  intro r
  apply IndexedShort.pair_contains
  intro j
  have coords := (of_decide_eq_true hc) p hp r j
  have value := hs (lookup p (r.val+1) j.val)
  simpa only [ShortEntry.source, coords.1, coords.2.1, coords.2.2.1,
    coords.2.2.2] using value

theorem short_chunk_contains {entries : Array ShortEntry}
    (hs : ∀ i : Fin entries.size, Contains entries[i].box entries[i].source)
    {lookup : ShortLookup entries} {b : ShortBoxes} {start stop : ℕ}
    (hc : shortCoverageCheck entries lookup b start stop = true) :
    Contains (shortChunk b start stop)
      (∑ p ∈ Finset.Ico start stop, originalShortRow p) :=
  sumBox_contains _ _ _ (short_rows_of_coverage hs hc)

/-- Every original short occurrence remains p ≤ 100, 1 ≤ r < p, p < m ≤ 2p. -/
theorem original_short100_contains {entries : Array ShortEntry}
    (hs : ∀ i : Fin entries.size, Contains entries[i].box entries[i].source)
    {lookup : ShortLookup entries} {b : ShortBoxes}
    (hc : shortCoverageCheck entries lookup b 0 101 = true) :
    Contains (shortChunk b 0 101) (originalShortPrefix 100) := by
  have h := short_chunk_contains hs hc
  simpa only [originalShortPrefix, originalShortRow, Finset.range_eq_Ico] using h

#print axioms NumericPacket.rejects_wrong_key_count
#print axioms NumericPacket.rejects_wrong_pure_pivot
#print axioms NumericPacket.rejects_missing_pure_box
#print axioms NumericPacket.accepted
#print axioms NumericPacket.keys_unchanged
#print axioms NumericPacket.pure_bases_of_coverage
#print axioms NumericPacket.mixed_bases_of_coverage
#print axioms NumericPacket.pure_chunk_contains
#print axioms NumericPacket.mixed_chunk_contains
#print axioms NumericPacket.original_pure400_contains
#print axioms NumericPacket.original_mixed100_contains
#print axioms short_rows_of_coverage
#print axioms short_chunk_contains
#print axioms original_short100_contains

end SubmittedGenus.CapFourMass.Interval.CompactOriginalBatchV3
