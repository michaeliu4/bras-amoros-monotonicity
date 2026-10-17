import Results.Genus.CapFourMass.IntervalCompactOriginalBatchCheckV3
import Results.Genus.CapFourMass.IntervalReflectionShortRows
import Results.Genus.CapFourMass.IntervalPhysicalFixtures

/-! Executable five-state certificates for the original short source.
Finite table recurrences certify each complete component signature. Each graph
then checks every ordered physical component against its supplied cache key.
The resulting ShortEntry array needs no assumed raw-polynomial containment.
All original p ≤ 100, 1 ≤ r < p and p < m ≤ 2p occurrences remain covered by
the existing finite batch coverage checker. Repeated component keys stay repeated.
This module proves a checker interface, not a concrete short100 numerical bound. -/
open scoped BigOperators
namespace SubmittedGenus.CapFourMass.Interval.CompactOriginalShortV3
open RawGraph RawGraph.LayoutCompiler RawGraph.PackedAcceptance
open CompactOriginalBatchV3

/-- A path stores one five-state table. A cycle stores all five closing-state
tables, including the exact final-to-first threshold in its signature. -/
structure SignatureEntry where
  signature : ComponentSignature 4
  cells : Array Box
  box : Box

namespace SignatureEntry

def requiredCells (e : SignatureEntry) : ℕ :=
  (if e.signature.cycle then 25 else 5) * (e.signature.edges+1)

def tables (e : SignatureEntry) : SignatureTables.Tables e.signature :=
  fun first j v =>
    e.cells[(first.val * (e.signature.edges+1) + j.val) * 5 + v.val]?.getD (point 0)

def check (e : SignatureEntry) : Bool :=
  decide (e.cells.size = e.requiredCells ∧
    SignatureTables.Valid e.signature PhysicalFixtures.radiusBox e.tables ∧
    SignatureTables.output e.signature e.tables = e.box)

theorem contains {e : SignatureEntry} (h : e.check = true) :
    Contains e.box (signatureScalar e.signature radius) := by
  have hc : e.cells.size = e.requiredCells ∧
      SignatureTables.Valid e.signature PhysicalFixtures.radiusBox e.tables ∧
      SignatureTables.output e.signature e.tables = e.box := of_decide_eq_true h
  rw [←hc.2.2]
  exact SignatureTables.signature_contains e.signature
    PhysicalFixtures.radiusBox_contains e.tables hc.2.1

theorem rejects_wrong_cell_count (e : SignatureEntry)
    (hne : e.cells.size ≠ e.requiredCells) : e.check = false := by
  cases h : e.check with
  | false => rfl
  | true => exact False.elim (hne (of_decide_eq_true h).1)

end SignatureEntry

def cacheCheck {k : ℕ} (entries : Fin k → SignatureEntry) : Bool :=
  decide (∀ i, (entries i).check = true)

theorem cache_contains {k : ℕ} {entries : Fin k → SignatureEntry}
    (h : cacheCheck entries = true) (i : Fin k) :
    Contains (entries i).box (signatureScalar (entries i).signature radius) :=
  SignatureEntry.contains ((of_decide_eq_true h) i)

/-- The original source coordinate is part of the certificate, not a label.
Its layout is the already-proved reflected original layout at cap four. -/
structure GraphCertificate where
  p : ℕ
  pivot : Fin (p-1)
  step : Fin p
  keys : Array ℕ
  box : Box

namespace GraphCertificate

abbrev layout (g : GraphCertificate) := ReflectionShortRows.layout g.pivot g.step

def rawKey (g : GraphCertificate) (c : Fin g.layout.count) : ℕ :=
  g.keys[c.val]?.getD 0

def key (g : GraphCertificate) {k : ℕ} (hk : 0 < k)
    (c : Fin g.layout.count) : Fin k :=
  ⟨g.rawKey c % k, Nat.mod_lt _ hk⟩

def output (g : GraphCertificate) {k : ℕ} (hk : 0 < k)
    (entries : Fin k → SignatureEntry) : Box :=
  prodBoxes (fun c => (entries (g.key hk c)).box)

def check (g : GraphCertificate) {k : ℕ} (hk : 0 < k)
    (entries : Fin k → SignatureEntry) : Bool :=
  decide (g.keys.size = g.layout.count ∧
    (∀ c : Fin g.layout.count, g.rawKey c < k ∧
      SameSignature (physicalSignature g.layout (g.pivot.val+1) g.p 4 c)
        (entries (g.key hk c)).signature) ∧ g.output hk entries = g.box)

def entry (g : GraphCertificate) : ShortEntry :=
  ⟨g.p, g.pivot.val+1, g.step.val, g.box⟩

/-- A successful bound check prevents the total accessor from wrapping a key. -/
theorem key_val_of_check {g : GraphCertificate} {k : ℕ} {hk : 0 < k}
    {entries : Fin k → SignatureEntry} (h : g.check hk entries = true)
    (c : Fin g.layout.count) : (g.key hk c).val = g.rawKey c :=
  Nat.mod_eq_of_lt ((of_decide_eq_true h).2.1 c).1

theorem entry_contains {g : GraphCertificate} {k : ℕ} {hk : 0 < k}
    {entries : Fin k → SignatureEntry} (hc : cacheCheck entries = true)
    (hg : g.check hk entries = true) : Contains g.entry.box g.entry.source := by
  have hcheck : g.keys.size = g.layout.count ∧
      (∀ c : Fin g.layout.count, g.rawKey c < k ∧
        SameSignature (physicalSignature g.layout (g.pivot.val+1) g.p 4 c)
          (entries (g.key hk c)).signature) ∧ g.output hk entries = g.box :=
    of_decide_eq_true hg
  change Contains g.box (Polynomial.eval₂ (Nat.castRingHom ℝ) radius
    (rawPolynomial (g.p+1+g.step.val) (g.pivot.val+1) g.p 4))
  rw [←hcheck.2.2]
  apply SignatureTables.cache_layout_contains g.layout
    (cache := fun i : Fin k => (entries i).signature)
    (boxes := fun i : Fin k => (entries i).box) (key := g.key hk)
  · unfold Parameters
    have hr := ReflectionShortRows.pivot_lt g.pivot
    omega
  · exact ReflectionOriginalLayout.covers _ _ _ _
      (ReflectionShortRows.pivot_lt g.pivot) (by omega)
  · exact fun c => sameSignature_sound (hcheck.2.1 c).2
  · exact cache_contains hc

theorem rejects_wrong_key_count (g : GraphCertificate) {k : ℕ} (hk : 0 < k)
    (entries : Fin k → SignatureEntry) (hne : g.keys.size ≠ g.layout.count) :
    g.check hk entries = false := by
  cases h : g.check hk entries with
  | false => rfl
  | true => exact False.elim (hne (of_decide_eq_true h).1)

theorem rejects_out_of_range_key (g : GraphCertificate) {k : ℕ} (hk : 0 < k)
    (entries : Fin k → SignatureEntry) (c : Fin g.layout.count)
    (hne : k ≤ g.rawKey c) : g.check hk entries = false := by
  cases h : g.check hk entries with
  | false => rfl
  | true => exact False.elim (Nat.not_lt_of_ge hne ((of_decide_eq_true h).2.1 c).1)

theorem rejects_wrong_signature (g : GraphCertificate) {k : ℕ} (hk : 0 < k)
    (entries : Fin k → SignatureEntry) (c : Fin g.layout.count)
    (hne : ¬ SameSignature (physicalSignature g.layout (g.pivot.val+1) g.p 4 c)
      (entries (g.key hk c)).signature) : g.check hk entries = false := by
  cases h : g.check hk entries with
  | false => rfl
  | true => exact False.elim (hne ((of_decide_eq_true h).2.1 c).2)

end GraphCertificate

def entryArray (graphs : Array GraphCertificate) : Array ShortEntry :=
  graphs.map GraphCertificate.entry

def graphsCheck {k : ℕ} (hk : 0 < k) (entries : Fin k → SignatureEntry)
    (graphs : Array GraphCertificate) : Bool :=
  decide (∀ i : Fin graphs.size, graphs[i].check hk entries = true)

/-- Raw-polynomial containment for the entire array follows from executable
cache recurrence and ordered source-signature checks; it is not an input premise. -/
theorem entryArray_contains {k : ℕ} {hk : 0 < k} {entries : Fin k → SignatureEntry}
    {graphs : Array GraphCertificate} (hc : cacheCheck entries = true)
    (hg : graphsCheck hk entries graphs = true) :
    ∀ i : Fin (entryArray graphs).size,
      Contains (entryArray graphs)[i].box (entryArray graphs)[i].source := by
  intro i
  have hi : i.val < graphs.size := by
    simpa only [entryArray, Array.size_map] using i.isLt
  have h := GraphCertificate.entry_contains hc ((of_decide_eq_true hg) ⟨i.val,hi⟩)
  change Contains ((graphs.map GraphCertificate.entry)[i.val]'i.isLt).box
    ((graphs.map GraphCertificate.entry)[i.val]'i.isLt).source
  have he : ((graphs.map GraphCertificate.entry)[i.val]'i.isLt) =
      (graphs[i.val]'hi).entry :=
    Array.getElem_map GraphCertificate.entry i.isLt
  rw [he]
  exact h

theorem short_chunk_contains {k : ℕ} {hk : 0 < k} {entries : Fin k → SignatureEntry}
    {graphs : Array GraphCertificate} (hc : cacheCheck entries = true)
    (hg : graphsCheck hk entries graphs = true)
    {lookup : ShortLookup (entryArray graphs)} {b : ShortBoxes} {start stop : ℕ}
    (hcover : shortCoverageCheck (entryArray graphs) lookup b start stop = true) :
    Contains (shortChunk b start stop)
      (∑ p ∈ Finset.Ico start stop, originalShortRow p) :=
  CompactOriginalBatchV3.short_chunk_contains (entryArray_contains hc hg) hcover

/-- All three premises are finite executable checks. The conclusion is the
original short100 target, with every original m,r,p occurrence retained. -/
theorem original_short100_contains {k : ℕ} {hk : 0 < k}
    {entries : Fin k → SignatureEntry} {graphs : Array GraphCertificate}
    (hc : cacheCheck entries = true) (hg : graphsCheck hk entries graphs = true)
    {lookup : ShortLookup (entryArray graphs)} {b : ShortBoxes}
    (hcover : shortCoverageCheck (entryArray graphs) lookup b 0 101 = true) :
    Contains (shortChunk b 0 101) (originalShortPrefix 100) :=
  CompactOriginalBatchV3.original_short100_contains (entryArray_contains hc hg) hcover

#print axioms SignatureEntry.contains
#print axioms SignatureEntry.rejects_wrong_cell_count
#print axioms cache_contains
#print axioms GraphCertificate.key_val_of_check
#print axioms GraphCertificate.entry_contains
#print axioms GraphCertificate.rejects_wrong_key_count
#print axioms GraphCertificate.rejects_out_of_range_key
#print axioms GraphCertificate.rejects_wrong_signature
#print axioms entryArray_contains
#print axioms short_chunk_contains
#print axioms original_short100_contains

end SubmittedGenus.CapFourMass.Interval.CompactOriginalShortV3
