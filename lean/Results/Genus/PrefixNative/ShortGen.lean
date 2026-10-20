import Results.Genus.CapFourMass.IntervalCompactOriginalShortCheckV3
import Results.Genus.PrefixNative.Assembly

/-! Native-evaluation generator for the original short prefix.

All data (distinct signature tables, ordered component keys, graph boxes) are
produced by Lean-side computation and then accepted by the existing V3 Boolean
checks (`cacheCheck`, `graphsCheck`, `shortCoverageCheck`).  Nothing produced here
is trusted: the generated arrays are only ever consumed through those checks. -/
namespace SubmittedGenus.CapFourMass.Interval.PrefixNative
open RawGraph RawGraph.LayoutCompiler RawGraph.PackedAcceptance
open CompactOriginalBatchV3 CompactOriginalShortV3
open scoped BigOperators

instance : Inhabited Box := ⟨point 0⟩
instance : Inhabited SignatureEntry :=
  ⟨⟨⟨0, fun _ _ => false, fun _ => 0, false, 0⟩, #[], point 0⟩⟩
instance : Inhabited GraphCertificate :=
  ⟨⟨2, ⟨0, by omega⟩, ⟨0, by omega⟩, #[], point 0⟩⟩

/-- Canonical description of an ordered signature, used only as a hash key.
Collisions cannot matter: the graph check compares the full signature. -/
def sigKey (s : ComponentSignature 4) : List ℕ :=
  let masks := (List.finRange (s.edges+1)).foldl (fun acc j =>
    (List.finRange 5).foldl (fun acc v =>
      if s.mask j v then acc ||| (1 <<< (5*j.val+v.val)) else acc) acc) 0
  s.edges :: (if s.cycle then 1 else 0) :: s.close :: masks ::
    (List.finRange s.edges).map (fun j => s.bound j)

/-- Powers z^0..z^4 of the radius box, as used by `SignatureTables.vertices`. -/
def radiusPowers : Array Box :=
  (List.range 5).toArray.map (fun v => fastPower PhysicalFixtures.radiusBox v)

def maskAt (s : ComponentSignature 4) (j : ℕ) (i : Fin 5) : Bool :=
  if h : j < s.edges+1 then s.mask ⟨j,h⟩ i else false

def boundAt (s : ComponentSignature 4) (j : ℕ) : ℕ :=
  if h : j < s.edges then s.bound ⟨j,h⟩ else 0

/-- All rows 0..edges of one transfer table, given the finishing vector. -/
def sliceRows (s : ComponentSignature 4) (zp : Array Box) (fin : Fin 5 → Box) :
    List (Array Box) := Id.run do
  let lastRow : Array Box := Array.ofFn (n := 5) fun i =>
    if maskAt s s.edges i then mul (zp[i.val]?.getD (point 0)) (fin i) else point 0
  let mut cur := lastRow
  let mut acc := [cur]
  for jj in [0:s.edges] do
    let j := s.edges - 1 - jj
    let nxt := cur
    cur := Array.ofFn (n := 5) fun i =>
      if maskAt s j i then
        let sm := (List.finRange 5).foldr (fun k a =>
          if boundAt s j ≤ i.val + k.val then add (nxt[k.val]?.getD (point 0)) a else a) (point 0)
        mul (zp[i.val]?.getD (point 0)) sm
      else point 0
    acc := cur :: acc
  return acc

def mkCells (s : ComponentSignature 4) (zp : Array Box) : Array Box :=
  if s.cycle then
    (List.finRange 5).foldl (fun cells first =>
      (sliceRows s zp (fun last => if s.close ≤ last.val+first.val then point 1 else point 0)).foldl
        (fun cells row => cells ++ row) cells) #[]
  else
    (sliceRows s zp (fun _ => point 1)).foldl (fun cells row => cells ++ row) #[]

def mkEntry (zp : Array Box) (s : ComponentSignature 4) : SignatureEntry :=
  let e0 : SignatureEntry := ⟨s, mkCells s zp, point 0⟩
  { e0 with box := SignatureTables.output s e0.tables }


/-! Strict physical signatures: each vertex label (an expensive Equiv evaluation)
is computed once and tabulated; the resulting signature equals `physicalSignature`. -/
def sigOfLabels {m : ℕ} (r p a e : ℕ) (lab : Fin (e+1) → Fin (m-1)) (cyc : Bool) :
    ComponentSignature a where
  edges := e
  mask j v := decide (SourceModel.Domain r p a (lab j) v.val)
  bound j := SourceModel.edgeBound r p a (lab j.castSucc) (lab j.succ)
  cycle := cyc
  close := SourceModel.edgeBound r p a (lab (Fin.last e)) (lab 0)

def labTab {m : ℕ} (L : Layout m) (c : Fin L.count) : Array (Fin (m-1)) :=
  Array.ofFn (fun j : Fin (L.edges c+1) => L.label ⟨c,j⟩)

theorem labTab_size {m : ℕ} (L : Layout m) (c : Fin L.count) : (labTab L c).size = L.edges c + 1 :=
  Array.size_ofFn

def sigOfArr {m : ℕ} (r p a e : ℕ) (arr : Array (Fin (m-1))) (h : arr.size = e+1) (cyc : Bool) :
    ComponentSignature a :=
  sigOfLabels r p a e (fun j => arr[j.val]'(by rw [h]; exact j.isLt)) cyc

def strictPhys {m : ℕ} (L : Layout m) (r p a : ℕ) (c : Fin L.count) : ComponentSignature a :=
  sigOfArr r p a (L.edges c) (labTab L c) (labTab_size L c) (L.cycle c)

theorem strictPhys_eq {m : ℕ} (L : Layout m) (r p a : ℕ) (c : Fin L.count) :
    strictPhys L r p a c = physicalSignature L r p a c := by
  unfold strictPhys sigOfArr physicalSignature sigOfLabels labTab
  simp only [Array.getElem_ofFn]

section CompTabSec
open ReflectionOriginalLayout

/-- Labels and cycle flag of one component of a layout `L`, with proofs that they are those of `L`. -/
structure CompTab {m : ℕ} (L : Layout m) (c : Fin L.count) where
  arr : Array (Fin (m-1))
  cyc : Bool
  e : ℕ
  hsz : arr.size = e + 1
  harr : arr = labTab L c
  he : e = L.edges c
  hcyc : cyc = L.cycle c

/-- Component tables of the original layout, with all shared data constructed once per graph /
once per component. -/
def compTabsFn {M r p : ℕ} (hrp : r<p) (hpm : p<M) :
    (c : Fin (layout M r p hrp hpm).count) → CompTab (layout M r p hrp hpm) c :=
  let C := coordinates M r p hrp hpm
  letI : NeZero C.g := ⟨ne_of_gt C.g_pos⟩
  fun c =>
    let cd := ReflectionFullLayout.componentData C.n r p C.δ C.coprime C.gap C.pivot_pos C.pivot_lt c
    let ec : Fin cd.size ≃ _ := cd.equiv.trans (ReflectionFullLayout.blockEquiv C.n r c)
    ⟨Array.ofFn (fun j : Fin (cd.size - 1 + 1) =>
      (finCongr (congrArg (fun n : ℕ => n-1) C.modulus.symm))
        (ec (ReflectionComponentCompiler.sizeIndex
          (fun c => (ReflectionFullLayout.componentData C.n r p C.δ C.coprime C.gap C.pivot_pos
            C.pivot_lt c).size)
          (fun c => (ReflectionFullLayout.componentData C.n r p C.δ C.coprime C.gap C.pivot_pos
            C.pivot_lt c).size_pos) c j)).val),
     cd.cycle, cd.size - 1, Array.size_ofFn, rfl, rfl, rfl⟩

def CompTab.strict {m : ℕ} {L : Layout m} {c : Fin L.count} (t : CompTab L c) (r p a : ℕ) :
    ComponentSignature a :=
  sigOfLabels r p a t.e (fun j => t.arr[j.val]'(by rw [t.hsz]; exact j.isLt)) t.cyc

theorem CompTab.strict_eq {m : ℕ} {L : Layout m} {c : Fin L.count} (t : CompTab L c) (r p a : ℕ) :
    t.strict r p a = strictPhys L r p a c := by
  obtain ⟨arr, cyc, e, hsz, harr, he, hcyc⟩ := t
  subst harr he hcyc
  unfold CompTab.strict strictPhys sigOfArr
  rfl

end CompTabSec


/-- Fast per-graph check: component label tables are constructed once per component. -/
def graphCheck' (g : GraphCertificate) {k : ℕ} (hk : 0 < k)
    (entries : Fin k → SignatureEntry) : Bool :=
  let tabs := compTabsFn (M := g.p+1+g.step.val) (r := g.pivot.val+1) (p := g.p)
    (ReflectionShortRows.pivot_lt g.pivot) (by omega)
  decide (g.keys.size = g.layout.count ∧
    (∀ c : Fin g.layout.count, g.rawKey c < k ∧
      SameSignature ((tabs c).strict (g.pivot.val+1) g.p 4)
        (entries (g.key hk c)).signature) ∧ g.output hk entries = g.box)

theorem graphCheck'_eq (g : GraphCertificate) {k : ℕ} (hk : 0 < k)
    (entries : Fin k → SignatureEntry) : graphCheck' g hk entries = g.check hk entries := by
  unfold graphCheck' GraphCertificate.check
  simp only [CompTab.strict_eq, strictPhys_eq]

def graphsCheck' {k : ℕ} (hk : 0 < k) (entries : Fin k → SignatureEntry)
    (graphs : Array GraphCertificate) : Bool :=
  decide (∀ i : Fin graphs.size, graphCheck' graphs[i] hk entries = true)

theorem graphsCheck'_eq {k : ℕ} (hk : 0 < k) (entries : Fin k → SignatureEntry)
    (graphs : Array GraphCertificate) : graphsCheck' hk entries graphs = graphsCheck hk entries graphs := by
  unfold graphsCheck' graphsCheck
  simp only [graphCheck'_eq]

structure Gen where
  index : Std.HashMap (List ℕ) ℕ := {}
  entries : Array SignatureEntry := #[]
  graphs : Array GraphCertificate := #[]

/-- Add the certificate of the graph (p, r+1, j) to the generator state. -/
def Gen.addGraph (zp : Array Box) (st : Gen) (p : ℕ) (r : Fin (p-1)) (j : Fin p) : Gen :=
  let g0 : GraphCertificate := ⟨p, r, j, #[], point 0⟩
  let L := g0.layout
  let tabs := compTabsFn (M := p+1+j.val) (r := r.val+1) (p := p) (ReflectionShortRows.pivot_lt r) (by omega)
  let (st, keys) := (List.finRange L.count).foldl (fun (acc : Gen × Array ℕ) c =>
    let (st, keys) := acc
    let s := (tabs c).strict (r.val+1) p 4
    let key := sigKey s
    match st.index[key]? with
    | some idx => (st, keys.push idx)
    | none =>
      let idx := st.entries.size
      ({ st with index := st.index.insert key idx, entries := st.entries.push (mkEntry zp s) },
        keys.push idx)) (st, #[])
  let box := keys.foldr (fun k acc => mul (st.entries[k]?.map (·.box) |>.getD (point 0)) acc) (point 1)
  { st with graphs := st.graphs.push { g0 with keys := keys, box := box } }

/-- Graphs for the pivots p in [a, b), in the order p, r, j. -/
def Gen.run (a b : ℕ) : Gen :=
  let zp := radiusPowers
  (List.range' a (b-a)).foldl (fun st p =>
    (List.finRange (p-1)).foldl (fun st r =>
      (List.finRange p).foldl (fun st j => st.addGraph zp p r j) st) st) {}

/-- Number of graphs with pivot in [a, p) (p*(p-1)*(p-2)/3 for a = 0). -/
def graphsBefore (q : ℕ) : ℕ := q*(q-1)*(q-2)/3

/-- Position of graph (p, r, j) (r one-based) in the array generated for [a, b). -/
def graphIndex (a p r j : ℕ) : ℕ := graphsBefore p - graphsBefore a + (r-1)*p + j

/-- Boxes of the generated graphs, looked up by (p, r, j). -/
def bbOf (a : ℕ) (es : Array ShortEntry) : ShortBoxes := fun p r j =>
  (es[graphIndex a p r j]?.map (·.box)).getD (point 0)

/-- Aggregate box of the generated data for pivots [a, b). -/
def chunkBox (a b : ℕ) : Box :=
  let st := Gen.run a b
  shortChunk (bbOf a (entryArray st.graphs)) a b

/-- Single Boolean for a chunk of pivots [a, b): the three V3 premises plus a predicate `fin` on the
aggregate box.  Closed term in (a, b, fin): suitable for `native_decide`. -/
def shortChunkCheckWith (fin : Box → Bool) (a b : ℕ) : Bool :=
  let st := Gen.run a b
  if hk : 0 < st.entries.size then
    let entries : Fin st.entries.size → SignatureEntry := fun i => st.entries[i]
    let es := entryArray st.graphs
    if hs : 0 < es.size then
      let lookup : ShortLookup es := fun p r j => ⟨min (graphIndex a p r j) (es.size-1), by omega⟩
      let bb : ShortBoxes := bbOf a es
      cacheCheck entries && graphsCheck' hk entries st.graphs &&
        shortCoverageCheck es lookup bb a b && fin (shortChunk bb a b)
    else false
  else false

theorem shortChunkCheckWith_sound {fin : Box → Bool} {a b : ℕ}
    (h : shortChunkCheckWith fin a b = true) :
    ∃ bx, Contains bx (∑ p ∈ Finset.Ico a b, originalShortRow p) ∧ fin bx = true := by
  unfold shortChunkCheckWith at h
  dsimp only at h
  split at h
  · rename_i hk
    split at h
    · rename_i hs
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨⟨hc, hg⟩, hcov⟩, hfin⟩ := h
      rw [graphsCheck'_eq] at hg
      exact ⟨_, short_chunk_contains hc hg hcov, hfin⟩
    · contradiction
  · contradiction

def shortChunkCheck (a b : ℕ) (box : Box) : Bool :=
  shortChunkCheckWith (fun bx => decide (bx = box)) a b

theorem shortChunkCheck_sound {a b : ℕ} {box : Box} (h : shortChunkCheck a b box = true) :
    Contains box (∑ p ∈ Finset.Ico a b, originalShortRow p) := by
  obtain ⟨bx, hc, hf⟩ := shortChunkCheckWith_sound h
  rw [← of_decide_eq_true hf]
  exact hc

/-- Upper-bound form: the source sum over [a, b) is at most N / 2^56. -/
def shortChunkCheckLe (a b : ℕ) (N : ℤ) : Bool := shortChunkCheckWith (Assembly.leCheck N) a b

theorem shortChunkCheckLe_sound {a b : ℕ} {N : ℤ} (h : shortChunkCheckLe a b N = true) :
    (∑ p ∈ Finset.Ico a b, originalShortRow p) ≤ (N:ℝ) / 72057594037927936 := by
  obtain ⟨bx, hc, hf⟩ := shortChunkCheckWith_sound h
  exact Assembly.le_of_contains_leCheck hc hf

end SubmittedGenus.CapFourMass.Interval.PrefixNative
