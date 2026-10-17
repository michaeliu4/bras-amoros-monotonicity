import Results.Genus.PrefixNative.ShortGen
import Results.Genus.PrefixNative.Assembly

/-! Sub-row pieces of the short prefix: the graphs (p, r, j) with r in [ra, rb) and all
j < p.  A full row is the sum of consecutive pieces (`Assembly.ChunksOK` over `pairSource`). -/
namespace SubmittedGenus.CapFourMass.Interval.PrefixNative
open RawGraph RawGraph.LayoutCompiler RawGraph.PackedAcceptance
open CompactOriginalBatchV3 CompactOriginalShortV3
open scoped BigOperators

/-- Graphs (p, r, j) for one-based pivots r ∈ [ra, rb), in the order r, j. -/
def Gen.runPiece (p ra rb : ℕ) : Gen :=
  let zp := radiusPowers
  (List.range' (ra-1) (rb-ra)).foldl (fun st r =>
    if hr : r < p-1 then
      (List.finRange p).foldl (fun st j => st.addGraph zp p ⟨r,hr⟩ j) st
    else st) {}

/-- Position of the graph (p, r, j) in the piece starting at one-based pivot ra. -/
def pieceIndex (p ra r j : ℕ) : ℕ := (r-ra)*p + j

/-- Graph boxes of a piece, looked up by (r, j). -/
def pieceBoxes (p ra : ℕ) (es : Array ShortEntry) : ℕ → ℕ → Box := fun r j =>
  (es[pieceIndex p ra r j]?.map (·.box)).getD (point 0)

/-- Aggregate box: sum over r ∈ [ra, rb) of the pair boxes. -/
def pieceBox (p ra rb : ℕ) (es : Array ShortEntry) : Box :=
  IndexedModePrefix.sumBox (Finset.Ico ra rb) fun r =>
    IndexedShort.pairBox (fun j : Fin p => pieceBoxes p ra es r j.val)

def coordOk (es : Array ShortEntry) (idx p r j : ℕ) : Bool :=
  match es[idx]? with
  | some e => e.p == p && e.r == r && e.j == j
  | none => false

theorem coordOk_spec {es : Array ShortEntry} {idx p r j : ℕ} (h : coordOk es idx p r j = true) :
    ∃ hlt : idx < es.size, es[idx].p = p ∧ es[idx].r = r ∧ es[idx].j = j := by
  unfold coordOk at h
  cases hget : es[idx]? with
  | none => rw [hget] at h; exact absurd h (by simp)
  | some e =>
    rw [hget] at h
    have hlt := (Array.getElem?_eq_some_iff.mp hget).1
    have he := (Array.getElem?_eq_some_iff.mp hget).2
    refine ⟨hlt, ?_⟩
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    rw [he]
    exact ⟨h.1.1, h.1.2, h.2⟩

def pieceCoverage (p ra rb : ℕ) (es : Array ShortEntry) : Bool :=
  decide (∀ r ∈ Finset.Ico ra rb, ∀ j : Fin p, coordOk es (pieceIndex p ra r j.val) p r j.val = true)

def shortPieceCheckWith (fin : Box → Bool) (p ra rb : ℕ) : Bool :=
  let st := Gen.runPiece p ra rb
  if hk : 0 < st.entries.size then
    let entries : Fin st.entries.size → SignatureEntry := fun i => st.entries[i]
    let es := entryArray st.graphs
    cacheCheck entries && graphsCheck' hk entries st.graphs &&
      pieceCoverage p ra rb es && fin (pieceBox p ra rb es)
  else false

def shortPieceBox (p ra rb : ℕ) : Box :=
  pieceBox p ra rb (entryArray (Gen.runPiece p ra rb).graphs)

theorem shortPieceCheckWith_sound {fin : Box → Bool} {p ra rb : ℕ}
    (h : shortPieceCheckWith fin p ra rb = true) :
    ∃ bx, Contains bx (∑ r ∈ Finset.Ico ra rb, IndexedShort.pairSource p r) ∧ fin bx = true := by
  unfold shortPieceCheckWith at h
  dsimp only at h
  split at h
  · rename_i hk
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨hc, hg⟩, hcov⟩, hfin⟩ := h
    rw [graphsCheck'_eq] at hg
    have hs := entryArray_contains hc hg
    refine ⟨_, ?_, hfin⟩
    apply IndexedModePrefix.sumBox_contains
    intro r hr
    apply IndexedShort.pair_contains
    intro j
    have hcov' := (of_decide_eq_true hcov) r hr j
    obtain ⟨hidx, hp1, hr1, hj1⟩ := coordOk_spec hcov'
    have hv := hs ⟨pieceIndex p ra r j.val, hidx⟩
    have hsrc : ∀ e : ShortEntry, e.p = p → e.r = r → e.j = j.val → Contains e.box e.source →
        Contains e.box (Polynomial.eval₂ (Nat.castRingHom ℝ) radius
          (rawPolynomial (p+1+j.val) r p 4)) := by
      intro e h1 h2 h3 h4
      obtain ⟨ep, er, ej, eb⟩ := e
      simp only at h1 h2 h3
      subst h1 h2 h3
      exact h4
    have hget : (entryArray (Gen.runPiece p ra rb).graphs)[pieceIndex p ra r j.val]? =
        some ((entryArray (Gen.runPiece p ra rb).graphs)[pieceIndex p ra r j.val]'hidx) :=
      Array.getElem?_eq_some_iff.mpr ⟨hidx, rfl⟩
    unfold pieceBoxes
    rw [hget]
    simp only [Option.map_some, Option.getD_some]
    exact hsrc _ hp1 hr1 hj1 hv
  · contradiction

def shortPieceCheck (p ra rb : ℕ) (box : Box) : Bool :=
  shortPieceCheckWith (fun bx => decide (bx = box)) p ra rb

theorem shortPieceCheck_sound {p ra rb : ℕ} {box : Box} (h : shortPieceCheck p ra rb box = true) :
    Contains box (∑ r ∈ Finset.Ico ra rb, IndexedShort.pairSource p r) := by
  obtain ⟨bx, hc, hf⟩ := shortPieceCheckWith_sound h
  rw [← of_decide_eq_true hf]
  exact hc

def shortPieceCheckLe (p ra rb : ℕ) (N : ℤ) : Bool := shortPieceCheckWith (Assembly.leCheck N) p ra rb

theorem shortPieceCheckLe_sound {p ra rb : ℕ} {N : ℤ} (h : shortPieceCheckLe p ra rb N = true) :
    (∑ r ∈ Finset.Ico ra rb, IndexedShort.pairSource p r) ≤ (N:ℝ) / 72057594037927936 := by
  obtain ⟨bx, hc, hf⟩ := shortPieceCheckWith_sound h
  exact Assembly.le_of_contains_leCheck hc hf

theorem row_eq_sum_Ico (p : ℕ) :
    ∑ r ∈ Finset.Ico 1 p, IndexedShort.pairSource p r = originalShortRow p := by
  rw [← IndexedShort.rowSource_eq, IndexedShort.rowSource, Finset.sum_Ico_eq_sum_range]
  rw [Fin.sum_univ_eq_sum_range (fun i => IndexedShort.pairSource p (i+1)) (p-1)]
  exact Finset.sum_congr rfl (fun i _ => by rw [Nat.add_comm])

/-- A full short row from consecutive r-pieces. -/
theorem short_row_of_pieces {p : ℕ} {l : List (ℕ × Box)}
    (h : Assembly.ChunksOK (fun r => IndexedShort.pairSource p r) 1 l)
    (hl : Assembly.lastEnd 1 l = p) : Contains (Assembly.totalBox l) (originalShortRow p) := by
  have := (Assembly.chunks_contains _ l 1 h).2
  rw [hl, row_eq_sum_Ico] at this
  exact this

/-- A full short row from consecutive r-pieces, upper-bound form. -/
theorem short_row_le_of_pieces {p : ℕ} {l : List (ℕ × ℤ)}
    (h : Assembly.ChunksLE (fun r => IndexedShort.pairSource p r) 1 l)
    (hl : Assembly.lastEnd' 1 l = p) :
    originalShortRow p ≤ (Assembly.totalN l : ℝ) / 72057594037927936 := by
  have := (Assembly.chunksLE_bound _ l 1 h).2
  rw [hl, row_eq_sum_Ico] at this
  exact this

theorem row_as_chunk_le {p : ℕ} {x : ℝ} (h : originalShortRow p ≤ x) :
    (∑ q ∈ Finset.Ico p (p+1), originalShortRow q) ≤ x := by
  simpa using h

theorem row_as_chunk {p : ℕ} {b : Box} (h : Contains b (originalShortRow p)) :
    Contains b (∑ q ∈ Finset.Ico p (p+1), originalShortRow q) := by
  simpa using h

end SubmittedGenus.CapFourMass.Interval.PrefixNative
