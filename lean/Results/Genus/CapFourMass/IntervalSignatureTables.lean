import Results.Genus.CapFourMass.IntervalTables
import Results.Genus.CapFourMass.IntervalPower
import Results.Genus.RawGraph.PackedAcceptance.Signatures

/-! Shared interval tables for exact ordered physical component signatures. -/
open scoped BigOperators
namespace SubmittedGenus.CapFourMass.Interval
namespace SignatureTables
open RawGraph RawGraph.LayoutCompiler RawGraph.PackedAcceptance

deriving instance DecidableEq for ComponentSignature

def vertices {a : ℕ} (s : ComponentSignature a) (z : Box)
    (j : ℕ) (v : Fin (a+1)) : Box :=
  if h:j<s.edges+1 then if s.mask ⟨j,h⟩ v then fastPower z v.val else point 0 else point 0

def edges {a : ℕ} (s : ComponentSignature a) (j : ℕ) (v w : Fin (a+1)) : Box :=
  if h:j<s.edges then if s.bound ⟨j,h⟩≤v.val+w.val then point 1 else point 0 else point 1

def close {a : ℕ} (s : ComponentSignature a) (v w : Fin (a+1)) : Box :=
  if s.close≤v.val+w.val then point 1 else point 0

abbrev Tables {a : ℕ} (s : ComponentSignature a) :=
  Fin (a+1) → Fin (s.edges+1) → Fin (a+1) → Box

def Valid {a : ℕ} (s : ComponentSignature a) (z : Box) (ts : Tables s) : Prop :=
  if s.cycle then ∀first,TableValid s.edges (vertices s z) (edges s)
    (fun last=>close s last first) (ts first)
  else TableValid s.edges (vertices s z) (edges s) (fun _=>point 1) (ts 0)

instance {a : ℕ} (s : ComponentSignature a) (z : Box) (ts : Tables s) :
    Decidable (Valid s z ts) := by unfold Valid; infer_instance

def output {a : ℕ} (s : ComponentSignature a) (ts : Tables s) : Box :=
  if s.cycle then sumBoxes (fun first=>ts first 0 first) else sumBoxes (ts 0 0)

theorem vertices_contains {a : ℕ} (s : ComponentSignature a) {zb : Box} {z : ℝ}
    (hz : Contains zb z) (j : ℕ) (v : Fin (a+1)) :
    Contains (vertices s zb j v) (signatureVertices s z j v) := by
  unfold vertices signatureVertices
  split_ifs
  · exact fastPower_contains hz v.val
  · simpa using point_contains 0
  · simpa using point_contains 0

theorem edges_contains {a : ℕ} (s : ComponentSignature a) (j : ℕ) (v w : Fin (a+1)) :
    Contains (edges s j v w) (signatureEdges (R:=ℝ) s j v w) := by
  unfold edges signatureEdges
  split_ifs
  · simpa using point_contains 1
  · simpa using point_contains 0
  · simpa using point_contains 1

theorem close_contains {a : ℕ} (s : ComponentSignature a) (v w : Fin (a+1)) :
    Contains (close s v w) (if s.close≤v.val+w.val then (1:ℝ) else 0) := by
  unfold close
  split_ifs
  · simpa using point_contains 1
  · simpa using point_contains 0

/-- One checked table can be reused wherever this entire source signature occurs. -/
theorem signature_contains {a : ℕ} (s : ComponentSignature a) {zb : Box} {z : ℝ}
    (hz : Contains zb z) (ts : Tables s) (ht : Valid s zb ts) :
    Contains (output s ts) (signatureScalar s z) := by
  unfold output signatureScalar
  unfold Valid at ht
  split_ifs with h
  · simp only [h,ite_true] at ht
    exact cycle_table_contains s.edges _ _ _ _ _ _
      (vertices_contains s hz) (edges_contains s) (close_contains s) ts ht
  · simp only [h,ite_false] at ht
    exact path_table_contains s.edges _ _ _ _
      (vertices_contains s hz) (edges_contains s) (ts 0) ht

/-- The per-graph check now consists of source signature matching and a finite
product of already certified cache boxes. -/
theorem cache_layout_contains {m r p a : ℕ} (L : Layout m)
    (hp : Parameters m r p a) (hc : Covers L r p a)
    {I : Type*} (cache : I→ComponentSignature a) (boxes : I→Box) (key : Fin L.count→I)
    (hs : ∀c,physicalSignature L r p a c=cache (key c)) {z : ℝ}
    (hb : ∀i,Contains (boxes i) (signatureScalar (cache i) z)) :
    Contains (prodBoxes (fun c=>boxes (key c)))
      (Polynomial.eval₂ (Nat.castRingHom ℝ) z (rawPolynomial m r p a)) := by
  rw [eval_raw_eq_signature_product L hp hc cache key hs]
  exact prodBoxes_contains (fun c=>hb (key c))

end SignatureTables
end SubmittedGenus.CapFourMass.Interval
