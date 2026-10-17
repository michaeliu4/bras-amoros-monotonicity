import Results.Genus.CapFourMass.IntervalTables
import Results.Genus.CapFourMass.IntervalPower
import Results.Genus.RawGraph.PackedAcceptance.LayoutCheck

/-! Supplied local interval tables for the actual physical raw source. All
unary masks, loops, and cycle closing edges are checked against the source
layout. No recursively expanded arithmetic expression is a certificate input. -/
open scoped BigOperators
namespace SubmittedGenus.CapFourMass.Interval
namespace RawTables
open RawGraph RawGraph.LayoutCompiler RawGraph.SourceModel

def vertex {m : ℕ} (r p a : ℕ) (z : Box) (i : Fin (m-1)) (v : Fin (a+1)) : Box :=
  if Domain r p a i v.val then fastPower z v.val else point 0

def edge {m : ℕ} (r p a : ℕ) (i j : Fin (m-1)) (v w : Fin (a+1)) : Box :=
  if edgeBound r p a i j≤v.val+w.val then point 1 else point 0

def vertices {m : ℕ} (L : Layout m) (r p a : ℕ) (z : Box)
    (c : Fin L.count) (j : ℕ) (v : Fin (a+1)) : Box :=
  if h:j<L.edges c+1 then vertex r p a z (L.label ⟨c,⟨j,h⟩⟩) v else point 0

def edges {m : ℕ} (L : Layout m) (r p a : ℕ)
    (c : Fin L.count) (j : ℕ) (v w : Fin (a+1)) : Box :=
  if h:j<L.edges c then edge r p a
    (L.label ⟨c,(⟨j,h⟩:Fin (L.edges c)).castSucc⟩)
    (L.label ⟨c,(⟨j,h⟩:Fin (L.edges c)).succ⟩) v w else point 1

def close {m : ℕ} (L : Layout m) (r p a : ℕ)
    (c : Fin L.count) (v w : Fin (a+1)) : Box :=
  edge r p a (L.label ⟨c,Fin.last (L.edges c)⟩) (L.label ⟨c,0⟩) v w

abbrev Tables {m : ℕ} (L : Layout m) (a : ℕ) :=
  (c : Fin L.count) → Fin (a+1) → Fin (L.edges c+1) → Fin (a+1) → Box

def Valid {m : ℕ} (L : Layout m) (r p a : ℕ) (z : Box) (ts : Tables L a) : Prop :=
  ∀c, if L.cycle c=true then
    ∀first, TableValid (L.edges c) (vertices L r p a z c) (edges L r p a c)
      (fun last=>close L r p a c last first) (ts c first)
  else TableValid (L.edges c) (vertices L r p a z c) (edges L r p a c)
    (fun _=>point 1) (ts c 0)

instance {m : ℕ} (L : Layout m) (r p a : ℕ) (z : Box) (ts : Tables L a) :
    Decidable (Valid L r p a z ts) := by unfold Valid; infer_instance

def componentBox {m : ℕ} (L : Layout m) (a : ℕ) (ts : Tables L a) (c : Fin L.count) : Box :=
  if L.cycle c=true then sumBoxes (fun first=>ts c first 0 first)
  else sumBoxes (ts c 0 0)

def layoutBox {m : ℕ} (L : Layout m) (a : ℕ) (ts : Tables L a) : Box :=
  prodBoxes (componentBox L a ts)

theorem vertex_contains {m : ℕ} (r p a : ℕ) {zb : Box} {z : ℝ} (hz : Contains zb z)
    (i : Fin (m-1)) (v : Fin (a+1)) :
    Contains (vertex r p a zb i v) (PackedAcceptance.vertexScalar r p a z i v) := by
  unfold vertex PackedAcceptance.vertexScalar
  split_ifs
  · exact fastPower_contains hz v.val
  · simpa using point_contains 0

theorem edge_contains {m : ℕ} (r p a : ℕ) (i j : Fin (m-1)) (v w : Fin (a+1)) :
    Contains (edge r p a i j v w) (PackedAcceptance.edgeScalar (R:=ℝ) r p a i j v w) := by
  unfold edge PackedAcceptance.edgeScalar
  split_ifs
  · simpa using point_contains 1
  · simpa using point_contains 0

theorem vertices_contains {m : ℕ} (L : Layout m) (r p a : ℕ) {zb : Box} {z : ℝ}
    (hz : Contains zb z) (c : Fin L.count) (j : ℕ) (v : Fin (a+1)) :
    Contains (vertices L r p a zb c j v) (PackedAcceptance.scalarVertices L r p a z c j v) := by
  unfold vertices PackedAcceptance.scalarVertices
  split_ifs
  · exact vertex_contains r p a hz _ v
  · simpa using point_contains 0

theorem edges_contains {m : ℕ} (L : Layout m) (r p a : ℕ)
    (c : Fin L.count) (j : ℕ) (v w : Fin (a+1)) :
    Contains (edges L r p a c j v w) (PackedAcceptance.scalarEdges (R:=ℝ) L r p a c j v w) := by
  unfold edges PackedAcceptance.scalarEdges
  split_ifs
  · exact edge_contains r p a _ _ v w
  · simpa using point_contains 1

theorem close_contains {m : ℕ} (L : Layout m) (r p a : ℕ)
    (c : Fin L.count) (v w : Fin (a+1)) :
    Contains (close L r p a c v w) (PackedAcceptance.scalarClose (R:=ℝ) L r p a c v w) :=
  edge_contains r p a _ _ v w

theorem component_contains {m : ℕ} (L : Layout m) (r p a : ℕ) {zb : Box} {z : ℝ}
    (hz : Contains zb z) (ts : Tables L a) (ht : Valid L r p a zb ts) (c : Fin L.count) :
    Contains (componentBox L a ts c) (PackedAcceptance.scalarComponent L r p a z c) := by
  have hc:=ht c
  unfold componentBox PackedAcceptance.scalarComponent
  split_ifs with h
  · simp only [h,ite_true] at hc
    exact cycle_table_contains (L.edges c) _ _ _ _ _ _
      (vertices_contains L r p a hz c) (edges_contains L r p a c)
      (close_contains L r p a c) (ts c) hc
  · simp only [h] at hc
    exact path_table_contains (L.edges c) _ _ _ _
      (vertices_contains L r p a hz c) (edges_contains L r p a c) (ts c 0) hc

/-- A locally accepted table encloses the actual raw polynomial at the supplied real radius. -/
theorem layout_contains_raw {m r p a : ℕ} (L : Layout m)
    (hp : Parameters m r p a) (hc : Covers L r p a) {zb : Box} {z : ℝ}
    (hz : Contains zb z) (ts : Tables L a) (ht : Valid L r p a zb ts) :
    Contains (layoutBox L a ts) (Polynomial.eval₂ (Nat.castRingHom ℝ) z (rawPolynomial m r p a)) := by
  rw [PackedAcceptance.eval_raw_eq_scalar L hp hc]
  exact prodBoxes_contains (component_contains L r p a hz ts ht)

end RawTables
end SubmittedGenus.CapFourMass.Interval
