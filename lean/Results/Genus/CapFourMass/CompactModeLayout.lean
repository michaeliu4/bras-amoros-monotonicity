import Results.Genus.CapFourMass.ExecutableModeLinearCheck

/-! Compact, untrusted natural-array storage for the exact signed layout
contract. Array shape, free physical indices, and inverse bounds are checked
before conversion to typed data. The existing exact-once linear checker then
checks every inverse and edge. No correctness of an external producer is used. -/
namespace SubmittedGenus.CapFourMass.ExecutableModes
open RawGraph RawGraph.SourceModel RawGraph.Topology

/-- One physical path or cycle, with one-based original coordinates. -/
structure CompactComponent where
  vertices : Array ℕ
  cycle : Bool
  deriving Inhabited, DecidableEq

/-- The inverse array is indexed by physical coordinate minus one. Pivot
entries are unused; all other entries are checked in both directions. -/
structure CompactLayout where
  components : Array CompactComponent
  inverse : Array (ℕ × ℕ)
  deriving Inhabited, DecidableEq

namespace CompactLayout

def component (D : CompactLayout) (c : ℕ) : CompactComponent :=
  D.components[c]?.getD default

def vertex (D : CompactLayout) (c j : ℕ) : ℕ :=
  (D.component c).vertices[j]?.getD 0

def back (D : CompactLayout) (i : ℕ) : ℕ × ℕ :=
  D.inverse[i]?.getD (0,0)

def count (D : CompactLayout) : ℕ := D.components.size

def edges (D : CompactLayout) (c : Fin D.count) : ℕ :=
  (D.component c.val).vertices.size-1

abbrev Position (D : CompactLayout) := Σ c : Fin D.count, Fin (D.edges c+1)

local instance {m r p : ℕ} (i : Fin (m-1)) : Decidable (IsFree r p i) := by
  unfold IsFree IsPivot
  infer_instance

/-- Shape validation is deliberately separate from geometry. Missing arrays,
empty components, pivots, out-of-range vertices and inverse entries all fail
before construction of any proof-bearing physical coordinate. -/
def Shape (D : CompactLayout) (m r p : ℕ) : Prop :=
  D.inverse.size=m-1 ∧
  (∀c : Fin D.count, 0<(D.component c.val).vertices.size) ∧
  (∀c : Fin D.count, ∀j : Fin (D.component c.val).vertices.size,
    0<D.vertex c.val j.val ∧ D.vertex c.val j.val<m ∧
    D.vertex c.val j.val≠r ∧ D.vertex c.val j.val≠p) ∧
  (∀i : Fin (m-1), IsFree r p i →
    (D.back i.val).1<D.count ∧
    (D.back i.val).2<(D.component (D.back i.val).1).vertices.size)

instance (D : CompactLayout) (m r p : ℕ) : Decidable (D.Shape m r p) := by
  unfold Shape
  infer_instance

def shapeCheck (D : CompactLayout) (m r p : ℕ) : Bool := decide (D.Shape m r p)

@[simp] theorem shapeCheck_eq_true (D : CompactLayout) (m r p : ℕ) :
    D.shapeCheck m r p=true ↔ D.Shape m r p := by simp [shapeCheck]

private theorem position_lt {D : CompactLayout} {m r p : ℕ}
    (h : D.Shape m r p) (s : D.Position) :
    s.2.val<(D.component s.1.val).vertices.size := by
  have hp:=h.2.1 s.1
  have hj:=s.2.isLt
  dsimp only [edges] at hj
  omega

/-- Bounds are established by the accepted shape; indexing has no trusted
fallback. The total accessors above are merely the data being checked. -/
def forward (D : CompactLayout) {m r p : ℕ} (h : D.Shape m r p)
    (s : D.Position) : FreeVertex m r p := by
  have hv:=h.2.2.1 s.1 ⟨s.2.val,position_lt h s⟩
  dsimp only at hv
  let i : Fin (m-1):=⟨D.vertex s.1.val s.2.val-1,by omega⟩
  refine ⟨i,?_⟩
  unfold IsFree IsPivot
  dsimp only [physical,i]
  omega

/-- Supplied inverse coordinates are bounded before they are made into Fin
indices. The later inverse checks reject omitted or duplicated free vertices. -/
def backward (D : CompactLayout) {m r p : ℕ} (h : D.Shape m r p)
    (v : FreeVertex m r p) : D.Position := by
  have hb:=h.2.2.2 v.val v.property
  let c : Fin D.count:=⟨(D.back v.val.val).1,hb.1⟩
  refine ⟨c,⟨(D.back v.val.val).2,?_⟩⟩
  have hp:=h.2.1 c
  dsimp only [edges,c] at *
  omega

def toData (D : CompactLayout) {m r p : ℕ} (h : D.Shape m r p) :
    FreeLayoutData m r p where
  count:=D.count
  edges:=D.edges
  cycle:=fun c=>(D.component c.val).cycle
  forward:=D.forward h
  backward:=D.backward h

/-- One bounded check guards typed conversion and then reuses the complete
source-exact signed linear checker, including the minimum cycle length. -/
def check (D : CompactLayout) (m r p : ℕ) : Bool :=
  if h : D.Shape m r p then (D.toData h).linearCheck else false

theorem shape_of_check {D : CompactLayout} {m r p : ℕ}
    (h : D.check m r p=true) : D.Shape m r p := by
  unfold check at h
  split at h
  · assumption
  · contradiction

theorem linearCheck_of_check {D : CompactLayout} {m r p : ℕ}
    (h : D.check m r p=true) : (D.toData (shape_of_check h)).linearCheck=true := by
  simpa only [check,dif_pos (shape_of_check h)] using h

def acceptedLayout (D : CompactLayout) {m r p : ℕ} (h : D.check m r p=true) :
    FreeLayout m r p :=
  (D.toData (shape_of_check h)).acceptedLayout
    ((D.toData (shape_of_check h)).linearCheck_sound (linearCheck_of_check h))

/-- This is exactly the previously accepted signed layout contract. In
particular it retains every free coordinate and every genuine edge once. -/
theorem acceptedLayout_valid (D : CompactLayout) {m r p : ℕ}
    (h : D.check m r p=true) : (D.acceptedLayout h).Valid :=
  (D.toData (shape_of_check h)).acceptedLayout_valid _

@[simp] theorem acceptedLayout_count (D : CompactLayout) {m r p : ℕ}
    (h : D.check m r p=true) : (D.acceptedLayout h).count=D.count := rfl

@[simp] theorem acceptedLayout_edges (D : CompactLayout) {m r p : ℕ}
    (h : D.check m r p=true) (c : Fin D.count) :
    (D.acceptedLayout h).edges c=D.edges c := rfl

@[simp] theorem acceptedLayout_vertex (D : CompactLayout) {m r p : ℕ}
    (h : D.check m r p=true) (c : Fin D.count) (j : Fin (D.edges c+1)) :
    ((D.acceptedLayout h).vertex c j).val=D.vertex c.val j.val-1 := rfl

end CompactLayout
end SubmittedGenus.CapFourMass.ExecutableModes
