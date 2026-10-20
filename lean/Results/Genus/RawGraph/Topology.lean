import Results.Genus.RawGraph.Incidence
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# Finite graphs of degree at most two

Primary reuse: Mathlib's finite longest-path theorem. The additional arguments
below prove that a longest path in a connected degree-two graph contains every
vertex, and all edges are consecutive or join its two endpoints. Triangle-free
source graphs therefore have path components or cycles of length at least four.
-/

namespace SubmittedGenus.RawGraph.Topology

open SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- A cardinality-free formulation of degree at most two. -/
def NoThirdNeighbor : Prop :=
  ∀ u v w t, G.Adj u v → G.Adj u w → v ≠ w → G.Adj u t → t = v ∨ t = w

def NoTriangle : Prop := ∀ u v w, G.Adj u v → G.Adj v w → G.Adj w u → False

/-- Maximality among all simple paths, supplied by the finite Mathlib theorem. -/
def Longest {u v : V} (p : G.Walk u v) : Prop :=
  ∀ u' v' (q : G.Walk u' v'), q.IsPath → q.length ≤ p.length

theorem path_internal_neighbors {u v : V} {p : G.Walk u v}
    (hd : NoThirdNeighbor G) (hp : p.IsPath) {k : ℕ}
    (hk0 : 0 < k) (hkn : k < p.length) {w : V} (hw : G.Adj (p.getVert k) w) :
    w = p.getVert (k - 1) ∨ w = p.getVert (k + 1) := by
  have hprev : G.Adj (p.getVert k) (p.getVert (k - 1)) := by
    have hh := (p.adj_getVert_succ (i := k - 1) (by omega)).symm
    simpa [Nat.sub_add_cancel hk0] using hh
  have hnext := p.adj_getVert_succ hkn
  have hne : p.getVert (k - 1) ≠ p.getVert (k + 1) := by
    intro he
    have hh := hp.getVert_injOn (by simp; omega : k - 1 ∈ {i | i ≤ p.length})
      (by simp; omega : k + 1 ∈ {i | i ≤ p.length}) he
    omega
  exact hd _ _ _ _ hprev hnext hne hw

/-- A longest degree-two path is closed under all graph neighbors. -/
theorem longest_path_closed {u v : V} {p : G.Walk u v}
    (hd : NoThirdNeighbor G) (hp : p.IsPath) (hl : Longest G p)
    {x y : V} (hx : x ∈ p.support) (hxy : G.Adj x y) : y ∈ p.support := by
  by_contra hy
  obtain ⟨k, hk, hkn⟩ := Walk.mem_support_iff_exists_getVert.mp hx
  subst x
  by_cases hk0 : k = 0
  · have hadj : G.Adj y u := by simpa [hk0] using hxy.symm
    have hh := hl y v (p.cons hadj) (hp.cons hy)
    simp only [Walk.length_cons] at hh
    omega
  by_cases hkl : k = p.length
  · have hadj : G.Adj v y := by simpa [hkl] using hxy
    have hh := hl u y (p.concat hadj) (hp.concat hy hadj)
    simp only [Walk.length_concat] at hh
    omega
  have hh := path_internal_neighbors G hd hp (by omega) (by omega) hxy
  rcases hh with rfl | rfl <;> exact hy (p.getVert_mem_support _)

/-- Neighbor-closed sets contain every vertex reachable from one of their vertices. -/
theorem reachable_mem_closed {s : Set V}
    (hc : ∀ ⦃u v⦄, u ∈ s → G.Adj u v → v ∈ s)
    {u v : V} (hu : u ∈ s) (hr : G.Reachable u v) : v ∈ s := by
  obtain ⟨w⟩ := hr
  induction w with
  | nil => exact hu
  | @cons u w v hadj q ih => exact ih (hc hu hadj)

/-- In a connected finite degree-two graph, a longest path spans all vertices. -/
theorem longest_path_spans (hconn : G.Connected) {u v : V} {p : G.Walk u v}
    (hd : NoThirdNeighbor G) (hp : p.IsPath) (hl : Longest G p) :
    ∀ x : V, x ∈ p.support := by
  intro x
  exact reachable_mem_closed G (s := {x | x ∈ p.support})
    (fun _ _ hx hxy => longest_path_closed G hd hp hl hx hxy)
    p.start_mem_support (hconn.preconnected u x)

/-- Every edge in a spanning simple degree-two path is consecutive or joins
its two endpoints. This also excludes every possible chord. -/
theorem path_edge_indices {u v : V} {p : G.Walk u v}
    (hd : NoThirdNeighbor G) (hp : p.IsPath) {i j : ℕ}
    (hi : i ≤ p.length) (hj : j ≤ p.length)
    (hij : G.Adj (p.getVert i) (p.getVert j)) :
    i + 1 = j ∨ j + 1 = i ∨ (i = 0 ∧ j = p.length) ∨ (j = 0 ∧ i = p.length) := by
  have hne : i ≠ j := by intro he; subst j; exact hij.ne rfl
  by_cases hii : 0 < i ∧ i < p.length
  · have h := path_internal_neighbors G hd hp hii.1 hii.2 hij
    rcases h with h | h
    · have hh := hp.getVert_injOn (by simpa using hj) (by simp; omega) h
      omega
    · have hh := hp.getVert_injOn (by simpa using hj) (by simp; omega) h
      omega
  by_cases hjj : 0 < j ∧ j < p.length
  · have h := path_internal_neighbors G hd hp hjj.1 hjj.2 hij.symm
    rcases h with h | h
    · have hh := hp.getVert_injOn (by simpa using hi) (by simp; omega) h
      omega
    · have hh := hp.getVert_injOn (by simpa using hi) (by simp; omega) h
      omega
  omega

/-- An ordered connected component with an exact path/cycle adjacency rule. -/
structure OrderedComponent where
  edges : ℕ
  label : Fin (edges + 1) ≃ V
  cycle : Bool
  cycle_min : cycle = true → 3 ≤ edges
  adjacent_iff : ∀ i j, G.Adj (label i) (label j) ↔
    i.val + 1 = j.val ∨ j.val + 1 = i.val ∨
      (cycle = true ∧ ((i.val = 0 ∧ j.val = edges) ∨ (j.val = 0 ∧ i.val = edges)))

/-- All-parameter existence of a strict path/cycle ordering. The only selected
object is a finite longest path, whose coverage and adjacency are proved above. -/
theorem exists_orderedComponent [Finite V] (hconn : G.Connected)
    (hd : NoThirdNeighbor G) (ht : NoTriangle G) : Nonempty (OrderedComponent G) := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  letI : Nonempty V := hconn.nonempty
  obtain ⟨u, v, p, hp, hl⟩ := Walk.exists_isPath_forall_isPath_length_le_length G
  have hlong : Longest G p := hl
  have hspan := longest_path_spans G hconn hd hp hlong
  let label : Fin (p.length + 1) ≃ V := Equiv.ofBijective (fun i => p.getVert i.val) (by
    constructor
    · intro i j hij
      apply Fin.ext
      exact hp.getVert_injOn (by simp; omega) (by simp; omega) hij
    · intro x
      obtain ⟨k, hk, hkn⟩ := Walk.mem_support_iff_exists_getVert.mp (hspan x)
      exact ⟨⟨k, by omega⟩, hk⟩)
  let cyc : Bool := decide (2 ≤ p.length ∧ G.Adj u v)
  have hcyc : cyc = true ↔ 2 ≤ p.length ∧ G.Adj u v := by simp [cyc]
  refine ⟨⟨p.length, label, cyc, ?_, ?_⟩⟩
  · intro hc
    obtain ⟨hn, hadj⟩ := hcyc.mp hc
    by_contra hsmall
    have he : p.length = 2 := by omega
    have h01 := p.adj_getVert_succ (i := 0) (by omega)
    have h12 := p.adj_getVert_succ (i := 1) (by omega)
    have h20 : G.Adj (p.getVert 2) (p.getVert 0) := by simpa [← he] using hadj.symm
    exact ht _ _ _ h01 h12 h20
  · intro i j
    change G.Adj (p.getVert i.val) (p.getVert j.val) ↔ _
    have hi := i.isLt
    have hj := j.isLt
    constructor
    · intro hadj
      have hh := path_edge_indices G hd hp (by omega) (by omega) hadj
      rcases hh with hh | hh | hh | hh
      · exact Or.inl hh
      · exact Or.inr (Or.inl hh)
      · by_cases hn : p.length ≤ 1
        · have hne := hadj.ne
          have hnpos : 0 < p.length := by
            by_contra hn0
            have he : i.val = j.val := by omega
            exact hne (congrArg p.getVert he)
          left
          omega
        · right; right
          refine ⟨hcyc.mpr ⟨by omega, ?_⟩, Or.inl hh⟩
          simpa [hh.1, hh.2] using hadj
      · by_cases hn : p.length ≤ 1
        · have hne := hadj.ne
          have hnpos : 0 < p.length := by
            by_contra hn0
            have he : i.val = j.val := by omega
            exact hne (congrArg p.getVert he)
          right; left
          omega
        · right; right
          refine ⟨hcyc.mpr ⟨by omega, ?_⟩, Or.inr hh⟩
          simpa [hh.1, hh.2] using hadj.symm
    · rintro (hadj | hadj | ⟨hc, hends | hends⟩)
      · simpa [hadj] using p.adj_getVert_succ (i := i.val) (by omega)
      · simpa [hadj] using (p.adj_getVert_succ (i := j.val) (by omega)).symm
      · simpa [hends.1, hends.2] using (hcyc.mp hc).2
      · simpa [hends.1, hends.2] using (hcyc.mp hc).2.symm

end SubmittedGenus.RawGraph.Topology
