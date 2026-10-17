import Results.Genus.RawGraph
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

/-!
# Submitted-paper carry-reflection geometry

This file concerns the original carry graph before deletion of its pivot port.
Coordinates are shifted by r. Its vertex interval is 0 < x < N, and its
reflections are N-x and N+d-x. All facts are proved from these actual formulas.
A residue-list normal form retains loops instead of discarding fixed points.
-/

namespace SubmittedGenus.FixedPivot

/-- Shifted carry vertices, with the pivot temporarily retained. -/
def CarryVertex (N x : ℕ) : Prop := 0 < x ∧ x < N

def reflectF (N x : ℕ) : ℕ := N - x

def reflectG (N d x : ℕ) : ℕ := N + d - x

/-- Both targets, including a self-pair, are genuine carry incidences. -/
def CarryIncidence (N d x y : ℕ) : Prop := x + y = N ∨ x + y = N + d

lemma physical_carry_iff {m r p x y : ℕ} (hrp : r ≤ p) (hrm : r ≤ m) :
    ((r+x)+(r+y) = m+r ∨ (r+x)+(r+y) = m+p) ↔
      CarryIncidence (m-r) (p-r) x y := by
  unfold CarryIncidence
  omega

lemma reflectF_vertex {N x : ℕ} (hx : CarryVertex N x) :
    CarryVertex N (reflectF N x) := by
  unfold CarryVertex reflectF at *
  omega

lemma reflectF_involutive {N x : ℕ} (hx : CarryVertex N x) :
    reflectF N (reflectF N x) = x := by
  unfold CarryVertex reflectF at *
  omega

/-- Exactly the first d shifted vertices have no second incidence. -/
lemma reflectG_vertex_iff {N d x : ℕ} (hx : CarryVertex N x) :
    CarryVertex N (reflectG N d x) ↔ d < x := by
  unfold CarryVertex reflectG at *
  omega

lemma reflectG_involutive {N d x : ℕ} (hx : CarryVertex N x) (hdx : d < x) :
    reflectG N d (reflectG N d x) = x := by
  unfold CarryVertex reflectG at *
  omega

lemma incidence_iff_reflections {N d x y : ℕ}
    (hx : CarryVertex N x) (hy : CarryVertex N y) :
    CarryIncidence N d x y ↔ y = reflectF N x ∨ y = reflectG N d x := by
  unfold CarryVertex CarryIncidence reflectF reflectG at *
  omega

lemma distinct_reflections {N d x : ℕ} (hd : 0 < d) (hx : CarryVertex N x) :
    reflectF N x ≠ reflectG N d x := by
  unfold CarryVertex reflectF reflectG at *
  omega

/-- Alternating the two actual reflections translates one full residue step. -/
lemma reflectG_reflectF {N d x : ℕ} (hx : CarryVertex N x) :
    reflectG N d (reflectF N x) = x + d := by
  unfold CarryVertex reflectF reflectG at *
  omega

lemma reflectF_reflectG {N d x : ℕ} (hx : CarryVertex N x) (hdx : d < x) :
    reflectF N (reflectG N d x) = x - d := by
  unfold CarryVertex reflectF reflectG at *
  omega

/-- Source assumption m>2p implies every residue list has at least two vertices. -/
lemma at_least_two_vertices {m r p : ℕ} (hrp : r < p) (hmp : 2*p < m)
    {a : ℕ} (ha : 1 ≤ a) (had : a ≤ p-r) :
    CarryVertex (m-r) a ∧ CarryVertex (m-r) (a+(p-r)) := by
  unfold CarryVertex
  omega

/-- Complete arithmetic data of a reflected pair of residue lists. -/
structure ResiduePair (N d : ℕ) where
  a : ℕ
  b : ℕ
  n : ℕ
  d_pos : 0 < d
  a_pos : 0 < a
  a_le : a ≤ d
  b_pos : 0 < b
  b_le : b ≤ d
  n_pos : 0 < n
  endpoint : a + (n-1)*d + b = N

namespace ResiduePair

variable {N d : ℕ} (L : ResiduePair N d)

def left (k : ℕ) : ℕ := L.a + k*d

def right (k : ℕ) : ℕ := L.b + k*d

lemma left_vertex {k : ℕ} (hk : k < L.n) : CarryVertex N (L.left k) := by
  have hs : k*d ≤ (L.n-1)*d := Nat.mul_le_mul_right d (by omega)
  have he := L.endpoint
  have ha := L.a_pos
  have hb := L.b_pos
  unfold CarryVertex left
  omega

lemma right_vertex {k : ℕ} (hk : k < L.n) : CarryVertex N (L.right k) := by
  have hs : k*d ≤ (L.n-1)*d := Nat.mul_le_mul_right d (by omega)
  have he := L.endpoint
  have ha := L.a_pos
  have hb := L.b_pos
  unfold CarryVertex right
  omega

/-- There are exactly n vertices in the a-residue list. -/
lemma left_vertex_iff (k : ℕ) : CarryVertex N (L.left k) ↔ k < L.n := by
  constructor
  · intro hk
    have he := L.endpoint
    have hb := L.b_le
    have hd := L.d_pos
    have hn := L.n_pos
    by_contra hn'
    have hs : L.n*d ≤ k*d := Nat.mul_le_mul_right d (by omega)
    have he' : L.n*d = (L.n-1)*d+d := by
      have heq : L.n = L.n-1+1 := by omega
      calc L.n*d = (L.n-1+1)*d := by rw [← heq]
           _ = (L.n-1)*d+d := by ring
    unfold CarryVertex left at hk
    omega
  · exact L.left_vertex

lemma right_vertex_iff (k : ℕ) : CarryVertex N (L.right k) ↔ k < L.n := by
  constructor
  · intro hk
    have he := L.endpoint
    have ha := L.a_le
    have hd := L.d_pos
    have hn := L.n_pos
    by_contra hn'
    have hs : L.n*d ≤ k*d := Nat.mul_le_mul_right d (by omega)
    have he' : L.n*d = (L.n-1)*d+d := by
      have heq : L.n = L.n-1+1 := by omega
      calc L.n*d = (L.n-1+1)*d := by rw [← heq]
           _ = (L.n-1)*d+d := by ring
    unfold CarryVertex right at hk
    omega
  · exact L.right_vertex

/-- F reverses the two lists, including its possible middle loop. -/
lemma reflectF_left {k : ℕ} (hk : k < L.n) :
    reflectF N (L.left k) = L.right (L.n-1-k) := by
  have he := L.endpoint
  have hm : (L.n-1-k)*d + k*d = (L.n-1)*d := by
    rw [← Nat.add_mul]
    congr 1
    omega
  unfold reflectF left right
  omega

/-- G reverses the lists with an index offset, and is present exactly after the port. -/
lemma reflectG_left {k : ℕ} (hk0 : 0 < k) (hk : k < L.n) :
    reflectG N d (L.left k) = L.right (L.n-k) := by
  have he := L.endpoint
  have hn := L.n_pos
  have hm : (L.n-k)*d + k*d = (L.n-1)*d+d := by
    have heq : L.n-k+k = L.n-1+1 := by omega
    calc (L.n-k)*d+k*d = (L.n-k+k)*d := by ring
         _ = (L.n-1+1)*d := by rw [heq]
         _ = (L.n-1)*d+d := by ring
  unfold reflectG left right
  omega

lemma port_iff {k : ℕ} (hk : k < L.n) : L.left k ≤ d ↔ k = 0 := by
  have ha := L.a_pos
  have had := L.a_le
  have hd := L.d_pos
  unfold left
  constructor
  · intro h
    by_contra hn
    have : d ≤ k*d := by simpa using Nat.mul_le_mul_right d (show 1 ≤ k by omega)
    omega
  · rintro rfl
    simpa using had

/-- Increasing m by d preserves both ports and adds one vertex to each list. -/
def extend : ResiduePair (N+d) d where
  a := L.a
  b := L.b
  n := L.n+1
  d_pos := L.d_pos
  a_pos := L.a_pos
  a_le := L.a_le
  b_pos := L.b_pos
  b_le := L.b_le
  n_pos := by omega
  endpoint := by
    have hn := L.n_pos
    have he := L.endpoint
    have hm : L.n*d = (L.n-1)*d+d := by
      have heq : L.n = L.n-1+1 := by omega
      calc L.n*d = (L.n-1+1)*d := by rw [← heq]
           _ = (L.n-1)*d+d := by ring
    simp only [Nat.add_sub_cancel]
    omega

@[simp] lemma extend_a : L.extend.a = L.a := rfl
@[simp] lemma extend_b : L.extend.b = L.b := rfl
@[simp] lemma extend_n : L.extend.n = L.n+1 := rfl

end ResiduePair

/-- Residue representatives use the paper's convention 1,...,d, not 0,...,d-1. -/
def residuePort (d x : ℕ) : ℕ := (x-1)%d+1

def residueIndex (d x : ℕ) : ℕ := (x-1)/d

lemma residuePort_bounds {d x : ℕ} (hd : 0 < d) :
    1 ≤ residuePort d x ∧ residuePort d x ≤ d := by
  have hm := Nat.mod_lt (x-1) hd
  unfold residuePort
  omega

/-- Every shifted vertex occurs in a residue list. -/
lemma residue_decomposition {d x : ℕ} (hx : 0 < x) :
    x = residuePort d x + residueIndex d x*d := by
  have he := Nat.mod_add_div (x-1) d
  rw [Nat.mul_comm d] at he
  unfold residuePort residueIndex
  omega

/-- The second member of a reflected pair and its common length are canonical. -/
def residuePair (N d a : ℕ) (hd : 0 < d) (ha : 0 < a)
    (had : a ≤ d) (haN : a < N) : ResiduePair N d where
  a := a
  b := (N-1-a)%d+1
  n := (N-1-a)/d+1
  d_pos := hd
  a_pos := ha
  a_le := had
  b_pos := by omega
  b_le := by have hm := Nat.mod_lt (N-1-a) hd; omega
  n_pos := Nat.succ_pos _
  endpoint := by
    have he := Nat.mod_add_div (N-1-a) d
    rw [Nat.mul_comm d] at he
    simp only [Nat.add_sub_cancel]
    omega

/-- This is a complete residue-list presentation of every original carry vertex. -/
theorem carry_vertex_in_canonical_list {N d x : ℕ} (hd : 0 < d)
    (hx : CarryVertex N x) :
    ∃ (a : ℕ) (ha : 0 < a) (had : a ≤ d) (haN : a < N),
      let L := residuePair N d a hd ha had haN
      x = L.left (residueIndex d x) ∧ residueIndex d x < L.n := by
  have hp := residuePort_bounds (x := x) hd
  have he := residue_decomposition (d := d) hx.1
  have hxN := hx.2
  have haN : residuePort d x < N := by omega
  refine ⟨residuePort d x, by omega, hp.2, haN, ?_⟩
  dsimp only
  constructor
  · exact he
  · apply (ResiduePair.left_vertex_iff _ _).1
    simpa only [ResiduePair.left, residuePair, ← he] using hx

end SubmittedGenus.FixedPivot
