import Results.Genus.RawGraph.SourceModel
import Results.Genus.RawGraph.Factorization

/-!
# Verified component layouts

A layout is a disjoint cover of all physical vertices by ordered paths/cycles.
The two fixed pivots may appear as singleton paths. A finite coverage predicate
checks that every retained ordinary edge occurs consecutively or as a closing
cycle edge. Extra consecutive pairs have their actual source threshold (zero
for a nonedge), so they cannot introduce unsupported constraints.
-/

namespace SubmittedGenus.RawGraph.LayoutCompiler

open scoped BigOperators
open SourceModel Factorization

structure Layout (m : ℕ) where
  count : ℕ
  edges : Fin count → ℕ
  cycle : Fin count → Bool
  label : (Σ c : Fin count, Fin (edges c + 1)) ≃ Fin (m - 1)

abbrev Layout.Vertex {m : ℕ} (L : Layout m) := Σ c : Fin L.count, Fin (L.edges c + 1)

def Adjacent {m : ℕ} (L : Layout m) (u v : Fin (m - 1)) : Prop :=
  ∃ c : Fin L.count,
    (∃ j : Fin (L.edges c),
      (L.label ⟨c, j.castSucc⟩ = u ∧ L.label ⟨c, j.succ⟩ = v) ∨
      (L.label ⟨c, j.castSucc⟩ = v ∧ L.label ⟨c, j.succ⟩ = u)) ∨
    (L.cycle c = true ∧
      ((L.label ⟨c, Fin.last (L.edges c)⟩ = u ∧ L.label ⟨c, 0⟩ = v) ∨
      (L.label ⟨c, Fin.last (L.edges c)⟩ = v ∧ L.label ⟨c, 0⟩ = u)))

/-- Source-complete edge coverage. This is a finite, decidable property of the
layout data and the original reflection targets, not a trusted graph oracle. -/
def Covers {m : ℕ} (L : Layout m) (r p a : ℕ) : Prop :=
  ∀ u v, 0 < edgeBound r p a u v → Adjacent L u v

instance {m : ℕ} (L : Layout m) (r p a : ℕ) : Decidable (Covers L r p a) := by
  unfold Covers Adjacent
  infer_instance

/-- Direct local source constraints on one ordered component. -/
def ComponentAllowed {m : ℕ} (L : Layout m) (r p a : ℕ) (c : Fin L.count)
    (x : Fin (L.edges c + 1) → Fin (a + 1)) : Prop :=
  (∀ j, Domain r p a (L.label ⟨c, j⟩) (x j).val) ∧
  (∀ j : Fin (L.edges c),
    edgeBound r p a (L.label ⟨c, j.castSucc⟩) (L.label ⟨c, j.succ⟩) ≤
      (x j.castSucc).val + (x j.succ).val) ∧
  (L.cycle c = true →
    edgeBound r p a (L.label ⟨c, Fin.last (L.edges c)⟩) (L.label ⟨c, 0⟩) ≤
      (x (Fin.last (L.edges c))).val + (x 0).val)

instance {m : ℕ} (L : Layout m) (r p a : ℕ) (c : Fin L.count)
    (x : Fin (L.edges c + 1) → Fin (a + 1)) : Decidable (ComponentAllowed L r p a c x) := by
  unfold ComponentAllowed
  infer_instance

/-- All source binary inequalities, with both edge orientations admitted. -/
theorem admissible_edge_all {m r p a : ℕ} {x : Word m}
    (h : Admissible r p a x) (i j : Fin (m - 1)) :
    edgeBound r p a i j ≤ x i + x j := by
  rcases lt_trichotomy i j with hij | rfl | hij
  · exact h.2.2 i j hij
  · simp [edgeBound]
  · simpa [edgeBound_symm, Nat.add_comm] using h.2.2 j i hij

/-- A valid layout covers exactly the complete raw source constraints. -/
theorem raw_iff_components {m r p a : ℕ} (L : Layout m)
    (hp : Parameters m r p a) (hc : Covers L r p a)
    (x : Fin (m - 1) → Fin (a + 1)) :
    RawAdmissible r p a (boundedWord x) ↔
      ∀ c, ComponentAllowed L r p a c (fun j => x (L.label ⟨c, j⟩)) := by
  rw [raw_iff_compiled]
  constructor
  · intro h c
    exact ⟨fun j => h.2.1 _, fun j => admissible_edge_all h _ _,
      fun _ => admissible_edge_all h _ _⟩
  · intro h
    refine ⟨hp, ?_, ?_⟩
    · intro i
      obtain ⟨⟨c, j⟩, rfl⟩ := L.label.surjective i
      exact (h c).1 j
    · intro i j _
      by_cases he : edgeBound r p a i j = 0
      · simp [he]
      have hpos : 0 < edgeBound r p a i j := Nat.pos_of_ne_zero he
      obtain ⟨c, hedge | hclose⟩ := hc i j hpos
      · obtain ⟨k, hor | hor⟩ := hedge
        · obtain ⟨rfl, rfl⟩ := hor
          exact (h c).2.1 k
        · obtain ⟨rfl, rfl⟩ := hor
          simpa [edgeBound_symm, boundedWord, Nat.add_comm] using (h c).2.1 k
      · obtain ⟨hcyc, hor | hor⟩ := hclose
        · obtain ⟨rfl, rfl⟩ := hor
          exact (h c).2.2 hcyc
        · obtain ⟨rfl, rfl⟩ := hor
          simpa [edgeBound_symm, boundedWord, Nat.add_comm] using (h c).2.2 hcyc

/-- A physical vertex weight, with all unary restrictions including loops. -/
noncomputable def vertexWeight {m : ℕ} (r p a : ℕ) (i : Fin (m - 1))
    (value : Fin (a + 1)) : Polynomial ℕ :=
  if Domain r p a i value.val then Polynomial.X ^ value.val else 0

/-- A binary compatibility factor has no extra vertex monomial. -/
noncomputable def edgeWeight {m : ℕ} (r p a : ℕ) (i j : Fin (m - 1))
    (left right : Fin (a + 1)) : Polynomial ℕ :=
  if edgeBound r p a i j ≤ left.val + right.val then 1 else 0

noncomputable def componentTerm {m : ℕ} (L : Layout m) (r p a : ℕ) (c : Fin L.count)
    (x : Fin (L.edges c + 1) → Fin (a + 1)) : Polynomial ℕ :=
  (∏ j, vertexWeight r p a (L.label ⟨c, j⟩) (x j)) *
  (∏ j : Fin (L.edges c), edgeWeight r p a
    (L.label ⟨c, j.castSucc⟩) (L.label ⟨c, j.succ⟩) (x j.castSucc) (x j.succ)) *
  (if L.cycle c = true then edgeWeight r p a
    (L.label ⟨c, Fin.last (L.edges c)⟩) (L.label ⟨c, 0⟩)
    (x (Fin.last (L.edges c))) (x 0) else 1)

/-- Direct assignment semantics for a component. Every coordinate contributes
one monomial whether or not it is an endpoint or carries a self-pair. -/
theorem componentTerm_eq_gate {m : ℕ} (L : Layout m) (r p a : ℕ) (c : Fin L.count)
    (x : Fin (L.edges c + 1) → Fin (a + 1)) :
    componentTerm L r p a c x =
      if ComponentAllowed L r p a c x then
        (Polynomial.X : Polynomial ℕ) ^ (∑ j, (x j).val) else 0 := by
  classical
  unfold componentTerm vertexWeight edgeWeight
  rw [prod_gated_powers, prod_gate]
  simp only [Finset.prod_const_one]
  unfold ComponentAllowed
  split_ifs <;> simp_all

/-- Vertex weights as indexed by the transfer routine. Invalid indices are
never reached by the corresponding source term. -/
noncomputable def transferVertices {m : ℕ} (L : Layout m) (r p a : ℕ)
    (c : Fin L.count) (j : ℕ) (value : Fin (a + 1)) : Polynomial ℕ :=
  if h : j < L.edges c + 1 then vertexWeight r p a (L.label ⟨c, ⟨j, h⟩⟩) value else 0

noncomputable def transferEdges {m : ℕ} (L : Layout m) (r p a : ℕ)
    (c : Fin L.count) (j : ℕ) (left right : Fin (a + 1)) : Polynomial ℕ :=
  if h : j < L.edges c then edgeWeight r p a
    (L.label ⟨c, (⟨j, h⟩ : Fin (L.edges c)).castSucc⟩)
    (L.label ⟨c, (⟨j, h⟩ : Fin (L.edges c)).succ⟩) left right else 1

noncomputable def transferClose {m : ℕ} (L : Layout m) (r p a : ℕ)
    (c : Fin L.count) (last first : Fin (a + 1)) : Polynomial ℕ :=
  edgeWeight r p a (L.label ⟨c, Fin.last (L.edges c)⟩) (L.label ⟨c, 0⟩) last first

@[simp] theorem transferVertices_fin {m : ℕ} (L : Layout m) (r p a : ℕ)
    (c : Fin L.count) (j : Fin (L.edges c + 1)) (value : Fin (a + 1)) :
    transferVertices L r p a c j.val value = vertexWeight r p a (L.label ⟨c, j⟩) value := by
  simp only [transferVertices, dif_pos j.isLt]

@[simp] theorem transferEdges_fin {m : ℕ} (L : Layout m) (r p a : ℕ)
    (c : Fin L.count) (j : Fin (L.edges c)) (left right : Fin (a + 1)) :
    transferEdges L r p a c j.val left right = edgeWeight r p a
      (L.label ⟨c, j.castSucc⟩) (L.label ⟨c, j.succ⟩) left right := by
  simp only [transferEdges, dif_pos j.isLt]

noncomputable def componentRun {m : ℕ} (L : Layout m) (r p a : ℕ)
    (c : Fin L.count) : Polynomial ℕ :=
  if L.cycle c = true then Transfer.cycleRun (L.edges c)
    (transferVertices L r p a c) (transferEdges L r p a c) (transferClose L r p a c)
  else Transfer.pathRun (L.edges c) (transferVertices L r p a c) (transferEdges L r p a c)

/-- The original path/cycle transfer computes each complete component source. -/
theorem componentRun_eq_source {m : ℕ} (L : Layout m) (r p a : ℕ)
    (c : Fin L.count) : componentRun L r p a c =
      ∑ x : Fin (L.edges c + 1) → Fin (a + 1), componentTerm L r p a c x := by
  classical
  unfold componentRun
  split_ifs with hc
  · rw [Transfer.cycleRun_eq_source]
    unfold Transfer.cycleSource
    apply Finset.sum_congr rfl
    intro x _
    simp only [Transfer.sourceTerm, componentTerm, transferVertices_fin, transferEdges_fin,
      transferClose, hc, if_true]
  · rw [Transfer.pathRun_eq_source]
    unfold Transfer.pathSource
    apply Finset.sum_congr rfl
    intro x _
    simp only [Transfer.sourceTerm, componentTerm, transferVertices_fin, transferEdges_fin,
      hc, Bool.false_eq_true, if_false]

/-- Verified raw-graph compilation: a source-complete vertex layout computes the
exact original raw polynomial by multiplying path/cycle transfer polynomials.
No exponential assignment enumeration is used in `componentRun`. -/
theorem rawPolynomial_eq_components {m r p a : ℕ} (L : Layout m)
    (hp : Parameters m r p a) (hc : Covers L r p a) :
    rawPolynomial m r p a = ∏ c, componentRun L r p a c := by
  classical
  unfold rawPolynomial
  rw [sum_assignments_reindex L.label]
  simp_rw [componentRun_eq_source]
  rw [← sum_product_components]
  apply Finset.sum_congr rfl
  intro y _
  simp_rw [componentTerm_eq_gate]
  rw [prod_gated_powers]
  have he : RawAdmissible r p a (boundedWord (fun v => y (L.label.symm v))) ↔
      ∀ c, ComponentAllowed L r p a c (fun j => y ⟨c, j⟩) := by
    simpa using raw_iff_components L hp hc (fun v => y (L.label.symm v))
  have hg : genus (boundedWord (fun v => y (L.label.symm v))) =
      ∑ c, ∑ j, (y ⟨c, j⟩).val := by
    simpa [genus, boundedWord] using sum_cost_reindex L.label
      (boundedWord (fun v => y (L.label.symm v)))
  simp only [he, hg]
  split_ifs <;> rfl

end SubmittedGenus.RawGraph.LayoutCompiler
