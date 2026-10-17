import Results.Genus.RawGraph.Layout

namespace SubmittedGenus.RawGraph.LayoutCompiler

private def sampleEdges : Fin 3 → ℕ := ![0, 0, 2]
private abbrev SampleVertex := Σ c : Fin 3, Fin (sampleEdges c + 1)

private def sampleLabel : SampleVertex ≃ Fin 5 where
  toFun v := if v.1 = 0 then 0 else if v.1 = 1 then 1
    else if v.2.val = 0 then 3 else if v.2.val = 1 then 2 else 4
  invFun := ![⟨0, 0⟩, ⟨1, 0⟩, ⟨2, 1⟩, ⟨2, 0⟩, ⟨2, 2⟩]
  left_inv := by decide
  right_inv := by decide

/-- Two fixed singleton pivots and the free path4--3--5, with a carry loop at4. -/
def sampleLayout : Layout 6 where
  count := 3
  edges := sampleEdges
  cycle := fun _ => false
  label := sampleLabel

/-- Kernel-checked coverage of every original retained binary edge. -/
theorem sampleLayout_covers : Covers sampleLayout 1 2 4 := by decide

theorem sampleLayout_source : rawPolynomial 6 1 2 4 =
    ∏ c, componentRun sampleLayout 1 2 4 c :=
  rawPolynomial_eq_components sampleLayout (by decide) sampleLayout_covers

private theorem sample_vertex_pivot0 (v : Fin 5) :
    transferVertices sampleLayout 1 2 4 (0 : Fin 3) 0 v =
      if v.val = 4 then (Polynomial.X : Polynomial ℕ) ^ 4 else 0 := by
  fin_cases v <;> rfl

private theorem sample_vertex_pivot1 (v : Fin 5) :
    transferVertices sampleLayout 1 2 4 (1 : Fin 3) 0 v =
      if v.val = 4 then (Polynomial.X : Polynomial ℕ) ^ 4 else 0 := by
  fin_cases v <;> rfl

private theorem sample_vertex_loop (v : Fin 5) :
    transferVertices sampleLayout 1 2 4 (2 : Fin 3) 0 v =
      if v.val = 2 ∨ v.val = 3 then (Polynomial.X : Polynomial ℕ) ^ v.val else 0 := by
  fin_cases v <;> rfl

private theorem sample_vertex_middle (v : Fin 5) :
    transferVertices sampleLayout 1 2 4 (2 : Fin 3) 1 v =
      if 1 ≤ v.val ∧ v.val ≤ 3 then (Polynomial.X : Polynomial ℕ) ^ v.val else 0 := by
  fin_cases v <;> rfl

private theorem sample_vertex_end (v : Fin 5) :
    transferVertices sampleLayout 1 2 4 (2 : Fin 3) 2 v =
      if 1 ≤ v.val ∧ v.val ≤ 3 then (Polynomial.X : Polynomial ℕ) ^ v.val else 0 := by
  fin_cases v <;> rfl

private theorem sample_edge_first (u v : Fin 5) :
    transferEdges sampleLayout 1 2 4 (2 : Fin 3) 0 u v =
      if 3 ≤ u.val + v.val then 1 else (0 : Polynomial ℕ) := by rfl

private theorem sample_edge_second (u v : Fin 5) :
    transferEdges sampleLayout 1 2 4 (2 : Fin 3) 1 u v =
      if 3 ≤ u.val + v.val then 1 else (0 : Polynomial ℕ) := by rfl

private theorem sample_component_zero : componentRun sampleLayout 1 2 4 (0 : Fin 3) =
    (Polynomial.X : Polynomial ℕ) ^ 4 := by
  change (∑ v : Fin 5, transferVertices sampleLayout 1 2 4 (0 : Fin 3) 0 v * 1) = _
  simp [sample_vertex_pivot0, Fin.sum_univ_succ]

private theorem sample_component_one : componentRun sampleLayout 1 2 4 (1 : Fin 3) =
    (Polynomial.X : Polynomial ℕ) ^ 4 := by
  change (∑ v : Fin 5, transferVertices sampleLayout 1 2 4 (1 : Fin 3) 0 v * 1) = _
  simp [sample_vertex_pivot1, Fin.sum_univ_succ]

private theorem sample_component_two : componentRun sampleLayout 1 2 4 (2 : Fin 3) =
    2 * (Polynomial.X : Polynomial ℕ) ^ 5 + 5 * Polynomial.X ^ 6 +
      5 * Polynomial.X ^ 7 + 3 * Polynomial.X ^ 8 + Polynomial.X ^ 9 := by
  change Transfer.pathRun 2 (transferVertices sampleLayout 1 2 4 (2 : Fin 3))
    (transferEdges sampleLayout 1 2 4 (2 : Fin 3)) = _
  simp [Transfer.pathRun, Transfer.run, Transfer.shift, sample_vertex_loop,
    sample_vertex_middle, sample_vertex_end, sample_edge_first, sample_edge_second,
    Fin.sum_univ_succ]
  ring

/-- Complete original source evaluation through path transfer, with both a
nontrivial binary constraint and a loop at an endpoint. -/
theorem sampleLayout_polynomial : rawPolynomial 6 1 2 4 =
    2 * Polynomial.X ^ 13 + 5 * Polynomial.X ^ 14 + 5 * Polynomial.X ^ 15 +
      3 * Polynomial.X ^ 16 + Polynomial.X ^ 17 := by
  rw [sampleLayout_source]
  change (∏ c : Fin 3, componentRun sampleLayout 1 2 4 c) = _
  rw [Fin.prod_univ_three, sample_component_zero, sample_component_one, sample_component_two]
  ring

end SubmittedGenus.RawGraph.LayoutCompiler
