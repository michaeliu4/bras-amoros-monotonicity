import Results.Genus.RawGraph.Transfer

/-!
# Original raw-graph domain and edge extraction

Matches `graph`, `domain(...,0)`, and `bound` in the immutable submitted
`packed_relaxation.cpp`. Loops raise the lower endpoint of one vertex domain;
ordinary edges never receive an extra vertex weight. Pivots have fixed values.
-/

namespace SubmittedGenus.RawGraph.SourceModel

open scoped BigOperators

/-- A loop from a noncarried target. -/
def StrongLoop {m : ℕ} (r p : ℕ) (i : Fin (m - 1)) : Prop :=
  2 * physical i = r ∨ 2 * physical i = p

/-- A loop from a carried target. -/
def CarryLoop {m : ℕ} (r p : ℕ) (i : Fin (m - 1)) : Prop :=
  2 * physical i = m + r ∨ 2 * physical i = m + p

instance {m r p : ℕ} (i : Fin (m - 1)) : Decidable (StrongLoop r p i) := by
  unfold StrongLoop
  infer_instance

instance {m r p : ℕ} (i : Fin (m - 1)) : Decidable (CarryLoop r p i) := by
  unfold CarryLoop
  infer_instance

/-- Original alphabet upper endpoint at a free physical coordinate. -/
def upper {m : ℕ} (r a : ℕ) (i : Fin (m - 1)) : ℕ :=
  if physical i < r then a else a - 1

/-- Original lower endpoint, including every strong/carried self-pair. -/
def lower {m : ℕ} (r p a : ℕ) (i : Fin (m - 1)) : ℕ :=
  max 1 (max (if StrongLoop r p i then (a + 1) / 2 else 1)
    (if CarryLoop r p i then (a - 1 + 1) / 2 else 1))

/-- Interval test used by the graph evaluator. Pivots are retained here as
fixed singleton domains, so the global source can have a single vertex type. -/
def Domain {m : ℕ} (r p a : ℕ) (i : Fin (m - 1)) (v : ℕ) : Prop :=
  (IsPivot r p i → v = a) ∧ (IsFree r p i → lower r p a i ≤ v ∧ v ≤ upper r a i)

/-- Semantic unary constraints, prior to converting loops to domain endpoints. -/
def Unary {m : ℕ} (r p a : ℕ) (i : Fin (m - 1)) (v : ℕ) : Prop :=
  (IsPivot r p i → v = a) ∧
  (IsFree r p i → 1 ≤ v ∧ v ≤ upper r a i ∧
    (StrongLoop r p i → a ≤ 2 * v) ∧ (CarryLoop r p i → a - 1 ≤ 2 * v))

instance {m r p a : ℕ} (i : Fin (m - 1)) (v : ℕ) : Decidable (Domain r p a i v) := by
  unfold Domain IsFree IsPivot
  infer_instance

/-- No rounding approximation: this is exact integer ceiling division. -/
theorem ceil_half_le (b v : ℕ) : (b + 1) / 2 ≤ v ↔ b ≤ 2 * v := by omega

theorem lower_le_iff {m r p a : ℕ} (i : Fin (m - 1)) (v : ℕ) :
    lower r p a i ≤ v ↔
      1 ≤ v ∧ (StrongLoop r p i → a ≤ 2 * v) ∧
        (CarryLoop r p i → a - 1 ≤ 2 * v) := by
  by_cases hs : StrongLoop r p i <;> by_cases hc : CarryLoop r p i <;>
    simp [lower, hs, hc, max_le_iff, ceil_half_le, and_assoc, and_left_comm, and_comm]

theorem domain_iff_unary {m r p a : ℕ} (i : Fin (m - 1)) (v : ℕ) :
    Domain r p a i v ↔ Unary r p a i v := by
  simp only [Domain, Unary, lower_le_iff]
  tauto

/-- Original reflection incidence for one target, either ordinary or carried. -/
def TargetPair {m : ℕ} (t : ℕ) (i j : Fin (m - 1)) : Prop :=
  physical i + physical j = t ∨ physical i + physical j = m + t

instance {m t : ℕ} (i j : Fin (m - 1)) : Decidable (TargetPair t i j) := by
  unfold TargetPair
  infer_instance

/-- Binary threshold; zero denotes the absence of an ordinary edge. Self-pairs
have already been compiled into unary domains. Both orientations agree. -/
def edgeBound {m : ℕ} (r p a : ℕ) (i j : Fin (m - 1)) : ℕ :=
  if IsPivot r p i ∨ IsPivot r p j ∨ i = j then 0
  else if physical i + physical j = r ∨ physical i + physical j = p then a
  else if physical i + physical j = m + r ∨ physical i + physical j = m + p then a - 1
  else 0

theorem edgeBound_symm {m r p a : ℕ} (i j : Fin (m - 1)) :
    edgeBound r p a i j = edgeBound r p a j i := by
  unfold edgeBound
  simp only [Nat.add_comm (physical i) (physical j)]
  by_cases hi : IsPivot r p i <;> by_cases hj : IsPivot r p j <;>
    by_cases hij : i = j <;> simp [hi, hj, hij, Ne.symm]

/-- Graph-evaluator source after exact loop compilation. Each undirected edge
is tested only in the increasing physical-coordinate orientation. -/
def Admissible {m : ℕ} (r p a : ℕ) (x : Word m) : Prop :=
  Parameters m r p a ∧ (∀ i, Domain r p a i (x i)) ∧
    ∀ i j, i < j → edgeBound r p a i j ≤ x i + x j

/-- Exact original-source correctness of the domain/edge compiler. -/
theorem raw_iff_compiled {m r p a : ℕ} (x : Word m) :
    RawAdmissible r p a x ↔ Admissible r p a x := by
  rw [raw_iff_graph]
  constructor
  · rintro ⟨hp, ha, he, hc, hlo, hlc⟩
    refine ⟨hp, ?_, ?_⟩
    · intro i
      rw [domain_iff_unary]
      refine ⟨fun hi => alphabet_pivot ha hi, ?_⟩
      intro hi
      have hh := ha i
      simp only [show ¬ IsPivot r p i from hi, ↓reduceIte] at hh
      exact ⟨hh.1, hh.2, hlo i hi, hlc i hi⟩
    · intro i j hij
      unfold edgeBound
      split_ifs with h0 hs hcarry
      · exact Nat.zero_le _
      · have hf : IsFree r p i ∧ IsFree r p j ∧ i ≠ j := by
          unfold IsFree
          tauto
        exact he i j hf.1 hf.2.1 hf.2.2 hs
      · have hf : IsFree r p i ∧ IsFree r p j ∧ i ≠ j := by
          unfold IsFree
          tauto
        exact hc i j hf.1 hf.2.1 hf.2.2 hcarry
      · exact Nat.zero_le _
  · rintro ⟨hp, hd, he⟩
    have hu : ∀ i, Unary r p a i (x i) := fun i => (domain_iff_unary i (x i)).mp (hd i)
    have he' : ∀ i j, edgeBound r p a i j ≤ x i + x j := by
      intro i j
      rcases lt_trichotomy i j with hij | rfl | hij
      · exact he i j hij
      · simp [edgeBound]
      · simpa [edgeBound_symm, Nat.add_comm] using he j i hij
    refine ⟨hp, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      by_cases hi : IsPivot r p i
      · simpa only [hi, ↓reduceIte] using (hu i).1 hi
      · simpa only [hi, ↓reduceIte] using ⟨((hu i).2 hi).1, ((hu i).2 hi).2.1⟩
    · intro i j hi hj hij ht
      have hh := he' i j
      simpa [edgeBound, show ¬ IsPivot r p i from hi,
        show ¬ IsPivot r p j from hj, hij, ht] using hh
    · intro i j hi hj hij ht
      have hh := he' i j
      unfold edgeBound at hh
      simp only [show ¬ IsPivot r p i from hi, show ¬ IsPivot r p j from hj,
        hij, or_self, ↓reduceIte, ht] at hh
      split_ifs at hh <;> omega
    · intro i hi ht
      exact ((hu i).2 hi).2.2.1 ht
    · intro i hi ht
      exact ((hu i).2 hi).2.2.2 ht

/-- For each target a vertex has at most one reflection partner, including
a possible fixed point. This is the source of the degree-two structure. -/
theorem target_partner_unique {m t : ℕ} {i j k : Fin (m - 1)}
    (hij : TargetPair t i j) (hik : TargetPair t i k) : j = k := by
  apply Fin.ext
  have hj := j.isLt
  have hk := k.isLt
  dsimp [TargetPair, physical] at *
  omega

/-- Distinct admissible targets cannot generate parallel edges. -/
theorem targets_disjoint {m r p a : ℕ} (hp : Parameters m r p a)
    (i j : Fin (m - 1)) : ¬ (TargetPair r i j ∧ TargetPair p i j) := by
  have h1 := hp.1
  have h2 := hp.2.1
  have h3 := hp.2.2.1
  unfold TargetPair
  omega

/-- Ordinary neighbors after pivot and loop removal. -/
def neighbors {m : ℕ} (r p : ℕ) (i : Fin (m - 1)) : Finset (Fin (m - 1)) :=
  Finset.univ.filter (fun j => ¬ IsPivot r p i ∧ ¬ IsPivot r p j ∧ i ≠ j ∧
    (TargetPair r i j ∨ TargetPair p i j))

/-- The original ordinary reflection graph has maximum degree two. -/
theorem neighbors_card_le_two {m r p : ℕ} (i : Fin (m - 1)) :
    (neighbors r p i).card ≤ 2 := by
  classical
  let sr := Finset.univ.filter (TargetPair r i)
  let sp := Finset.univ.filter (TargetPair p i)
  have hr : sr.card ≤ 1 := Finset.card_le_one.mpr (by
    intro j hj k hk
    exact target_partner_unique (Finset.mem_filter.mp hj).2 (Finset.mem_filter.mp hk).2)
  have hp : sp.card ≤ 1 := Finset.card_le_one.mpr (by
    intro j hj k hk
    exact target_partner_unique (Finset.mem_filter.mp hj).2 (Finset.mem_filter.mp hk).2)
  have hsub : neighbors r p i ⊆ sr ∪ sp := by
    intro j hj
    have hh := (Finset.mem_filter.mp hj).2.2.2.2
    rcases hh with hh | hh
    · exact Finset.mem_union.mpr (Or.inl (by simp [sr, hh]))
    · exact Finset.mem_union.mpr (Or.inr (by simp [sp, hh]))
  have hh := (Finset.card_le_card hsub).trans (Finset.card_union_le sr sp)
  omega

end SubmittedGenus.RawGraph.SourceModel
