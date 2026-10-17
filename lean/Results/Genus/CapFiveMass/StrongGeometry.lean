import Results.Genus.CapFiveMass.ComponentCounts
import Results.Genus.RawGraph.Counting
import Results.Genus.RawGraph.ActualLayout
import Results.Genus.RawGraph.ComponentLocalization

noncomputable section
open scoped BigOperators
namespace SubmittedGenus.CapFiveMass.ActualComponent
open RawGraph RawGraph.SourceModel RawGraph.Topology LocalSource

local instance (m r p : ℕ) : DecidableRel (freeGraph m r p).Adj := Classical.decRel _

lemma vertex_injective {m r p : ℕ} (c : Component m r p) : Function.Injective (vertex c) := by
  intro i j h
  apply (freeComponentOrder m r p c).label.injective
  exact Subtype.ext (Subtype.ext h)

lemma loops_disjoint {m r p a : ℕ} (hp : Parameters m r p a) (i : Fin (m - 1)) :
    ¬ (StrongLoop r p i ∧ CarryLoop r p i) := by
  have h1 := hp.1; have h2 := hp.2.1; have h3 := hp.2.2.1
  unfold StrongLoop CarryLoop
  omega

lemma loop_no_two_neighbors {m r p : ℕ} {i j k : Fin (m - 1)}
    (hl : StrongLoop r p i ∨ CarryLoop r p i)
    (hj : (rawGraph m r p).Adj i j) (hk : (rawGraph m r p).Adj i k) : j = k := by
  have hself : TargetPair r i i ∨ TargetPair p i i := by
    unfold StrongLoop CarryLoop at hl
    unfold TargetPair
    rcases hl with (h | h) | (h | h)
    · exact Or.inl (Or.inl (by omega))
    · exact Or.inr (Or.inl (by omega))
    · exact Or.inl (Or.inr (by omega))
    · exact Or.inr (Or.inr (by omega))
  rcases hself with hr | hp
  · have hjp : TargetPair p i j := hj.2.2.2.resolve_left
      (fun h => hj.1 (target_partner_unique hr h))
    have hkp : TargetPair p i k := hk.2.2.2.resolve_left
      (fun h => hk.1 (target_partner_unique hr h))
    exact target_partner_unique hjp hkp
  · have hjr : TargetPair r i j := hj.2.2.2.resolve_right
      (fun h => hj.1 (target_partner_unique hp h))
    have hkr : TargetPair r i k := hk.2.2.2.resolve_right
      (fun h => hk.1 (target_partner_unique hp h))
    exact target_partner_unique hjr hkr

/-- Every retained unary loop lies at an endpoint of its actual path component. -/
lemma loop_is_path_endpoint {m r p : ℕ} (c : Component m r p)
    (j : Fin (edgeCount c + 1))
    (hl : StrongLoop r p (vertex c j) ∨ CarryLoop r p (vertex c j)) :
    (freeComponentOrder m r p c).cycle = false ∧ (j = 0 ∨ j = Fin.last (edgeCount c)) := by
  let n := edgeCount c
  have hend : j = 0 ∨ j = Fin.last n := by
    by_contra h
    have h0 : 0 < j.val := by
      have hh : j ≠ 0 := fun he => h (Or.inl he)
      have hval : j.val ≠ 0 := fun he => hh (Fin.ext he)
      omega
    have hn : j.val < n := by
      have hh : j ≠ Fin.last n := fun he => h (Or.inr he)
      have hval : j.val ≠ n := fun he => hh (Fin.ext he)
      have := j.isLt
      omega
    let prev : Fin (n + 1) := ⟨j.val - 1, by omega⟩
    let next : Fin (n + 1) := ⟨j.val + 1, by omega⟩
    have hp : (rawGraph m r p).Adj (vertex c j) (vertex c prev) :=
      ((freeComponentOrder m r p c).adjacent_iff j prev).mpr (Or.inr (Or.inl (by dsimp [prev]; omega)))
    have hn' : (rawGraph m r p).Adj (vertex c j) (vertex c next) :=
      ((freeComponentOrder m r p c).adjacent_iff j next).mpr (Or.inl rfl)
    have he := vertex_injective c (loop_no_two_neighbors hl hp hn')
    have he' := congrArg Fin.val he
    dsimp [prev, next] at he'
    omega
  refine ⟨?_, hend⟩
  by_contra hcycle
  have hc : (freeComponentOrder m r p c).cycle = true := Bool.eq_true_of_not_eq_false hcycle
  have hmin := (freeComponentOrder m r p c).cycle_min hc
  change 3 ≤ n at hmin
  rcases hend with rfl | rfl
  · let one : Fin (n + 1) := ⟨1, by omega⟩
    have h1 : (rawGraph m r p).Adj (vertex c 0) (vertex c one) :=
      ((freeComponentOrder m r p c).adjacent_iff 0 one).mpr (Or.inl rfl)
    have hn : (rawGraph m r p).Adj (vertex c 0) (vertex c (Fin.last n)) :=
      ((freeComponentOrder m r p c).adjacent_iff 0 (Fin.last n)).mpr
        (Or.inr (Or.inr ⟨hc, Or.inl ⟨rfl, rfl⟩⟩))
    have he := congrArg Fin.val (vertex_injective c (loop_no_two_neighbors hl h1 hn))
    dsimp [one] at he
    omega
  · let prev : Fin (n + 1) := ⟨n - 1, by omega⟩
    have hp : (rawGraph m r p).Adj (vertex c (Fin.last n)) (vertex c prev) :=
      ((freeComponentOrder m r p c).adjacent_iff (Fin.last n) prev).mpr
        (Or.inr (Or.inl (by dsimp [prev]; omega)))
    have h0 : (rawGraph m r p).Adj (vertex c (Fin.last n)) (vertex c 0) :=
      closing_adj c hc
    have he := congrArg Fin.val (vertex_injective c (loop_no_two_neighbors hl hp h0))
    dsimp [prev] at he
    omega


lemma sum_supported_endpoints (n : ℕ) (f : Fin (n + 1) → ℕ)
    (hf : ∀ j, j ≠ 0 → j ≠ Fin.last n → f j = 0) :
    (∑ j, f j) = f 0 + (if n = 0 then 0 else f (Fin.last n)) := by
  classical
  by_cases hn : n = 0
  · subst n
    simp
  · have hne : (0 : Fin (n + 1)) ≠ Fin.last n := by
      intro h
      have := congrArg Fin.val h
      exact hn this.symm
    have hs : (∑ j ∈ ({0, Fin.last n} : Finset (Fin (n + 1))), f j) = ∑ j, f j := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
      exact hf j hj.1 hj.2
    rw [← hs, Finset.sum_pair hne, if_neg hn]

lemma loopKind_ne_free {m r p : ℕ} (i : Fin (m - 1))
    (h : loopKind (r := r) (p := p) i ≠ .free) :
    StrongLoop r p i ∨ CarryLoop r p i := by
  unfold loopKind at h
  split_ifs at h with hs hc
  · exact Or.inl hs
  · exact Or.inr hc
  · exact (h rfl).elim

/-- Unary loop counts in an actual component equal its endpoint counts; the
isolated case counts its single physical loop just once. -/
lemma endpointCount_eq_loopKind_sum {m r p : ℕ} (c : Component m r p)
    (kind : EndpointKind) (hk : kind ≠ .free) :
    endpointCount c kind = ∑ j : Fin (edgeCount c + 1),
      if loopKind (r := r) (p := p) (vertex c j) = kind then 1 else 0 := by
  classical
  by_cases hc : (freeComponentOrder m r p c).cycle = true
  · simp only [endpointCount, hc, if_true]
    symm
    apply Finset.sum_eq_zero
    intro j _
    have hnot : loopKind (r := r) (p := p) (vertex c j) ≠ kind := by
      intro hj
      have hl := loopKind_ne_free (vertex c j) (fun h => hk (hj.symm.trans h))
      have hh := (loop_is_path_endpoint c j hl).1
      rw [hc] at hh
      cases hh
    simp [hnot]
  · rw [sum_supported_endpoints]
    · simp only [endpointCount, hc, if_false, leftKind, rightKind]
      by_cases hn : edgeCount c = 0 <;> simp [hn, Ne.symm hk]
    · intro j hj0 hjn
      have hnot : loopKind (r := r) (p := p) (vertex c j) ≠ kind := by
        intro hj
        have hl := loopKind_ne_free (vertex c j) (fun h => hk (hj.symm.trans h))
        exact (loop_is_path_endpoint c j hl).2.elim hj0 hjn
      simp [hnot]

lemma loopKind_strong_iff {m r p : ℕ} (i : Fin (m - 1)) :
    loopKind (r := r) (p := p) i = .strongLoop ↔ StrongLoop r p i := by
  unfold loopKind
  split_ifs <;> simp_all

lemma loopKind_carry_iff {m r p a : ℕ} (hp : Parameters m r p a) (i : Fin (m - 1)) :
    loopKind (r := r) (p := p) i = .carryLoop ↔ CarryLoop r p i := by
  have hd := loops_disjoint hp i
  unfold loopKind
  split_ifs <;> simp_all

lemma endpoint_strong_count {m r p : ℕ} (c : Component m r p) :
    endpointCount c .strongLoop = ∑ j : Fin (edgeCount c + 1),
      if StrongLoop r p (vertex c j) then 1 else 0 := by
  rw [endpointCount_eq_loopKind_sum c .strongLoop (by decide)]
  simp_rw [loopKind_strong_iff]

lemma endpoint_carry_count {m r p a : ℕ} (hp : Parameters m r p a) (c : Component m r p) :
    endpointCount c .carryLoop = ∑ j : Fin (edgeCount c + 1),
      if CarryLoop r p (vertex c j) then 1 else 0 := by
  rw [endpointCount_eq_loopKind_sum c .carryLoop (by decide)]
  simp_rw [loopKind_carry_iff hp]

/-- Global endpoint exponents are the original physical strong-loop count. -/
lemma total_strong_loops {m r p : ℕ} :
    totalEndpointCount m r p .strongLoop =
      (Finset.univ.filter (fun i : FreeVertex m r p => StrongLoop r p i.val)).card := by
  unfold totalEndpointCount
  simp_rw [endpoint_strong_count]
  have hh := (freeOrderedVertexEquiv m r p).sum_comp
    (fun i : FreeVertex m r p => (if StrongLoop r p i.val then 1 else 0 : ℕ))
  rw [Fintype.sum_sigma] at hh
  change (∑ c : Component m r p, ∑ j : Fin (edgeCount c + 1),
    if StrongLoop r p (vertex c j) then 1 else 0) =
      ∑ i : FreeVertex m r p, (if StrongLoop r p i.val then 1 else 0 : ℕ) at hh
  simpa only [Finset.sum_boole, Nat.cast_id] using hh

lemma total_carry_loops {m r p a : ℕ} (hp : Parameters m r p a) :
    totalEndpointCount m r p .carryLoop =
      (Finset.univ.filter (fun i : FreeVertex m r p => CarryLoop r p i.val)).card := by
  unfold totalEndpointCount
  simp_rw [endpoint_carry_count hp]
  have hh := (freeOrderedVertexEquiv m r p).sum_comp
    (fun i : FreeVertex m r p => (if CarryLoop r p i.val then 1 else 0 : ℕ))
  rw [Fintype.sum_sigma] at hh
  change (∑ c : Component m r p, ∑ j : Fin (edgeCount c + 1),
    if CarryLoop r p (vertex c j) then 1 else 0) =
      ∑ i : FreeVertex m r p, (if CarryLoop r p i.val then 1 else 0 : ℕ) at hh
  simpa only [Finset.sum_boole, Nat.cast_id] using hh


/-- The strong subrelation of the actual free ordinary graph. -/
def StrongAdj {m : ℕ} (r p : ℕ) (i j : FreeVertex m r p) : Prop :=
  (freeGraph m r p).Adj i j ∧ StrongEdge r p i.val j.val

instance {m r p : ℕ} (i j : FreeVertex m r p) : Decidable (StrongAdj r p i j) := by
  unfold StrongAdj freeGraph rawGraph StrongEdge IsFree IsPivot TargetPair
  infer_instance

lemma strongAdj_symm {m r p : ℕ} {i j : FreeVertex m r p} (h : StrongAdj r p i j) :
    StrongAdj r p j i := ⟨h.1.symm, by simpa [StrongEdge, Nat.add_comm] using h.2⟩

lemma strong_pairs_count (m r p : ℕ) :
    (Finset.univ.filter (fun ij : FreeVertex m r p × FreeVertex m r p =>
      StrongAdj r p ij.1 ij.2)).card = 2 * totalStrongCount m r p := by
  classical
  rw [relation_component_card (freeGraph m r p) (freeGraph_noThird m r p)
    (freeGraph_noTriangle m r p) (StrongAdj r p) (fun _ _ h => h.1)]
  have hlocal (c : Component m r p) :
      (Finset.univ.filter (fun ij : Fin (edgeCount c + 1) × Fin (edgeCount c + 1) =>
        StrongAdj r p ((freeComponentOrder m r p c).label ij.1).val
          ((freeComponentOrder m r p c).label ij.2).val)).card = 2 * strongCount c := by
    let O := freeComponentOrder m r p c
    let R (u v : c) := StrongAdj r p u.val v.val
    have hh := O.relation_edge_card R (fun _ _ h => strongAdj_symm h) (fun _ _ h => h.1)
    have hcons (j : Fin O.edges) : R (O.label j.castSucc) (O.label j.succ) ↔
        StrongEdge r p (vertex c j.castSucc) (vertex c j.succ) := by
      exact and_iff_right (consecutive_adj c j)
    have hclose : (O.cycle = true ∧ R (O.label 0) (O.label (Fin.last O.edges))) ↔
        O.cycle = true ∧ StrongEdge r p (vertex c (Fin.last _)) (vertex c 0) := by
      constructor
      · rintro ⟨hc, _, hs⟩
        change StrongEdge r p (vertex c 0) (vertex c (Fin.last _)) at hs
        exact ⟨hc, by simpa only [StrongEdge, Nat.add_comm] using hs⟩
      · rintro ⟨hc, hs⟩
        refine ⟨hc, (closing_adj c hc).symm, ?_⟩
        change StrongEdge r p (vertex c 0) (vertex c (Fin.last _))
        simpa only [StrongEdge, Nat.add_comm] using hs
    simp_rw [hcons, hclose] at hh
    exact hh
  calc
    _ = ∑ c : Component m r p, 2 * strongCount c := by
      apply Finset.sum_congr rfl
      intro c _
      exact hlocal c
    _ = _ := by rw [← Finset.mul_sum]; rfl

end SubmittedGenus.CapFiveMass.ActualComponent
