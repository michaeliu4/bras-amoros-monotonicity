import Results.Genus.RawGraph.Counting
import Results.Genus.RawGraph.StrongRuns

namespace SubmittedGenus.RawGraph.StrongEdgeCounts
open SourceModel Incidence

def ordinaryEdges (m t : ℕ) : Finset (Fin (m - 1) × Fin (m - 1)) :=
  Finset.univ.filter (fun ij => ij.1 < ij.2 ∧ physical ij.1 + physical ij.2 = t)

/-- Exact number of nonself ordinary reflection edges at one target. -/
theorem ordinaryEdges_card {m t : ℕ} (ht : 0 < t ∧ t < m) :
    (ordinaryEdges m t).card = (t - 1) / 2 := by
  let lows := Finset.univ.filter (fun i : Fin (m - 1) => 2 * physical i < t)
  have he : (ordinaryEdges m t).card = lows.card := by
    apply Finset.card_bij (fun ij _ => ij.1)
    · rintro ⟨i, j⟩ h
      obtain ⟨_, hij, hs⟩ := Finset.mem_filter.mp h
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      change i.val < j.val at hij
      change (i.val + 1) + (j.val + 1) = t at hs
      change 2 * (i.val + 1) < t
      omega
    · rintro ⟨i, j⟩ hij ⟨k, l⟩ hkl he
      change i = k at he
      subst k
      refine Prod.ext rfl ?_
      apply Fin.ext
      change j.val = l.val
      have h1 := (Finset.mem_filter.mp hij).2.2
      have h2 := (Finset.mem_filter.mp hkl).2.2
      change (i.val + 1) + (j.val + 1) = t at h1
      change (i.val + 1) + (l.val + 1) = t at h2
      omega
    · intro i hi
      have hh := (Finset.mem_filter.mp hi).2
      change 2 * (i.val + 1) < t at hh
      let j : Fin (m - 1) := ⟨t - (i.val + 1) - 1, by have := i.isLt; omega⟩
      refine ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩, rfl⟩
      · change i.val < t - (i.val + 1) - 1
        omega
      · change (i.val + 1) + (t - (i.val + 1) - 1 + 1) = t
        omega
  rw [he]
  have hpred (i : Fin (m - 1)) : 2 * physical i < t ↔ i.val < (t - 1) / 2 := by
    unfold physical
    omega
  simp only [lows, hpred, Fin.card_filter_val_lt]
  exact min_eq_right (by omega)

def allStrongEdges (m r p : ℕ) : Finset (Fin (m - 1) × Fin (m - 1)) :=
  ordinaryEdges m r ∪ ordinaryEdges m p

lemma allStrongEdges_card {m r p a : ℕ} (hp : Parameters m r p a) :
    (allStrongEdges m r p).card = (r - 1) / 2 + (p - 1) / 2 := by
  have h1 := hp.1; have h2 := hp.2.1; have h3 := hp.2.2.1
  have hd : Disjoint (ordinaryEdges m r) (ordinaryEdges m p) := by
    apply Finset.disjoint_left.mpr
    intro ij hi hj
    have hi' := (Finset.mem_filter.mp hi).2.2
    have hj' := (Finset.mem_filter.mp hj).2.2
    omega
  rw [allStrongEdges, Finset.card_union_of_disjoint hd, ordinaryEdges_card (by omega),
    ordinaryEdges_card (by omega)]

private def deletedPair {m r p a : ℕ} (hp : Parameters m r p a) : Fin (m - 1) × Fin (m - 1) :=
  let u : Fin (m - 1) := ⟨r - 1, by have := hp.1; have := hp.2.1; have := hp.2.2.1; omega⟩
  let v : Fin (m - 1) := ⟨p - r - 1, by have := hp.1; have := hp.2.1; have := hp.2.2.1; omega⟩
  if r < p - r then (u, v) else (v, u)

lemma allStrongEdges_eq_when_double {m r p a : ℕ} (hp : Parameters m r p a) (he : p = 2 * r) :
    allStrongEdges m r p = strongEdges m r p := by
  have h1 := hp.1; have h2 := hp.2.1; have h3 := hp.2.2.1
  ext ⟨i, j⟩
  simp only [allStrongEdges, ordinaryEdges, strongEdges, StrongPair, IsPivot,
    Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, physical, Fin.lt_def]
  omega

lemma allStrongEdges_eq_insert {m r p a : ℕ} (hp : Parameters m r p a) (he : p ≠ 2 * r) :
    allStrongEdges m r p = insert (deletedPair hp) (strongEdges m r p) := by
  have h1 := hp.1; have h2 := hp.2.1; have h3 := hp.2.2.1
  ext ⟨i, j⟩
  simp only [allStrongEdges, ordinaryEdges, strongEdges, StrongPair, IsPivot,
    Finset.mem_union, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and,
    physical, Fin.lt_def, deletedPair]
  split_ifs <;> simp only [Prod.mk.injEq, Fin.ext_iff] <;> omega

lemma deletedPair_not_retained {m r p a : ℕ} (hp : Parameters m r p a) :
    deletedPair hp ∉ strongEdges m r p := by
  have h1 := hp.1
  unfold deletedPair
  split_ifs <;> simp [strongEdges, StrongPair, IsPivot, physical, Nat.sub_add_cancel h1]

/-- Exact source strong-edge count, including the p=2r deleted-loop corner. -/
theorem strong_edges_exact {m r p a : ℕ} (hp : Parameters m r p a) :
    (strongEdges m r p).card + (if p = 2 * r then 0 else 1) =
      (r - 1) / 2 + (p - 1) / 2 := by
  by_cases he : p = 2 * r
  · rw [if_pos he, add_zero, ← allStrongEdges_eq_when_double hp he, allStrongEdges_card hp]
  · have hh := allStrongEdges_card hp
    rw [allStrongEdges_eq_insert hp he, Finset.card_insert_of_notMem (deletedPair_not_retained hp)] at hh
    simpa [he] using hh

theorem strong_edges_formula {m r p a : ℕ} (hp : Parameters m r p a) :
    (strongEdges m r p).card = (r - 1) / 2 + (p - 1) / 2 - (if p = 2 * r then 0 else 1) := by
  have hh := strong_edges_exact hp
  omega


def restrictedEdges (m r p : ℕ) : Finset (Fin (m - 1) × Fin (m - 1)) :=
  (strongEdges m r p).filter (fun ij => r < physical ij.1 ∧ r < physical ij.2)

lemma restricted_edge_data {m r p a : ℕ} (hp : Parameters m r p a)
    {ij : Fin (m - 1) × Fin (m - 1)} (h : ij ∈ restrictedEdges m r p) :
    ij.1 < ij.2 ∧ physical ij.1 + physical ij.2 = p ∧ r < physical ij.1 := by
  obtain ⟨he, hh⟩ := Finset.mem_filter.mp h
  obtain ⟨_, hij, _, _, hs⟩ := Finset.mem_filter.mp he
  exact ⟨hij, by have := hp.1; omega, hh.1⟩

/-- Exactly the strong edges with both endpoints carrying alphabet3. Their
source geometry makes each one a maximal one-edge E-run. -/
theorem restricted_edges_formula {m r p a : ℕ} (hp : Parameters m r p a) :
    (restrictedEdges m r p).card = (p - 1) / 2 - r := by
  let n := (p - 1) / 2 - r
  have h1 := hp.1; have h2 := hp.2.1; have h3 := hp.2.2.1
  have he : (restrictedEdges m r p).card = (Finset.univ : Finset (Fin n)).card := by
    let f (ij : Fin (m - 1) × Fin (m - 1)) (h : ij ∈ restrictedEdges m r p) : Fin n :=
      ⟨physical ij.1 - r - 1, by
        obtain ⟨hlt, hsum, hhi⟩ := restricted_edge_data hp h
        have hlt' : physical ij.1 < physical ij.2 := Nat.succ_lt_succ hlt
        dsimp [n]
        omega⟩
    apply Finset.card_bij f
    · intro ij h; exact Finset.mem_univ _
    · intro ij hij kl hkl he
      obtain ⟨_, hsij, hi⟩ := restricted_edge_data hp hij
      obtain ⟨_, hskl, hk⟩ := restricted_edge_data hp hkl
      have hv := congrArg Fin.val he
      change physical ij.1 - r - 1 = physical kl.1 - r - 1 at hv
      have ha : physical ij.1 = physical kl.1 := by omega
      have hb : physical ij.2 = physical kl.2 := by omega
      apply Prod.ext
      · exact Fin.ext (by unfold physical at ha; omega)
      · exact Fin.ext (by unfold physical at hb; omega)
    · intro k _
      have hk := k.isLt
      change k.val < (p - 1) / 2 - r at hk
      let i : Fin (m - 1) := ⟨r + k.val, by omega⟩
      let j : Fin (m - 1) := ⟨p - (r + k.val + 1) - 1, by omega⟩
      have hij : (i, j) ∈ restrictedEdges m r p := by
        refine Finset.mem_filter.mpr ⟨?_, ?_⟩
        · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_, ?_, ?_⟩
          · change r + k.val < p - (r + k.val + 1) - 1
            omega
          · unfold IsPivot
            dsimp [physical, i]
            omega
          · unfold IsPivot
            dsimp [physical, j]
            omega
          · right
            change (r + k.val + 1) + (p - (r + k.val + 1) - 1 + 1) = p
            omega
        · change r < r + k.val + 1 ∧ r < p - (r + k.val + 1) - 1 + 1
          omega
      refine ⟨(i, j), hij, ?_⟩
      apply Fin.ext
      change (r + k.val + 1) - r - 1 = k.val
      omega
  simpa only [Finset.card_univ, Fintype.card_fin] using he

lemma restricted_edge_is_singleton_run {m r p : ℕ}
    {ij : Fin (m - 1) × Fin (m - 1)} (h : ij ∈ restrictedEdges m r p) :
    (∀ k, StrongRuns.StrongStep r p ij.1 k → k = ij.2) ∧
      (∀ k, StrongRuns.StrongStep r p ij.2 k → k = ij.1) := by
  obtain ⟨he, hh⟩ := Finset.mem_filter.mp h
  obtain ⟨_, hij, hi, hj, hs⟩ := Finset.mem_filter.mp he
  apply StrongRuns.restricted_strong_run hh.1 hh.2
  refine ⟨⟨ne_of_lt hij, hi, hj, ?_⟩, hs⟩
  rcases hs with hs | hs
  · exact Or.inl (Or.inl hs)
  · exact Or.inr (Or.inl hs)

end SubmittedGenus.RawGraph.StrongEdgeCounts
