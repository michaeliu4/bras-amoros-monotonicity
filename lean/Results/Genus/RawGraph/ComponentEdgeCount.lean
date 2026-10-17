import Results.Genus.RawGraph.Topology

/-! Exact edge counting for the proved path/cycle orderings. -/
namespace SubmittedGenus.RawGraph.Topology
namespace OrderedComponent
variable {V : Type*} {G : SimpleGraph V}

theorem upper_edge_card (c : OrderedComponent G) [DecidableRel G.Adj] :
    (Finset.univ.filter (fun ij : Fin (c.edges + 1) × Fin (c.edges + 1) =>
      ij.1 < ij.2 ∧ G.Adj (c.label ij.1) (c.label ij.2))).card =
      c.edges + if c.cycle then 1 else 0 := by
  classical
  let f : Fin c.edges → Fin (c.edges + 1) × Fin (c.edges + 1) :=
    fun k => (k.castSucc, k.succ)
  let s := Finset.univ.image f
  let e : Fin (c.edges + 1) × Fin (c.edges + 1) := (0, Fin.last c.edges)
  have hf : Function.Injective f := by
    intro i j h
    apply Fin.ext
    exact congrArg (fun p => p.1.val) h
  have hs : s.card = c.edges := by
    dsimp [s]
    rw [Finset.card_image_of_injective _ hf]
    simp
  have hm (ij : Fin (c.edges + 1) × Fin (c.edges + 1)) :
      ij ∈ s ↔ ij.1.val + 1 = ij.2.val := by
    constructor
    · intro h
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp h
      rfl
    · intro h
      have hi : ij.1.val < c.edges := by have := ij.2.isLt; omega
      apply Finset.mem_image.mpr
      refine ⟨⟨ij.1.val, hi⟩, Finset.mem_univ _, ?_⟩
      apply Prod.ext <;> apply Fin.ext
      · rfl
      · exact h
  have he (hc : c.cycle = true) : e ∉ s := by
    rw [hm]
    have := c.cycle_min hc
    dsimp [e]
    omega
  have hset :
      Finset.univ.filter (fun ij : Fin (c.edges + 1) × Fin (c.edges + 1) =>
        ij.1 < ij.2 ∧ G.Adj (c.label ij.1) (c.label ij.2)) =
        if c.cycle then insert e s else s := by
    ext ij
    rcases ij with ⟨i,j⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, c.adjacent_iff]
    cases hc : c.cycle
    · simp only [Bool.false_eq_true, false_and, or_false, Bool.false_eq_true,
        ↓reduceIte, hm]
      change (i.val < j.val ∧ (i.val + 1 = j.val ∨ j.val + 1 = i.val)) ↔
        i.val + 1 = j.val
      omega
    · have hn := c.cycle_min hc
      simp only [true_and, ↓reduceIte, Finset.mem_insert, hm]
      simp only [e, Prod.mk.injEq, Fin.ext_iff, Fin.val_zero, Fin.val_last]
      change (i.val < j.val ∧ (i.val + 1 = j.val ∨ j.val + 1 = i.val ∨
        (i.val = 0 ∧ j.val = c.edges) ∨ (j.val = 0 ∧ i.val = c.edges))) ↔
        (i.val = 0 ∧ j.val = c.edges) ∨ i.val + 1 = j.val
      have := i.isLt
      have := j.isLt
      omega
  rw [hset]
  cases hc : c.cycle
  · simpa [hc] using hs
  · simp [Finset.card_insert_of_notMem (he hc), hs]

/-- A symmetric subrelation counts each undirected edge twice. -/
theorem relation_ordered_card (c : OrderedComponent G)
    (R : V → V → Prop) [DecidableRel R]
    (hsymm : ∀ u v, R u v → R v u)
    (hsub : ∀ u v, R u v → G.Adj u v) :
    (Finset.univ.filter (fun ij : Fin (c.edges + 1) × Fin (c.edges + 1) =>
      R (c.label ij.1) (c.label ij.2))).card =
    2 * (Finset.univ.filter (fun ij : Fin (c.edges + 1) × Fin (c.edges + 1) =>
      ij.1 < ij.2 ∧ R (c.label ij.1) (c.label ij.2))).card := by
  classical
  let a := Finset.univ.filter (fun ij : Fin (c.edges + 1) × Fin (c.edges + 1) =>
      ij.1 < ij.2 ∧ R (c.label ij.1) (c.label ij.2))
  let b := a.image Prod.swap
  have hb : b.card = a.card := Finset.card_image_of_injective _ Prod.swap_injective
  have hmem (i j : Fin (c.edges + 1)) :
      (i,j) ∈ b ↔ j < i ∧ R (c.label i) (c.label j) := by
    simp only [b, Finset.mem_image]
    constructor
    · rintro ⟨⟨u,v⟩, huv, he⟩
      cases he
      simp only [a, Finset.mem_filter, Finset.mem_univ, true_and] at huv
      exact ⟨huv.1, hsymm _ _ huv.2⟩
    · rintro ⟨hij, hr⟩
      refine ⟨(j,i), ?_, rfl⟩
      simp only [a, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hij, hsymm _ _ hr⟩
  have hd : Disjoint a b := by
    apply Finset.disjoint_left.mpr
    intro ij ha hb'
    rcases ij with ⟨i,j⟩
    have hh := (hmem i j).mp hb'
    simp only [a, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    exact (not_lt_of_ge (le_of_lt ha.1)) hh.1
  have heq : Finset.univ.filter (fun ij : Fin (c.edges + 1) × Fin (c.edges + 1) =>
      R (c.label ij.1) (c.label ij.2)) = a ∪ b := by
    ext ij
    rcases ij with ⟨i,j⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, hmem]
    simp only [a, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hr
      have hij : i ≠ j := by
        intro hh
        subst j
        exact G.irrefl (hsub _ _ hr)
      rcases lt_or_gt_of_ne hij with h | h
      · exact Or.inl ⟨h,hr⟩
      · exact Or.inr ⟨h,hr⟩
    · rintro (h | h) <;> exact h.2
  rw [heq, Finset.card_union_of_disjoint hd, hb]
  change a.card + a.card = 2 * a.card
  omega

/-- Exact coloured edge count, including the closing edge of a cycle. -/
theorem relation_upper_card (c : OrderedComponent G)
    (R : V → V → Prop) [DecidableRel R]
    (hsub : ∀ u v, R u v → G.Adj u v) :
    (Finset.univ.filter (fun ij : Fin (c.edges + 1) × Fin (c.edges + 1) =>
      ij.1 < ij.2 ∧ R (c.label ij.1) (c.label ij.2))).card =
    (Finset.univ.filter (fun k : Fin c.edges =>
      R (c.label k.castSucc) (c.label k.succ))).card +
    if c.cycle = true ∧ R (c.label 0) (c.label (Fin.last c.edges)) then 1 else 0 := by
  classical
  let f : Fin c.edges → Fin (c.edges + 1) × Fin (c.edges + 1) :=
    fun k => (k.castSucc, k.succ)
  let a := Finset.univ.filter (fun k : Fin c.edges =>
      R (c.label k.castSucc) (c.label k.succ))
  let s := a.image f
  let e : Fin (c.edges + 1) × Fin (c.edges + 1) := (0, Fin.last c.edges)
  have hf : Function.Injective f := by
    intro i j h
    apply Fin.ext
    exact congrArg (fun p => p.1.val) h
  have hs : s.card = a.card := Finset.card_image_of_injective _ hf
  have hm (i j : Fin (c.edges + 1)) :
      (i,j) ∈ s ↔ i.val + 1 = j.val ∧ R (c.label i) (c.label j) := by
    constructor
    · rintro h
      obtain ⟨k, hk, he⟩ := Finset.mem_image.mp h
      cases he
      exact ⟨rfl, (Finset.mem_filter.mp hk).2⟩
    · rintro ⟨h,hr⟩
      have hi : i.val < c.edges := by have := j.isLt; omega
      let k : Fin c.edges := ⟨i.val, hi⟩
      have hki : k.castSucc = i := Fin.ext rfl
      have hkj : k.succ = j := Fin.ext h
      refine Finset.mem_image.mpr ⟨k, ?_, ?_⟩
      · simp only [a, Finset.mem_filter, Finset.mem_univ, true_and, hki, hkj]
        exact hr
      · exact Prod.ext hki hkj
  let t := c.cycle = true ∧ R (c.label 0) (c.label (Fin.last c.edges))
  have he (ht : t) : e ∉ s := by
    rw [hm]
    have := c.cycle_min ht.1
    dsimp [e]
    omega
  have hset : Finset.univ.filter (fun ij : Fin (c.edges + 1) × Fin (c.edges + 1) =>
      ij.1 < ij.2 ∧ R (c.label ij.1) (c.label ij.2)) =
      if t then insert e s else s := by
    ext ij
    rcases ij with ⟨i,j⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hiff : (i < j ∧ R (c.label i) (c.label j)) ↔
        (i,j) ∈ s ∨ (t ∧ (i,j) = e) := by
      rw [hm]
      constructor
      · rintro ⟨hij,hr⟩
        have hadj := (c.adjacent_iff i j).mp (hsub _ _ hr)
        by_cases hcon : i.val + 1 = j.val
        · exact Or.inl ⟨hcon,hr⟩
        · have hv : i.val = 0 ∧ j.val = c.edges := by
            change i.val < j.val at hij
            rcases hadj with h | h | ⟨hc,h⟩ <;> omega
          have hi : i = 0 := Fin.ext hv.1
          have hj : j = Fin.last c.edges := Fin.ext hv.2
          have hc : c.cycle = true := by
            change i.val < j.val at hij
            rcases hadj with h | h | h <;> simp_all
          exact Or.inr ⟨⟨hc, by simpa [hi,hj] using hr⟩, Prod.ext hi hj⟩
      · rintro (⟨hcon,hr⟩ | ⟨ht,heq⟩)
        · exact ⟨by change i.val < j.val; omega, hr⟩
        · have hi : i = 0 := congrArg Prod.fst heq
          have hj : j = Fin.last c.edges := congrArg Prod.snd heq
          have hn := c.cycle_min ht.1
          subst i; subst j
          exact ⟨by change 0 < c.edges; omega, ht.2⟩
    rw [hiff]
    by_cases ht : t
    · simp [ht, Finset.mem_insert, or_comm]
    · simp [ht]
  rw [hset]
  change (if t then insert e s else s).card = a.card + if t then 1 else 0
  by_cases ht : t
  · simp [ht, Finset.card_insert_of_notMem (he ht), hs]
  · simp [ht, hs]

theorem relation_edge_card (c : OrderedComponent G)
    (R : V → V → Prop) [DecidableRel R]
    (hsymm : ∀ u v, R u v → R v u)
    (hsub : ∀ u v, R u v → G.Adj u v) :
    (Finset.univ.filter (fun ij : Fin (c.edges + 1) × Fin (c.edges + 1) =>
      R (c.label ij.1) (c.label ij.2))).card =
    2 * ((Finset.univ.filter (fun k : Fin c.edges =>
      R (c.label k.castSucc) (c.label k.succ))).card +
    if c.cycle = true ∧ R (c.label 0) (c.label (Fin.last c.edges)) then 1 else 0) := by
  rw [relation_ordered_card c R hsymm hsub, relation_upper_card c R hsub]

end OrderedComponent
end SubmittedGenus.RawGraph.Topology
