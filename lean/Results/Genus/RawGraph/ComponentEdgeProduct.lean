import Results.Genus.RawGraph.ComponentEdgeCount

/-! Exact products over the genuine ordered path/cycle edge sets. The target
commutative monoid permits signed weights; no positivity is required. -/
namespace SubmittedGenus.RawGraph.Topology.OrderedComponent
open scoped BigOperators
noncomputable section
variable {V M : Type*} {G : SimpleGraph V} [CommMonoid M]

/-- Arbitrary upper-oriented edge weights factor over consecutive positions
and the single closing edge of a cycle. -/
theorem upper_edge_prod (c : OrderedComponent G) [DecidableRel G.Adj] (w : V→V→M) :
    (∏ ij ∈ Finset.univ.filter (fun ij : Fin (c.edges+1)×Fin (c.edges+1) =>
      ij.1 < ij.2 ∧ G.Adj (c.label ij.1) (c.label ij.2)),w (c.label ij.1) (c.label ij.2))=
    (∏ k : Fin c.edges,w (c.label k.castSucc) (c.label k.succ))*
      (if c.cycle then w (c.label 0) (c.label (Fin.last c.edges)) else 1) := by
  classical
  let f : Fin c.edges → Fin (c.edges + 1) × Fin (c.edges + 1) :=
    fun k => (k.castSucc, k.succ)
  let s := Finset.univ.image f
  let e : Fin (c.edges + 1) × Fin (c.edges + 1) := (0, Fin.last c.edges)
  have hf : Function.Injective f := by
    intro i j h
    apply Fin.ext
    exact congrArg (fun p => p.1.val) h
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
  have hs : (∏ ij ∈ s,w (c.label ij.1) (c.label ij.2))=
      ∏ k : Fin c.edges,w (c.label k.castSucc) (c.label k.succ) := by
    dsimp [s]
    rw [Finset.prod_image (fun i _ j _ h => hf h)]
  rw [hset]
  cases hc : c.cycle
  · simpa only [hc,Bool.false_eq_true,if_false,mul_one] using hs
  · simp only [if_true,Finset.prod_insert (he hc),hs,e]
    exact mul_comm _ _

/-- The same exact product identity for any retained edge subrelation. -/
theorem relation_upper_prod (c : OrderedComponent G) (R : V→V→Prop) [DecidableRel R]
    (hsub : ∀ u v,R u v→G.Adj u v) (w : V→V→M) :
    (∏ ij ∈ Finset.univ.filter (fun ij : Fin (c.edges+1)×Fin (c.edges+1) =>
      ij.1 < ij.2 ∧ R (c.label ij.1) (c.label ij.2)),w (c.label ij.1) (c.label ij.2))=
    (∏ k ∈ Finset.univ.filter (fun k : Fin c.edges => R (c.label k.castSucc) (c.label k.succ)),
      w (c.label k.castSucc) (c.label k.succ))*
      (if c.cycle=true ∧ R (c.label 0) (c.label (Fin.last c.edges))
        then w (c.label 0) (c.label (Fin.last c.edges)) else 1) := by
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
  have hs : (∏ ij ∈ s,w (c.label ij.1) (c.label ij.2))=
      ∏ k ∈ a,w (c.label k.castSucc) (c.label k.succ) := by
    dsimp [s]
    rw [Finset.prod_image (fun i _ j _ h => hf h)]
  rw [hset]
  change (∏ ij ∈ (if t then insert e s else s),w (c.label ij.1) (c.label ij.2))=
    (∏ k ∈ a,w (c.label k.castSucc) (c.label k.succ))*
      (if t then w (c.label 0) (c.label (Fin.last c.edges)) else 1)
  by_cases ht : t
  · simp only [if_pos ht,Finset.prod_insert (he ht),hs,e]
    exact mul_comm _ _
  · simp only [if_neg ht,mul_one]
    exact hs

/-- Symmetry gives the usual source transfer orientation for the cycle close. -/
theorem upper_edge_prod_symmetric (c : OrderedComponent G) [DecidableRel G.Adj]
    (w : V→V→M) (hw : ∀ u v,w u v=w v u) :
    (∏ ij ∈ Finset.univ.filter (fun ij : Fin (c.edges+1)×Fin (c.edges+1) =>
      ij.1 < ij.2 ∧ G.Adj (c.label ij.1) (c.label ij.2)),w (c.label ij.1) (c.label ij.2))=
    (∏ k : Fin c.edges,w (c.label k.castSucc) (c.label k.succ))*
      (if c.cycle then w (c.label (Fin.last c.edges)) (c.label 0) else 1) := by
  rw [upper_edge_prod c w,hw (c.label 0) (c.label (Fin.last c.edges))]

end
end SubmittedGenus.RawGraph.Topology.OrderedComponent
