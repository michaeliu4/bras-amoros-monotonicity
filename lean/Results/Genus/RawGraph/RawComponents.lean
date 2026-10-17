import Results.Genus.RawGraph.Topology
import Results.Genus.RawGraph.Layout

namespace SubmittedGenus.RawGraph.Topology

open SourceModel SimpleGraph

/-- The actual ordinary graph after both fixed pivots and self-pairs are removed. -/
def rawGraph (m r p : ℕ) : SimpleGraph (Fin (m - 1)) where
  Adj i j := i ≠ j ∧ IsFree r p i ∧ IsFree r p j ∧ (TargetPair r i j ∨ TargetPair p i j)
  symm := ⟨by
    intro i j h
    refine ⟨h.1.symm, h.2.2.1, h.2.1, ?_⟩
    simpa [TargetPair, Nat.add_comm] using h.2.2.2⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance (m r p : ℕ) : DecidableRel (rawGraph m r p).Adj := by
  unfold rawGraph IsFree IsPivot TargetPair
  infer_instance

theorem targetPair_symm {m t : ℕ} {i j : Fin (m - 1)} (h : TargetPair t i j) :
    TargetPair t j i := by simpa [TargetPair, Nat.add_comm] using h

theorem rawGraph_noThird (m r p : ℕ) : NoThirdNeighbor (rawGraph m r p) := by
  intro u v w t huv huw hvw hut
  rcases huv.2.2.2 with hvr | hvp <;> rcases huw.2.2.2 with hwr | hwp
  · exact (hvw (target_partner_unique hvr hwr)).elim
  · rcases hut.2.2.2 with htr | htp
    · exact Or.inl (target_partner_unique htr hvr)
    · exact Or.inr (target_partner_unique htp hwp)
  · rcases hut.2.2.2 with htr | htp
    · exact Or.inr (target_partner_unique htr hwr)
    · exact Or.inl (target_partner_unique htp hvp)
  · exact (hvw (target_partner_unique hvp hwp)).elim

theorem rawGraph_noTriangle (m r p : ℕ) : NoTriangle (rawGraph m r p) := by
  intro u v w huv hvw hwu
  rcases huv.2.2.2 with hur | hup <;> rcases hvw.2.2.2 with hvr | hvp
  · exact hwu.1 (target_partner_unique (targetPair_symm hur) hvr).symm
  · rcases hwu.2.2.2 with hwr | hwp
    · exact hvw.1 (target_partner_unique hur (targetPair_symm hwr))
    · exact huv.1 (target_partner_unique (targetPair_symm hvp) hwp).symm
  · rcases hwu.2.2.2 with hwr | hwp
    · exact huv.1 (target_partner_unique (targetPair_symm hvr) hwr).symm
    · exact hvw.1 (target_partner_unique hup (targetPair_symm hwp))
  · exact hwu.1 (target_partner_unique (targetPair_symm hup) hvp).symm

/-- The genuine nonpivot vertex type needed by the mass argument. -/
abbrev FreeVertex (m r p : ℕ) := {i : Fin (m - 1) // IsFree r p i}

def freeGraph (m r p : ℕ) : SimpleGraph (FreeVertex m r p) :=
  (rawGraph m r p).induce {i | IsFree r p i}

theorem noThird_induce {V : Type*} (G : SimpleGraph V) (s : Set V)
    (h : NoThirdNeighbor G) : NoThirdNeighbor (G.induce s) := by
  intro u v w t huv huw hvw hut
  have hn : v.val ≠ w.val := fun he => hvw (Subtype.ext he)
  rcases h u.val v.val w.val t.val huv huw hn hut with he | he
  · exact Or.inl (Subtype.ext he)
  · exact Or.inr (Subtype.ext he)

theorem noTriangle_induce {V : Type*} (G : SimpleGraph V) (s : Set V)
    (h : NoTriangle G) : NoTriangle (G.induce s) := by
  intro u v w huv hvw hwu
  exact h u.val v.val w.val huv hvw hwu

theorem freeGraph_noThird (m r p : ℕ) : NoThirdNeighbor (freeGraph m r p) :=
  noThird_induce _ _ (rawGraph_noThird m r p)

theorem freeGraph_noTriangle (m r p : ℕ) : NoTriangle (freeGraph m r p) :=
  noTriangle_induce _ _ (rawGraph_noTriangle m r p)

/-- Every connected component of a finite degree-two triangle-free graph has
a strict ordered path/cycle representation. -/
noncomputable def componentOrder {V : Type*} [Finite V] (G : SimpleGraph V)
    (hd : NoThirdNeighbor G) (ht : NoTriangle G) (c : G.ConnectedComponent) :
    OrderedComponent c.toSimpleGraph :=
  Classical.choice (exists_orderedComponent _ c.connected_toSimpleGraph
    (noThird_induce G c.supp hd) (noTriangle_induce G c.supp ht))

/-- The connected-component partition covers every physical vertex exactly once. -/
def componentVertexEquiv {V : Type*} (G : SimpleGraph V) :
    (Σ c : G.ConnectedComponent, c) ≃ V where
  toFun x := x.2.val
  invFun v := ⟨G.connectedComponentMk v, ⟨v, rfl⟩⟩
  left_inv := by
    rintro ⟨c, ⟨v, hv⟩⟩
    have hc : G.connectedComponentMk v = c := hv
    subst c
    rfl
  right_inv _ := rfl

/-- Global bijection from strict ordered component positions to original vertices. -/
noncomputable def orderedVertexEquiv {V : Type*} [Finite V] (G : SimpleGraph V)
    (hd : NoThirdNeighbor G) (ht : NoTriangle G) :
    (Σ c : G.ConnectedComponent, Fin ((componentOrder G hd ht c).edges + 1)) ≃ V :=
  (Equiv.sigmaCongrRight (fun c => (componentOrder G hd ht c).label)).trans
    (componentVertexEquiv G)

/-- Actual nonpivot raw components, with proved existence for every parameter. -/
noncomputable def freeComponentOrder (m r p : ℕ) (c : (freeGraph m r p).ConnectedComponent) :
    OrderedComponent c.toSimpleGraph :=
  componentOrder _ (freeGraph_noThird m r p) (freeGraph_noTriangle m r p) c

noncomputable def freeOrderedVertexEquiv (m r p : ℕ) :
    (Σ c : (freeGraph m r p).ConnectedComponent, Fin ((freeComponentOrder m r p c).edges + 1)) ≃
      FreeVertex m r p :=
  orderedVertexEquiv _ (freeGraph_noThird m r p) (freeGraph_noTriangle m r p)

/-- All cycles in the actual free reflection graph have at least four vertices. -/
theorem free_cycle_min (m r p : ℕ) (c : (freeGraph m r p).ConnectedComponent)
    (hc : (freeComponentOrder m r p c).cycle = true) :
    4 ≤ (freeComponentOrder m r p c).edges + 1 := by
  have hh := (freeComponentOrder m r p c).cycle_min hc
  omega

end SubmittedGenus.RawGraph.Topology
