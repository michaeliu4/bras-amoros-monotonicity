import Results.Genus.RawGraph.ComponentEdgeSlots

/-! Exact evaluation over physical unordered edges in a proved component order. -/
noncomputable section
open scoped BigOperators
namespace SubmittedGenus.RawGraph.Topology.OrderedComponent
variable {V R : Type*} {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj] [CommMonoid R]

lemma edge_product_eq_ordered (O : OrderedComponent G) (w : Sym2 V→R) :
    (∏ e : G.edgeSet,w e.val)=
      (∏ k : Fin O.edges,w s(O.label k.castSucc,O.label k.succ))*
        (if O.cycle=true then w s(O.label (Fin.last O.edges),O.label 0) else 1) := by
  classical
  have hclose : (∏ _u : {_u : Unit // O.cycle=true},w s(O.label (Fin.last O.edges),O.label 0))=
      if O.cycle=true then w s(O.label (Fin.last O.edges),O.label 0) else 1 := by
    by_cases hc : O.cycle=true
    · letI : Unique {_u : Unit // O.cycle=true}:=⟨⟨⟨(),hc⟩⟩,fun u => Subtype.ext (Subsingleton.elim _ _)⟩
      simp only [Fintype.prod_unique,if_pos hc]
    · letI : IsEmpty {_u : Unit // O.cycle=true}:=⟨fun u => hc u.property⟩
      simp [hc]
  rw [←O.edgeSlotEquiv.prod_comp (fun e => w e.val),Fintype.prod_sum_type]
  change (∏ k : Fin O.edges,w s(O.label k.castSucc,O.label k.succ))*
    (∏ _u : {_u : Unit // O.cycle=true},w s(O.label (Fin.last O.edges),O.label 0))=_
  rw [hclose]

end SubmittedGenus.RawGraph.Topology.OrderedComponent
