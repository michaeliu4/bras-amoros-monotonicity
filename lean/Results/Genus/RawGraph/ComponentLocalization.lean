import Results.Genus.RawGraph.RawComponents
import Results.Genus.RawGraph.ComponentEdgeCount

namespace SubmittedGenus.RawGraph.Topology
open SimpleGraph

/-- An adjacency-supported relation is partitioned exactly by the genuine
connected components and their proved ordered labels. -/
theorem relation_component_card {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hd : NoThirdNeighbor G) (ht : NoTriangle G)
    (R : V → V → Prop) [DecidableRel R]
    [Fintype G.ConnectedComponent]
    (hsub : ∀ u v, R u v → G.Adj u v) :
    (Finset.univ.filter (fun uv : V × V => R uv.1 uv.2)).card =
    ∑ c : G.ConnectedComponent,
      (Finset.univ.filter (fun ij : Fin ((componentOrder G hd ht c).edges + 1) ×
          Fin ((componentOrder G hd ht c).edges + 1) =>
        R ((componentOrder G hd ht c).label ij.1).val
          ((componentOrder G hd ht c).label ij.2).val)).card := by
  classical
  let A := Σ c : G.ConnectedComponent,
    {ij : Fin ((componentOrder G hd ht c).edges + 1) ×
        Fin ((componentOrder G hd ht c).edges + 1) //
      R ((componentOrder G hd ht c).label ij.1).val
        ((componentOrder G hd ht c).label ij.2).val}
  let B := {uv : V × V // R uv.1 uv.2}
  let f : A → B := fun x =>
    ⟨(((componentOrder G hd ht x.1).label x.2.val.1).val,
      ((componentOrder G hd ht x.1).label x.2.val.2).val), x.2.property⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨c,⟨⟨i,j⟩,hr⟩⟩ ⟨d,⟨⟨k,l⟩,hs⟩⟩ he
      have hu : ((componentOrder G hd ht c).label i).val =
          ((componentOrder G hd ht d).label k).val :=
        congrArg (fun x : B => x.val.1) he
      have hc := ((componentOrder G hd ht c).label i).property
      have hd' := ((componentOrder G hd ht d).label k).property
      have hcd : c = d := by
        change G.connectedComponentMk _ = c at hc
        change G.connectedComponentMk _ = d at hd'
        rw [hu] at hc
        exact hc.symm.trans hd'
      subst d
      have hi : i = k := (componentOrder G hd ht c).label.injective (Subtype.ext hu)
      have hv : ((componentOrder G hd ht c).label j).val =
          ((componentOrder G hd ht c).label l).val :=
        congrArg (fun x : B => x.val.2) he
      have hj : j = l := (componentOrder G hd ht c).label.injective (Subtype.ext hv)
      subst k; subst l
      rfl
    · rintro ⟨⟨u,v⟩,hr⟩
      let c := G.connectedComponentMk u
      let u' : c := ⟨u,rfl⟩
      have hv : G.connectedComponentMk v = c :=
        (ConnectedComponent.connectedComponentMk_eq_of_adj (hsub u v hr)).symm
      let v' : c := ⟨v,hv⟩
      let o := componentOrder G hd ht c
      let i := o.label.symm u'
      let j := o.label.symm v'
      have hi : o.label i = u' := o.label.apply_symm_apply u'
      have hj : o.label j = v' := o.label.apply_symm_apply v'
      have hp : R (o.label i).val (o.label j).val := by simpa [hi,hj] using hr
      refine ⟨⟨c,⟨(i,j),hp⟩⟩, ?_⟩
      apply Subtype.ext
      change ((o.label i).val, (o.label j).val) = (u,v)
      simp [hi,hj,u',v']
  have hc := Fintype.card_congr (Equiv.ofBijective f hf)
  simp only [A, B, Fintype.card_sigma, Fintype.card_subtype] at hc
  exact hc.symm

end SubmittedGenus.RawGraph.Topology
