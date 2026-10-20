import Results.Genus.CapFourMass.SourceCoreProduct
import Results.Genus.CapFourMass.ModeVertexPartition

/-! Ordinary source edges are exactly the upper-ordered free core edges. -/
noncomputable section
namespace SubmittedGenus.CapFourMass.CarryLocalization
open RawGraph RawGraph.Topology FixedPivot SourceCoreFactorization
attribute [local instance] Classical.propDecidable Classical.decEq

section Partition
variable {r N d : ℕ} (hr : 0<r) (hd : 0<d) (hN : d<N)
variable (c : SourceComponent r N d)

def strongGraph : SimpleGraph c where
  Adj u v := StrongRuns.StrongStep r (r+d) u.val.val v.val.val
  symm := ⟨fun _ _ h => StrongRuns.strongStep_symm h⟩
  loopless := ⟨fun _ h => h.1.1 rfl⟩

def ownedCoreVertex (k : CoreAt hN c) : c := ⟨coreVertex hN k.val,k.property⟩

lemma ownedCoreVertex_injective : Function.Injective (ownedCoreVertex hN c) := by
  intro k l he
  apply Subtype.ext
  apply Subtype.ext
  apply Fin.ext
  exact congrArg (fun v : c => v.val.val.val) he

lemma core_positive_strong (i j : CoreAt hN c)
    (h : 0<coreStrongBound r (r+d) i.val.val j.val.val) :
    (strongGraph c).Adj (ownedCoreVertex hN c i) (ownedCoreVertex hN c j) := by
  unfold coreStrongBound at h
  split_ifs at h with hp ht
  · omega
  · refine ⟨⟨?_,i.val.property,j.val.property,?_⟩,ht⟩
    · intro he
      have hv:=congrArg Fin.val he
      exact hp (Or.inr (Or.inr (Fin.ext hv)))
    · exact ht.elim (fun h => Or.inl (Or.inl h)) (fun h => Or.inr (Or.inl h))
  · omega

lemma core_strong_positive (i j : CoreAt hN c)
    (h : (strongGraph c).Adj (ownedCoreVertex hN c i) (ownedCoreVertex hN c j)) :
    0<coreStrongBound r (r+d) i.val.val j.val.val := by
  have hij : i.val.val≠j.val.val := by
    intro he
    have hv : i.val.val.val=j.val.val.val:=congrArg (fun k : Fin (r+d+1-1) => k.val) he
    apply h.1.1
    apply Fin.ext
    exact hv
  have hi : ¬(i.val.val.val+1=r ∨ i.val.val.val+1=r+d):=i.val.property
  have hj : ¬(j.val.val.val+1=r ∨ j.val.val.val+1=r+d):=j.val.property
  have ht:=h.2
  change (i.val.val.val+1)+(j.val.val.val+1)=r ∨ (i.val.val.val+1)+(j.val.val.val+1)=r+d at ht
  unfold coreStrongBound
  rw [if_neg (fun hh => hh.elim hi (fun hh => hh.elim hj hij)),if_pos ht]
  norm_num

def coreSlotEdge (ij : {ij // ij∈coreEdgeSet hN c}) : (strongGraph c).edgeSet :=
  ⟨s(ownedCoreVertex hN c ij.val.1,ownedCoreVertex hN c ij.val.2),
    core_positive_strong hN c _ _ ((mem_coreEdgeSet hN c ij.val).mp ij.property).2⟩

lemma coreSlotEdge_injective : Function.Injective (coreSlotEdge hN c) := by
  intro a b he
  have hh:=congrArg Subtype.val he
  change s(ownedCoreVertex hN c a.val.1,ownedCoreVertex hN c a.val.2)=
    s(ownedCoreVertex hN c b.val.1,ownedCoreVertex hN c b.val.2) at hh
  rcases Sym2.eq_iff.mp hh with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · apply Subtype.ext
    exact Prod.ext (ownedCoreVertex_injective hN c h1) (ownedCoreVertex_injective hN c h2)
  · have h1':=congrArg (fun v : c => v.val.val.val) h1
    have h2':=congrArg (fun v : c => v.val.val.val) h2
    have ha:=((mem_coreEdgeSet hN c a.val).mp a.property).1
    have hb:=((mem_coreEdgeSet hN c b.val).mp b.property).1
    change a.val.1.val.val.val=b.val.2.val.val.val at h1'
    change a.val.2.val.val.val=b.val.1.val.val.val at h2'
    omega

def coreOfOwned (u : c) (hu : physical u.val.val≤r+d) : CoreAt hN c := by
  let k : CoreFree r (r+d):=⟨⟨u.val.val.val,by unfold physical at hu; omega⟩,u.val.property⟩
  exact ⟨k,u.property⟩

@[simp] lemma ownedCoreVertex_coreOfOwned (u : c) (hu : physical u.val.val≤r+d) :
    ownedCoreVertex hN c (coreOfOwned hN c u hu)=u := by
  apply Subtype.ext
  apply Subtype.ext
  apply Fin.ext
  rfl

include hr hd in
lemma coreSlotEdge_surjective : Function.Surjective (coreSlotEdge hN c) := by
  rintro ⟨e,he⟩
  induction e using Sym2.ind with
  | h u v =>
    have hs : StrongRuns.StrongStep r (r+d) u.val.val v.val.val:=he
    have hu:=(StrongRuns.strong_endpoint_lt_p (canonicalParameters hr hd hN) hs).le
    have hv:=(StrongRuns.strong_endpoint_lt_p (canonicalParameters hr hd hN) (StrongRuns.strongStep_symm hs)).le
    let i:=coreOfOwned hN c u hu
    let j:=coreOfOwned hN c v hv
    have hi : ownedCoreVertex hN c i=u:=ownedCoreVertex_coreOfOwned hN c u hu
    have hj : ownedCoreVertex hN c j=v:=ownedCoreVertex_coreOfOwned hN c v hv
    have hp : 0<coreStrongBound r (r+d) i.val.val j.val.val :=
      core_strong_positive hN c i j (by rwa [hi,hj])
    have hn : i.val.val.val≠j.val.val.val := by
      intro hij
      have hk : i=j:=Subtype.ext (Subtype.ext (Fin.ext hij))
      have hh : u=v:=hi.symm.trans ((congrArg (ownedCoreVertex hN c) hk).trans hj)
      exact hs.1.1 (congrArg (fun v : c => v.val.val) hh)
    rcases lt_or_gt_of_ne hn with hlt | hgt
    · refine ⟨⟨(i,j),(mem_coreEdgeSet hN c _).mpr ⟨hlt,hp⟩⟩,Subtype.ext ?_⟩
      change s(ownedCoreVertex hN c i,ownedCoreVertex hN c j)=s(u,v)
      rw [hi,hj]
    · have hp' : 0<coreStrongBound r (r+d) j.val.val i.val.val := by
        rwa [coreStrongBound_symm]
      refine ⟨⟨(j,i),(mem_coreEdgeSet hN c _).mpr ⟨hgt,hp'⟩⟩,Subtype.ext ?_⟩
      change s(ownedCoreVertex hN c j,ownedCoreVertex hN c i)=s(u,v)
      rw [hi,hj]
      exact Sym2.eq_swap

/-- Exact ordinary edge equivalence, preserving one signed factor per edge. -/
def coreEdgeEquiv : {ij // ij∈coreEdgeSet hN c}≃(strongGraph c).edgeSet :=
  Equiv.ofBijective (coreSlotEdge hN c)
    ⟨coreSlotEdge_injective hN c,coreSlotEdge_surjective hr hd hN c⟩

end Partition
end SubmittedGenus.CapFourMass.CarryLocalization
