import Results.Genus.CapFourMass.ModeVertexPartition

/-! Exact finite sums and products in actual core/tail component coordinates. -/
noncomputable section
open scoped BigOperators
namespace SubmittedGenus.CapFourMass.CarryLocalization
open RawGraph RawGraph.Topology FixedPivot SourceCoreFactorization

section Partition
variable {r N d : ℕ} (hr : 0<r) (hd : 0<d) (hN : d<N) (hbig : 2*d<N)
variable (c : SourceComponent r N d)

/-- Physical spin assignments split into the entire core assignment and all
owned tail assignments, before any contraction or absolute value. -/
def physicalAssignmentEquiv :
    (OwnedVertex c→State)≃((CoreAt hN c→State)×
      ((a : ModeFiber hr hN hbig c)→Fin (carryTailSize N d hN a.val)→State)) where
  toFun x := (fun k => x (componentVertexEquiv hr hd hN hbig c (.inl k)),
    fun a t => x (componentVertexEquiv hr hd hN hbig c (.inr ⟨a,t⟩)))
  invFun x v := match (componentVertexEquiv hr hd hN hbig c).symm v with
    | .inl k => x.1 k
    | .inr ⟨a,t⟩ => x.2 a t
  left_inv x := by
    funext v
    generalize he : (componentVertexEquiv hr hd hN hbig c).symm v=w
    have hv : componentVertexEquiv hr hd hN hbig c w=v := by
      rw [←he,Equiv.apply_symm_apply]
    cases w with
    | inl k => simpa only [he] using congrArg x hv
    | inr w =>
      rcases w with ⟨a,t⟩
      simpa only [he] using congrArg x hv
  right_inv x := by
    apply Prod.ext
    · funext k
      simp only [Equiv.symm_apply_apply]
    · funext a t
      simp only [Equiv.symm_apply_apply]

lemma physical_sum_split {R : Type*} [AddCommMonoid R]
    (f : (OwnedVertex c→State)→R) :
    (∑ x,f x)=∑ core : CoreAt hN c→State,
      ∑ tail : (a : ModeFiber hr hN hbig c)→Fin (carryTailSize N d hN a.val)→State,
        f ((physicalAssignmentEquiv hr hd hN hbig c).symm (core,tail)) := by
  calc
    _=∑ y : (CoreAt hN c→State)×((a : ModeFiber hr hN hbig c)→Fin (carryTailSize N d hN a.val)→State),
      f ((physicalAssignmentEquiv hr hd hN hbig c).symm y) :=
        ((physicalAssignmentEquiv hr hd hN hbig c).symm.sum_comp f).symm
    _=_ := Fintype.sum_prod_type _

lemma physical_product_split {R : Type*} [CommMonoid R] (f : OwnedVertex c→R) :
    (∏ v,f v)=
      (∏ k : CoreAt hN c,f (componentVertexEquiv hr hd hN hbig c (.inl k)))*
        ∏ a : ModeFiber hr hN hbig c,∏ t : Fin (carryTailSize N d hN a.val),
          f (componentVertexEquiv hr hd hN hbig c (.inr ⟨a,t⟩)) := by
  rw [←(componentVertexEquiv hr hd hN hbig c).prod_comp f]
  rw [Fintype.prod_sum_type,Fintype.prod_sigma]

end Partition
end SubmittedGenus.CapFourMass.CarryLocalization
