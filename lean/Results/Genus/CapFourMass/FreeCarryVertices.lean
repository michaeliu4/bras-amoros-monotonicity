import Results.Genus.CapFourMass.FreeCarryLayout

/-! The canonical retained carry layout on actual free physical coordinates. -/
noncomputable section
namespace SubmittedGenus.CapFourMass.CarryLocalization
open RawGraph RawGraph.SourceModel RawGraph.Topology FixedPivot

section Physical
variable {r N d : ℕ} (hr : 0<r) (hd : 0<d) (hN : d<N)

/-- A retained carry-run position denotes one original physical free vertex. -/
def runVertex (a : CarryRepresentative N d hN) (t : Fin (freeCarrySize N d hN a)) :
    FreeVertex (r+N) r (r+d) := by
  let x:=freeCarryLabel N d hN a t.val
  have hx : 0<x ∧ x<N ∧ x≠d := freeCarryLabel_vertex N d hN a t.isLt
  refine ⟨⟨r+x-1,by omega⟩,?_⟩
  change ¬(r+x-1+1=r ∨ r+x-1+1=r+d)
  omega

lemma runVertex_physical (a : CarryRepresentative N d hN) (t : Fin (freeCarrySize N d hN a)) :
    physical (runVertex hr hN a t).val=r+freeCarryLabel N d hN a t.val := by
  have hx:=freeCarryLabel_vertex N d hN a t.isLt
  change r+freeCarryLabel N d hN a t.val-1+1=_
  omega

lemma runVertex_high (a : CarryRepresentative N d hN) (t : Fin (freeCarrySize N d hN a)) :
    r<physical (runVertex hr hN a t).val := by
  rw [runVertex_physical]
  have hx:=freeCarryLabel_vertex N d hN a t.isLt
  omega

include hd in
lemma runVertex_injective : Function.Injective
    (fun v : Σ a : CarryRepresentative N d hN,Fin (freeCarrySize N d hN a) =>
      runVertex hr hN v.1 v.2) := by
  intro v w he
  have hv:=congrArg (fun i : FreeVertex (r+N) r (r+d) => physical i.val) he
  rw [runVertex_physical,runVertex_physical] at hv
  apply freeCarryMap_injective N d hd hN
  apply Subtype.ext
  change freeCarryLabel N d hN v.1 v.2.val=freeCarryLabel N d hN w.1 w.2.val
  omega

end Physical

/-- The actual high free vertices and canonical carry-run positions coincide. -/
def highVertexEquiv (r N d : ℕ) : {x : ℕ // 0<x ∧ x<N ∧ x≠d} ≃
    {v : FreeVertex (r+N) r (r+d) // r<physical v.val} where
  toFun x := ⟨⟨⟨r+x.val-1,by have := x.property; omega⟩,by
    change ¬(r+x.val-1+1=r ∨ r+x.val-1+1=r+d)
    have := x.property
    omega⟩,by change r<r+x.val-1+1; have := x.property; omega⟩
  invFun v := ⟨physical v.val.val-r,by
    have hv:=v.val.val.isLt
    have hh:=v.property
    have hf:=v.val.property
    change ¬(physical v.val.val=r ∨ physical v.val.val=r+d) at hf
    unfold physical at *
    omega⟩
  left_inv x := by
    apply Subtype.ext
    change r+x.val-1+1-r=x.val
    have := x.property
    omega
  right_inv v := by
    apply Subtype.ext
    apply Subtype.ext
    apply Fin.ext
    change r+(v.val.val.val+1-r)-1=v.val.val.val
    have hv:=v.property
    unfold physical at hv
    omega

section Physical
variable {r N d : ℕ} (hr : 0<r) (hd : 0<d) (hN : d<N)

def runVertexEquiv :
    (Σ a : CarryRepresentative N d hN,Fin (freeCarrySize N d hN a)) ≃
      {v : FreeVertex (r+N) r (r+d) // r<physical v.val} :=
  (freeCarryEquiv N d hd hN).trans (highVertexEquiv r N d)

@[simp] lemma runVertexEquiv_apply
    (v : Σ a : CarryRepresentative N d hN,Fin (freeCarrySize N d hN a)) :
    (runVertexEquiv (r:=r) hd hN v).val=runVertex hr hN v.1 v.2 := rfl

/-- A retained carry incidence between distinct physical vertices. -/
def CarryAdj (u v : FreeVertex (r+N) r (r+d)) : Prop :=
  u≠v ∧ (physical u.val+physical v.val=(r+N)+r ∨
    physical u.val+physical v.val=(r+N)+(r+d))

lemma CarryAdj.adj {u v : FreeVertex (r+N) r (r+d)} (h : CarryAdj u v) :
    (freeGraph (r+N) r (r+d)).Adj u v := by
  change (u.val≠v.val ∧ IsFree r (r+d) u.val ∧ IsFree r (r+d) v.val ∧
    (TargetPair r u.val v.val ∨ TargetPair (r+d) u.val v.val))
  refine ⟨fun he => h.1 (Subtype.ext he),u.property,v.property,?_⟩
  exact h.2.elim (fun he => Or.inl (Or.inr he)) (fun he => Or.inr (Or.inr he))

include hd in
/-- The exact positive-edge carry runs have consecutive incidence and no
extra edges. Their final loops remain unary source constraints. -/
theorem run_carry_adj_iff (a : CarryRepresentative N d hN)
    (t s : Fin (freeCarrySize N d hN a)) :
    CarryAdj (runVertex hr hN a t) (runVertex hr hN a s) ↔
      t.val+1=s.val ∨ s.val+1=t.val := by
  have hh:=freeCarry_incidence_iff N d hN a t.isLt s.isLt
  constructor
  · rintro ⟨hne,he⟩
    rw [runVertex_physical,runVertex_physical] at he
    have hinc : CarryIncidence N d (freeCarryLabel N d hN a t.val)
        (freeCarryLabel N d hN a s.val) := by unfold CarryIncidence; omega
    rcases hh.mp hinc with h | h | ⟨_,ht,hs⟩
    · exact Or.inl h
    · exact Or.inr h
    · exact False.elim (hne (congrArg (runVertex hr hN a) (Fin.ext (ht.trans hs.symm))))
  · intro he
    refine ⟨?_,?_⟩
    · intro hv
      have ht := runVertex_injective hr hd hN (a₁:=⟨a,t⟩) (a₂:=⟨a,s⟩) hv
      have hts : t=s := by cases ht; rfl
      have := congrArg Fin.val hts
      omega
    · rw [runVertex_physical,runVertex_physical]
      have hinc:=hh.mpr (he.elim Or.inl (fun h => Or.inr (Or.inl h)))
      unfold CarryIncidence at hinc
      omega

include hd in
/-- Distinct canonical runs never share an actual carry edge. -/
theorem carry_adj_same_run (a b : CarryRepresentative N d hN)
    (t : Fin (freeCarrySize N d hN a)) (s : Fin (freeCarrySize N d hN b))
    (h : CarryAdj (runVertex hr hN a t) (runVertex hr hN b s)) : a=b := by
  have he:=h.2
  rw [runVertex_physical,runVertex_physical] at he
  apply freeCarry_incidence_same N d hd hN a b t s
  unfold CarryIncidence
  omega

end Physical
end SubmittedGenus.CapFourMass.CarryLocalization
