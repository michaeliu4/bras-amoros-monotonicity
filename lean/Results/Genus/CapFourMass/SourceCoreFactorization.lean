import Results.Genus.CapFourMass.SourceCoreRestriction

/-! Exact stable-core factorization by the actual raw connected components. -/
namespace SubmittedGenus.CapFourMass.SourceCoreFactorization
open RawGraph RawGraph.SourceModel RawGraph.Topology FixedPivot
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

abbrev SourceComponent (r N d : ℕ) := (freeGraph (r+N) r (r+d)).ConnectedComponent

def coreVertex {r N d : ℕ} (hN : d<N) (k : CoreFree r (r+d)) : FreeVertex (r+N) r (r+d) :=
  ⟨⟨k.val.val,by have:=k.val.isLt; omega⟩,by exact k.property⟩

@[simp] lemma coreVertex_physical {r N d : ℕ} (hN : d<N) (k : CoreFree r (r+d)) :
    physical (coreVertex hN k).val=k.val.val+1 := rfl

def coreOwner {r N d : ℕ} (hN : d<N) (k : CoreFree r (r+d)) : SourceComponent r N d :=
  (freeGraph (r+N) r (r+d)).connectedComponentMk (coreVertex hN k)

/-- Every nonzero ordinary core constraint stays inside its genuine raw component. -/
lemma coreStrongBound_same_owner {r N d : ℕ} (hN : d<N) (i j : CoreFree r (r+d))
    (h : 0<coreStrongBound r (r+d) i.val j.val) : coreOwner hN i=coreOwner hN j := by
  unfold coreStrongBound at h
  split_ifs at h with hp ht
  · omega
  · apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
    change (coreVertex hN i).val≠(coreVertex hN j).val ∧
      IsFree r (r+d) (coreVertex hN i).val ∧ IsFree r (r+d) (coreVertex hN j).val ∧
      (TargetPair r (coreVertex hN i).val (coreVertex hN j).val ∨
        TargetPair (r+d) (coreVertex hN i).val (coreVertex hN j).val)
    refine ⟨?_,(coreVertex hN i).property,(coreVertex hN j).property,?_⟩
    · intro he
      have he' := congrArg (fun k : Fin (r+N-1) => k.val) he
      have hij : i.val=j.val := Fin.ext he'
      exact hp (Or.inr (Or.inr hij))
    · rcases ht with ht | ht
      · exact Or.inl (Or.inl ht)
      · exact Or.inr (Or.inl ht)
  · omega

abbrev CoreAt {r N d : ℕ} (hN : d<N) (c : SourceComponent r N d) :=
  {k : CoreFree r (r+d) // coreOwner hN k=c}

def coreAssignmentEquiv {r N d : ℕ} (hN : d<N) :
    (CoreFree r (r+d)→State)≃((c : SourceComponent r N d)→CoreAt hN c→State) where
  toFun x c k := x k.val
  invFun x k := x (coreOwner hN k) ⟨k,rfl⟩
  left_inv _ := rfl
  right_inv x := by
    funext c k
    rcases k with ⟨k,hk⟩
    subst c
    rfl

def componentCoreAllowed {r N d : ℕ} (hN : d<N) (c : SourceComponent r N d)
    (x : CoreAt hN c→State) : Prop :=
  (∀ k,CoreDomain r (r+d) k.val.val ((x k).val+1)) ∧
    ∀ k l,coreStrongBound r (r+d) k.val.val l.val.val≤((x k).val+1)+((x l).val+1)

instance {r N d : ℕ} (hN : d<N) (c : SourceComponent r N d)
    (x : CoreAt hN c→State) : Decidable (componentCoreAllowed hN c x) := by
  unfold componentCoreAllowed; infer_instance

/-- The original unary conditions and every ordinary core edge split exactly;
there are no omitted cross-component constraints. -/
theorem freeCoreAllowed_iff_components {r N d : ℕ} (hN : d<N) (x : CoreFree r (r+d)→State) :
    FreeCoreAllowed x ↔ ∀ c,componentCoreAllowed hN c (coreAssignmentEquiv hN x c) := by
  constructor
  · intro h c
    exact ⟨fun k => h.1 k.val,fun k l => h.2 k.val l.val⟩
  · intro h
    constructor
    · intro k
      exact (h (coreOwner hN k)).1 ⟨k,rfl⟩
    · intro k l
      by_cases he : coreOwner hN k=coreOwner hN l
      · exact (h (coreOwner hN k)).2 ⟨k,rfl⟩ ⟨l,he.symm⟩
      · have hz : coreStrongBound r (r+d) k.val l.val=0 := by
          by_contra hz
          exact he (coreStrongBound_same_owner hN k l (Nat.pos_of_ne_zero hz))
        rw [hz]
        exact Nat.zero_le _

section Semiring
variable {R : Type*} [CommSemiring R]

def componentCoreTerm {r N d : ℕ} (hN : d<N) (z : R) (c : SourceComponent r N d)
    (x : CoreAt hN c→State) : R :=
  if componentCoreAllowed hN c x then z^(∑ k,((x k).val+1)) else 0

/-- One full vertex weight for each remaining core coordinate, grouped by its
actual connected component. -/
theorem freeCoreTerm_factor {r N d : ℕ} (hN : d<N) (z : R) (x : CoreFree r (r+d)→State) :
    freeCoreTerm z x=∏ c : SourceComponent r N d,
      componentCoreTerm hN z c (coreAssignmentEquiv hN x c) := by
  by_cases hx : FreeCoreAllowed x
  · have hc:=(freeCoreAllowed_iff_components hN x).mp hx
    simp only [freeCoreTerm,hx,if_true,componentCoreTerm,hc]
    rw [Finset.prod_pow_eq_pow_sum]
    congr 1
    exact (Fintype.sum_fiberwise (coreOwner hN) (fun k => (x k).val+1)).symm
  · have hc : ∃ c,¬componentCoreAllowed hN c (coreAssignmentEquiv hN x c) := by
      by_contra h
      push Not at h
      exact hx ((freeCoreAllowed_iff_components hN x).mpr h)
    obtain ⟨c,hc⟩:=hc
    rw [freeCoreTerm,if_neg hx]
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ c)
    exact if_neg hc

/-- Exact original stable-core sum in physical-component coordinates, with
arbitrary remaining factors retained inside each completed core contraction. -/
theorem stableCore_sum_components {r N d : ℕ} (hr : 0<r) (hd : 0<d) (hN : d<N) (z : R)
    (f : (Fin (r+d)→Fin 5)→R) :
    (∑ x : Fin (r+d)→Fin 5,Polynomial.eval₂ (Nat.castRingHom R) z (stableCoreTerm r (r+d) x)*f x)=
      z^8*∑ x : (c : SourceComponent r N d)→CoreAt hN c→State,
        (∏ c,componentCoreTerm hN z c (x c))*
          f (extendCore hr (show r<r+d by omega) ((coreAssignmentEquiv hN).symm x)) := by
  rw [stableCore_sum_restrict hr (show r<r+d by omega) z]
  congr 1
  calc
    _=∑ x : (c : SourceComponent r N d)→CoreAt hN c→State,
      freeCoreTerm z ((coreAssignmentEquiv hN).symm x)*
        f (extendCore hr (show r<r+d by omega) ((coreAssignmentEquiv hN).symm x)) :=
      ((coreAssignmentEquiv hN).symm.sum_comp _).symm
    _=_ := by
      simp_rw [freeCoreTerm_factor hN z,Equiv.apply_symm_apply]

end Semiring
end
end SubmittedGenus.CapFourMass.SourceCoreFactorization
