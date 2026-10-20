import Results.Genus.FixedPivot.CoreSource
import Results.Genus.CapFourMass.ModeFubini
import Results.Genus.CapFourMass.SpectralMatrices

/-! Remove exactly the two fixed maximum-four coordinates from the actual stable core. -/
namespace SubmittedGenus.CapFourMass.SourceCoreFactorization
open RawGraph RawGraph.SourceModel RawGraph.Topology FixedPivot
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

abbrev CoreFree (r p : ℕ) := FreeVertex (p+1) r p

theorem coreParameters {r p : ℕ} (hr : 0<r) (hrp : r<p) : Parameters (p+1) r p 4 :=
  ⟨hr,hrp,by omega,Or.inl rfl⟩

def corePositive (v : State) : Fin 5 := ⟨v.val+1,by have:=v.isLt; omega⟩

def extendCore {r p : ℕ} (hr : 0<r) (hrp : r<p) (x : CoreFree r p→State) (k : Fin p) : Fin 5 :=
  match (pivotFreeEquiv (coreParameters hr hrp)).symm k with
  | .inl _ => 4
  | .inr j => corePositive (x j)

@[simp] lemma extendCore_pivot {r p : ℕ} (hr : 0<r) (hrp : r<p)
    (x : CoreFree r p→State) (b : Bool) :
    extendCore hr hrp x (pivotVertex (coreParameters hr hrp) b)=4 := by
  change extendCore hr hrp x ((pivotFreeEquiv (coreParameters hr hrp)) (.inl b))=4
  simp only [extendCore,Equiv.symm_apply_apply]

@[simp] lemma extendCore_free {r p : ℕ} (hr : 0<r) (hrp : r<p)
    (x : CoreFree r p→State) (j : CoreFree r p) :
    extendCore hr hrp x j.val=corePositive (x j) := by
  change extendCore hr hrp x ((pivotFreeEquiv (coreParameters hr hrp)) (.inr j))=corePositive (x j)
  simp only [extendCore,Equiv.symm_apply_apply]

def CoreSupported {r p : ℕ} (hr : 0<r) (hrp : r<p) (x : Fin p→Fin 5) : Prop :=
  (∀ b,x (pivotVertex (coreParameters hr hrp) b)=4) ∧
    ∀ j : CoreFree r p,0<(x j.val).val

lemma stableCore_supported {r p : ℕ} (hr : 0<r) (hrp : r<p) (x : Fin p→Fin 5)
    (hx : StableCoreAllowed r p x) : CoreSupported hr hrp x := by
  constructor
  · intro b
    apply Fin.ext
    have hh:=(hx.1 (pivotVertex (coreParameters hr hrp) b)).1
    apply hh
    have hv:=physical_pivotVertex (coreParameters hr hrp) b
    change (pivotVertex (coreParameters hr hrp) b).val+1=Incidence.target r p b at hv
    cases b <;> simp only [Incidence.target,Bool.false_eq_true,if_false,if_true] at hv
    · exact Or.inl hv
    · exact Or.inr hv
  · intro j
    exact ((hx.1 j.val).2 j.property).1

def supportedCoreEquiv {r p : ℕ} (hr : 0<r) (hrp : r<p) :
    (CoreFree r p→State)≃{x : Fin p→Fin 5 // CoreSupported hr hrp x} where
  toFun x := ⟨extendCore hr hrp x,by
    constructor
    · intro b; exact extendCore_pivot hr hrp x b
    · intro j; rw [extendCore_free]; exact Nat.succ_pos _⟩
  invFun x j := ⟨(x.val j.val).val-1,by have:=x.property.2 j; have:=(x.val j.val).isLt; omega⟩
  left_inv x := by
    funext j
    apply Fin.ext
    simp only [extendCore_free,corePositive]
    omega
  right_inv x := by
    apply Subtype.ext
    funext k
    obtain ⟨u,rfl⟩:=(pivotFreeEquiv (coreParameters hr hrp)).surjective k
    cases u with
    | inl b =>
      change extendCore hr hrp _ (pivotVertex (coreParameters hr hrp) b)=x.val (pivotVertex (coreParameters hr hrp) b)
      exact (extendCore_pivot hr hrp _ b).trans (x.property.1 b).symm
    | inr j =>
      change extendCore hr hrp _ j.val=x.val j.val
      rw [extendCore_free]
      apply Fin.ext
      have:=x.property.2 j
      simp only [corePositive]
      omega

lemma sum_restrict_core {R : Type*} [AddCommMonoid R] {r p : ℕ}
    (hr : 0<r) (hrp : r<p) (f : (Fin p→Fin 5)→R)
    (hf : ∀ x,¬CoreSupported hr hrp x → f x=0) :
    (∑ x,f x)=∑ x : CoreFree r p→State,f (extendCore hr hrp x) := by
  calc
    (∑ x,f x)=∑ x,if CoreSupported hr hrp x then f x else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      split_ifs with h
      · rfl
      · exact hf x h
    _=∑ x : {x : Fin p→Fin 5 // CoreSupported hr hrp x},f x.val := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype (Finset.univ.filter (CoreSupported hr hrp)) (by simp) f
    _=∑ x : CoreFree r p→State,f (extendCore hr hrp x) :=
      ((supportedCoreEquiv hr hrp).sum_comp (fun x => f x.val)).symm

def FreeCoreAllowed {r p : ℕ} (x : CoreFree r p→State) : Prop :=
  (∀ j,CoreDomain r p j.val ((x j).val+1)) ∧
    ∀ i j,coreStrongBound r p i.val j.val≤((x i).val+1)+((x j).val+1)

instance {r p : ℕ} (x : CoreFree r p→State) : Decidable (FreeCoreAllowed x) := by
  unfold FreeCoreAllowed; infer_instance

lemma coreDomain_pivot {r p : ℕ} (hr : 0<r) (hrp : r<p) (b : Bool) :
    CoreDomain r p (pivotVertex (coreParameters hr hrp) b) 4 := by
  have hv:=physical_pivotVertex (coreParameters hr hrp) b
  have hpiv : (pivotVertex (coreParameters hr hrp) b).val+1=r ∨
      (pivotVertex (coreParameters hr hrp) b).val+1=p := by
    change (pivotVertex (coreParameters hr hrp) b).val+1=Incidence.target r p b at hv
    cases b <;> simp only [Incidence.target,Bool.false_eq_true,if_false,if_true] at hv
    · exact Or.inl hv
    · exact Or.inr hv
  simp only [CoreDomain,hpiv,true_implies,not_true_eq_false,false_implies,and_true]

lemma coreStrongBound_pivot_left {r p : ℕ} (hr : 0<r) (hrp : r<p) (b : Bool) (k : Fin p) :
    coreStrongBound r p (pivotVertex (coreParameters hr hrp) b) k=0 := by
  have hv:=physical_pivotVertex (coreParameters hr hrp) b
  unfold coreStrongBound
  apply if_pos
  left
  change (pivotVertex (coreParameters hr hrp) b).val+1=Incidence.target r p b at hv
  cases b <;> simp only [Incidence.target,Bool.false_eq_true,if_false,if_true] at hv
  · exact Or.inl hv
  · exact Or.inr hv

lemma coreStrongBound_symm {r p : ℕ} (i j : Fin p) :
    coreStrongBound r p i j=coreStrongBound r p j i := by
  simp only [coreStrongBound,eq_comm,or_comm,or_left_comm,or_assoc,add_comm]

lemma stableCore_extend_iff {r p : ℕ} (hr : 0<r) (hrp : r<p) (x : CoreFree r p→State) :
    StableCoreAllowed r p (extendCore hr hrp x) ↔ FreeCoreAllowed x := by
  constructor
  · intro h
    constructor
    · intro j
      simpa only [extendCore_free,corePositive] using h.1 j.val
    · intro i j
      simpa only [extendCore_free,corePositive] using h.2 i.val j.val
  · intro h
    constructor
    · intro k
      obtain ⟨u,rfl⟩:=(pivotFreeEquiv (coreParameters hr hrp)).surjective k
      cases u with
      | inl b =>
        change CoreDomain r p (pivotVertex (coreParameters hr hrp) b)
          (extendCore hr hrp x (pivotVertex (coreParameters hr hrp) b)).val
        rw [extendCore_pivot]
        exact coreDomain_pivot hr hrp b
      | inr j =>
        change CoreDomain r p j.val (extendCore hr hrp x j.val).val
        simpa only [extendCore_free,corePositive] using h.1 j
    · intro k l
      obtain ⟨u,rfl⟩:=(pivotFreeEquiv (coreParameters hr hrp)).surjective k
      obtain ⟨v,rfl⟩:=(pivotFreeEquiv (coreParameters hr hrp)).surjective l
      cases u with
      | inl b => exact (coreStrongBound_pivot_left hr hrp b _).le.trans (Nat.zero_le _)
      | inr i =>
        cases v with
        | inl b => exact ((coreStrongBound_symm _ _).trans (coreStrongBound_pivot_left hr hrp b _)).le.trans (Nat.zero_le _)
        | inr j =>
          change coreStrongBound r p i.val j.val≤(extendCore hr hrp x i.val).val+(extendCore hr hrp x j.val).val
          simpa only [extendCore_free,corePositive] using h.2 i j

lemma extendCore_weight {r p : ℕ} (hr : 0<r) (hrp : r<p) (x : CoreFree r p→State) :
    (∑ k : Fin p,(extendCore hr hrp x k).val)=8+∑ j : CoreFree r p,((x j).val+1) := by
  calc
    _=∑ u : Bool ⊕ CoreFree r p,(extendCore hr hrp x ((pivotFreeEquiv (coreParameters hr hrp)) u)).val :=
      ((pivotFreeEquiv (coreParameters hr hrp)).sum_comp (fun k => (extendCore hr hrp x k).val)).symm
    _=8+∑ j : CoreFree r p,((x j).val+1) := by
      rw [Fintype.sum_sum_type]
      have hleft : ∀ b,(extendCore hr hrp x (pivotFreeEquiv (coreParameters hr hrp) (.inl b))).val=4 := by
        intro b; exact congrArg Fin.val (extendCore_pivot hr hrp x b)
      have hright : ∀ j,(extendCore hr hrp x (pivotFreeEquiv (coreParameters hr hrp) (.inr j))).val=(x j).val+1 := by
        intro j; exact congrArg Fin.val (extendCore_free hr hrp x j)
      simp only [hleft,hright]
      simp

section Semiring
variable {R : Type*} [CommSemiring R]

def freeCoreTerm {r p : ℕ} (z : R) (x : CoreFree r p→State) : R :=
  if FreeCoreAllowed x then z^(∑ j,((x j).val+1)) else 0

lemma stableCoreTerm_extend {r p : ℕ} (hr : 0<r) (hrp : r<p) (z : R) (x : CoreFree r p→State) :
    Polynomial.eval₂ (Nat.castRingHom R) z (stableCoreTerm r p (extendCore hr hrp x))=
      z^8*freeCoreTerm z x := by
  by_cases hx : FreeCoreAllowed x
  · have hs:=(stableCore_extend_iff hr hrp x).mpr hx
    simp only [stableCoreTerm,freeCoreTerm,hs,hx,if_true,Polynomial.eval₂_X_pow]
    rw [extendCore_weight,pow_add]
  · have hs : ¬StableCoreAllowed r p (extendCore hr hrp x) :=
      fun h => hx ((stableCore_extend_iff hr hrp x).mp h)
    simp only [stableCoreTerm,freeCoreTerm,hs,hx,if_false,Polynomial.eval₂_zero,mul_zero]

/-- Exact core restriction with arbitrary remaining factors. Both pivots retain
one weight each, giving precisely z^8 outside the remaining core contraction. -/
theorem stableCore_sum_restrict {r p : ℕ} (hr : 0<r) (hrp : r<p) (z : R)
    (f : (Fin p→Fin 5)→R) :
    (∑ x : Fin p→Fin 5,Polynomial.eval₂ (Nat.castRingHom R) z (stableCoreTerm r p x)*f x)=
      z^8*∑ x : CoreFree r p→State,freeCoreTerm z x*f (extendCore hr hrp x) := by
  rw [sum_restrict_core hr hrp _ (by
    intro x hx
    have hn : ¬StableCoreAllowed r p x := fun h => hx (stableCore_supported hr hrp x h)
    simp [stableCoreTerm,hn])]
  simp_rw [stableCoreTerm_extend hr hrp z,mul_assoc]
  rw [Finset.mul_sum]

end Semiring
end
end SubmittedGenus.CapFourMass.SourceCoreFactorization
