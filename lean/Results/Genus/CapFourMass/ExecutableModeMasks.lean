import Results.Genus.CapFourMass.SignedUnaryMasks

/-! Exact signed unary-mask removal in an arbitrary supplied ordering of an
actual free component. No choice-based component order is used here. -/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFourMass.ExecutableModes.OrderedSource
open RawGraph RawGraph.SourceModel RawGraph.Topology ActualComponent
attribute [local instance] Classical.propDecidable Classical.decEq

variable {m r p : ℕ} (c : Component m r p) (O : OrderedComponent c.toSimpleGraph)

def vertex (j : Fin (O.edges+1)) : Fin (m-1) := (O.label j).val.val

def kernelProduct (K : Fin (m-1)→Fin (m-1)→State→State→ℝ)
    (x : Fin (O.edges+1)→State) : ℝ :=
  (∏ j : Fin O.edges,K (vertex c O j.castSucc) (vertex c O j.succ)
    (x j.castSucc) (x j.succ))*
    (if O.cycle=true then K (vertex c O (Fin.last _)) (vertex c O 0)
      (x (Fin.last _)) (x 0) else 1)

def BoundaryAllowed (x : Fin (O.edges+1)→State) : Prop :=
  O.cycle=false → Domain r p 4 (vertex c O 0) ((x 0).val+1) ∧
    Domain r p 4 (vertex c O (Fin.last _)) ((x (Fin.last _)).val+1)

lemma vertex_injective : Function.Injective (vertex c O) := by
  intro i j he
  exact O.label.injective (Subtype.ext (Subtype.ext he))

section Kernel
variable (K : Fin (m-1)→Fin (m-1)→State→State→ℝ)
variable (hsym : ∀ i j v w,K i j v w=K j i w v)
variable (hsupport : ∀ i j,StrongRuns.CarryStep r p i j → ∀ v w,K i j v w≠0 → v.val+1 ≤ 3)

include hsym
lemma kernelProduct_nonzero_all (x : Fin (O.edges+1)→State)
    (hprod : kernelProduct c O K x≠0) :
    ∀ i j,(rawGraph m r p).Adj (vertex c O i) (vertex c O j) →
      K (vertex c O i) (vertex c O j) (x i) (x j)≠0 := by
  have hpath : ∀ j : Fin (O.edges),K (vertex c O j.castSucc) (vertex c O j.succ) (x j.castSucc) (x j.succ)≠0 :=
    fun j => (Finset.prod_ne_zero_iff.mp (mul_ne_zero_iff.mp hprod).1) j (Finset.mem_univ j)
  have hclose : O.cycle=true →
      K (vertex c O (Fin.last _)) (vertex c O 0) (x (Fin.last _)) (x 0)≠0 := by
    intro hc
    simpa only [kernelProduct,if_pos hc] using (mul_ne_zero_iff.mp hprod).2
  intro i j he
  have hh:=(O.adjacent_iff i j).mp he
  rcases hh with hij | hji | ⟨hc,hh⟩
  · have hi : i.val<O.edges := by have := j.isLt; omega
    have hi' : i=Fin.castSucc (⟨i.val,hi⟩ : Fin (O.edges)) := Fin.ext rfl
    have hj' : j=Fin.succ (⟨i.val,hi⟩ : Fin (O.edges)) := Fin.ext hij.symm
    simpa only [←hi',←hj'] using hpath ⟨i.val,hi⟩
  · have hj : j.val<O.edges := by have := i.isLt; omega
    have hj' : j=Fin.castSucc (⟨j.val,hj⟩ : Fin (O.edges)) := Fin.ext rfl
    have hi' : i=Fin.succ (⟨j.val,hj⟩ : Fin (O.edges)) := Fin.ext hji.symm
    rw [hsym]
    simpa only [←hi',←hj'] using hpath ⟨j.val,hj⟩
  · rcases hh with ⟨hi,hj⟩ | ⟨hj,hi⟩
    · have hi' : i=0 := Fin.ext hi
      have hj' : j=Fin.last (O.edges) := Fin.ext hj
      rw [hi',hj',hsym]
      exact hclose hc
    · have hi' : i=Fin.last (O.edges) := Fin.ext hi
      have hj' : j=0 := Fin.ext hj
      rw [hi',hj']
      exact hclose hc

include hsupport
lemma boundary_implies_domains (x : Fin (O.edges+1)→State)
    (hb : BoundaryAllowed c O x) (hprod : kernelProduct c O K x≠0) :
    ∀ i,Domain r p 4 (vertex c O i) ((x i).val+1) := by
  have he:=kernelProduct_nonzero_all c O K hsym x hprod
  intro i
  by_cases hc : O.cycle=true
  · obtain ⟨j,k,hj,hk,hne⟩:=StrongRuns.cycle_two_neighbors O hc i
    exact domain_of_two_carry_supports hj hk (fun h => hne (vertex_injective c O h)) (x i)
      (fun hh => hsupport _ _ hh _ _ (he i j hj)) (fun hh => hsupport _ _ hh _ _ (he i k hk))
  · have hc' : O.cycle=false := Bool.eq_false_iff.mpr hc
    by_cases hi0 : i=0
    · subst i; exact (hb hc').1
    by_cases hin : i=Fin.last (O.edges)
    · subst i; exact (hb hc').2
    have hi:=i.isLt
    have h0 : 0 < i.val := by
      by_contra h
      apply hi0
      apply Fin.ext
      simp only [Fin.val_zero]
      omega
    have hn : i.val<O.edges := by
      by_contra h
      apply hin
      apply Fin.ext
      simp only [Fin.val_last]
      omega
    let j : Fin (O.edges+1):=⟨i.val-1,by omega⟩
    let k : Fin (O.edges+1):=⟨i.val+1,by omega⟩
    have hj : (rawGraph m r p).Adj (vertex c O i) (vertex c O j) :=
      (O.adjacent_iff _ _).2 (Or.inr (Or.inl (by dsimp [j]; omega)))
    have hk : (rawGraph m r p).Adj (vertex c O i) (vertex c O k) :=
      (O.adjacent_iff _ _).2 (Or.inl rfl)
    have hne : vertex c O j≠vertex c O k := by
      intro h
      have hh:=congrArg Fin.val (vertex_injective c O h)
      dsimp [j,k] at hh
      omega
    exact domain_of_two_carry_supports hj hk hne (x i)
      (fun hh => hsupport _ _ hh _ _ (he i j hj)) (fun hh => hsupport _ _ hh _ _ (he i k hk))

/-- Pointwise exact mask elimination. The kernel product may have either sign. -/
theorem signed_unary_masks (x : Fin (O.edges+1)→State) :
    (if ∀ i,Domain r p 4 (vertex c O i) ((x i).val+1) then (1:ℝ) else 0)*kernelProduct c O K x=
      (if BoundaryAllowed c O x then 1 else 0)*kernelProduct c O K x := by
  by_cases hz : kernelProduct c O K x=0
  · simp only [hz,mul_zero]
  · have he : (∀ i,Domain r p 4 (vertex c O i) ((x i).val+1)) ↔ BoundaryAllowed c O x :=
      ⟨fun h _ => ⟨h 0,h (Fin.last _)⟩,fun h => boundary_implies_domains c O K hsym hsupport x h hz⟩
    simp only [he]

/-- Arbitrary signed physical weights can be included without moving absolute
values through this complete assignment sum. -/
theorem signed_unary_masks_sum (weight : (Fin (O.edges+1)→State)→ℝ) :
    (∑ x,weight x*((if ∀ i,Domain r p 4 (vertex c O i) ((x i).val+1) then (1:ℝ) else 0)*kernelProduct c O K x))=
      ∑ x,weight x*((if BoundaryAllowed c O x then 1 else 0)*kernelProduct c O K x) := by
  apply Finset.sum_congr rfl
  intro x _
  rw [signed_unary_masks c O K hsym hsupport]


end Kernel
end SubmittedGenus.CapFourMass.ExecutableModes.OrderedSource
