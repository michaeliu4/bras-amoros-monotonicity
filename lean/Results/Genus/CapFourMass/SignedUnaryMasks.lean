import Results.Genus.CapFourMass.SourceMasks

/-! Exact unary-mask elimination for arbitrary signed carry-mode kernels.
Only the carry alphabet support is used; signed carry projector entries are
not incorrectly assumed to retain the original threshold-three gate. -/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFourMass.ActualComponent
open RawGraph RawGraph.SourceModel RawGraph.Topology
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Internal domains follow from two distinct incidences whenever the occupied
carry entries are supported on the physical alphabet 1..3. -/
lemma domain_of_two_carry_supports {m r p : ℕ}
    {i j k : Fin (m-1)} (hj : (rawGraph m r p).Adj i j) (hk : (rawGraph m r p).Adj i k)
    (hne : j≠k) (v : State)
    (h1 : StrongRuns.CarryStep r p i j → v.val+1 ≤ 3)
    (h2 : StrongRuns.CarryStep r p i k → v.val+1 ≤ 3) : Domain r p 4 i (v.val+1) := by
  have hloop : ¬(StrongLoop r p i ∨ CarryLoop r p i) :=
    fun h => hne (StrongRuns.loop_excludes_two_neighbors h hj hk)
  have hv:=v.isLt
  have hupper : v.val+1 ≤ upper r 4 i := by
    by_cases hi : physical i<r
    · simp only [upper,if_pos hi]; omega
    · have hc : StrongRuns.CarryStep r p i j ∨ StrongRuns.CarryStep r p i k := by
        rcases StrongRuns.edge_strong_or_carry hj with hs | hc
        · rcases StrongRuns.edge_strong_or_carry hk with hs' | hc'
          · exact (hi (StrongRuns.internal_strong_lt_r hs hs' hne)).elim
          · exact Or.inr hc'
        · exact Or.inl hc
      have hv3 : v.val+1 ≤ 3 := hc.elim h1 h2
      simpa only [upper,if_neg hi] using hv3
  rw [domain_iff_unary]
  refine ⟨fun h => (hj.2.1 h).elim,fun _ => ⟨by omega,hupper,?_,?_⟩⟩
  · exact fun h => (hloop (Or.inl h)).elim
  · exact fun h => (hloop (Or.inr h)).elim

section Kernel
variable {m r p : ℕ}
variable (K : Fin (m-1)→Fin (m-1)→State→State→ℝ)
variable (hsym : ∀ i j v w,K i j v w=K j i w v)
variable (hsupport : ∀ i j,StrongRuns.CarryStep r p i j → ∀ v w,K i j v w≠0 → v.val+1 ≤ 3)

/-- Every ordinary edge occurs exactly once, including the true closing edge. -/
def signedKernelProduct (c : Component m r p) (x : Fin (edgeCount c+1)→State) : ℝ :=
  (∏ j : Fin (edgeCount c),K (vertex c j.castSucc) (vertex c j.succ) (x j.castSucc) (x j.succ))*
    (if (freeComponentOrder m r p c).cycle=true then
      K (vertex c (Fin.last _)) (vertex c 0) (x (Fin.last _)) (x 0) else 1)

include hsym
lemma signedKernelProduct_nonzero_all (c : Component m r p) (x : Fin (edgeCount c+1)→State)
    (hprod : signedKernelProduct K c x≠0) :
    ∀ i j,(rawGraph m r p).Adj (vertex c i) (vertex c j) →
      K (vertex c i) (vertex c j) (x i) (x j)≠0 := by
  have hpath : ∀ j : Fin (edgeCount c),K (vertex c j.castSucc) (vertex c j.succ) (x j.castSucc) (x j.succ)≠0 :=
    fun j => (Finset.prod_ne_zero_iff.mp (mul_ne_zero_iff.mp hprod).1) j (Finset.mem_univ j)
  have hclose : (freeComponentOrder m r p c).cycle=true →
      K (vertex c (Fin.last _)) (vertex c 0) (x (Fin.last _)) (x 0)≠0 := by
    intro hc
    simpa only [signedKernelProduct,if_pos hc] using (mul_ne_zero_iff.mp hprod).2
  intro i j he
  have hh:=((freeComponentOrder m r p c).adjacent_iff i j).mp he
  rcases hh with hij | hji | ⟨hc,hh⟩
  · have hi : i.val<edgeCount c := by have := j.isLt; omega
    have hi' : i=Fin.castSucc (⟨i.val,hi⟩ : Fin (edgeCount c)) := Fin.ext rfl
    have hj' : j=Fin.succ (⟨i.val,hi⟩ : Fin (edgeCount c)) := Fin.ext hij.symm
    simpa only [←hi',←hj'] using hpath ⟨i.val,hi⟩
  · have hj : j.val<edgeCount c := by have := i.isLt; omega
    have hj' : j=Fin.castSucc (⟨j.val,hj⟩ : Fin (edgeCount c)) := Fin.ext rfl
    have hi' : i=Fin.succ (⟨j.val,hj⟩ : Fin (edgeCount c)) := Fin.ext hji.symm
    rw [hsym]
    simpa only [←hi',←hj'] using hpath ⟨j.val,hj⟩
  · rcases hh with ⟨hi,hj⟩ | ⟨hj,hi⟩
    · have hi' : i=0 := Fin.ext hi
      have hj' : j=Fin.last (edgeCount c) := Fin.ext hj
      rw [hi',hj',hsym]
      exact hclose hc
    · have hi' : i=Fin.last (edgeCount c) := Fin.ext hi
      have hj' : j=0 := Fin.ext hj
      rw [hi',hj']
      exact hclose hc

include hsupport
lemma signed_boundary_implies_domains (c : Component m r p) (x : Fin (edgeCount c+1)→State)
    (hb : BoundaryAllowed c x) (hprod : signedKernelProduct K c x≠0) :
    ∀ i,Domain r p 4 (vertex c i) ((x i).val+1) := by
  have he:=signedKernelProduct_nonzero_all K hsym c x hprod
  intro i
  by_cases hc : (freeComponentOrder m r p c).cycle=true
  · obtain ⟨j,k,hj,hk,hne⟩:=StrongRuns.cycle_two_neighbors (freeComponentOrder m r p c) hc i
    exact domain_of_two_carry_supports hj hk (fun h => hne (vertex_injective c h)) (x i)
      (fun hh => hsupport _ _ hh _ _ (he i j hj)) (fun hh => hsupport _ _ hh _ _ (he i k hk))
  · have hc' : (freeComponentOrder m r p c).cycle=false := Bool.eq_false_iff.mpr hc
    by_cases hi0 : i=0
    · subst i; exact (hb hc').1
    by_cases hin : i=Fin.last (edgeCount c)
    · subst i; exact (hb hc').2
    have hi:=i.isLt
    have h0 : 0 < i.val := by
      by_contra h
      apply hi0
      apply Fin.ext
      simp only [Fin.val_zero]
      omega
    have hn : i.val<edgeCount c := by
      by_contra h
      apply hin
      apply Fin.ext
      simp only [Fin.val_last]
      omega
    let j : Fin (edgeCount c+1):=⟨i.val-1,by omega⟩
    let k : Fin (edgeCount c+1):=⟨i.val+1,by omega⟩
    have hj : (rawGraph m r p).Adj (vertex c i) (vertex c j) :=
      ((freeComponentOrder m r p c).adjacent_iff _ _).2 (Or.inr (Or.inl (by dsimp [j]; omega)))
    have hk : (rawGraph m r p).Adj (vertex c i) (vertex c k) :=
      ((freeComponentOrder m r p c).adjacent_iff _ _).2 (Or.inl rfl)
    have hne : vertex c j≠vertex c k := by
      intro h
      have hh:=congrArg Fin.val (vertex_injective c h)
      dsimp [j,k] at hh
      omega
    exact domain_of_two_carry_supports hj hk hne (x i)
      (fun hh => hsupport _ _ hh _ _ (he i j hj)) (fun hh => hsupport _ _ hh _ _ (he i k hk))

/-- Pointwise exact mask elimination. The kernel product may have either sign. -/
theorem signed_unary_masks (c : Component m r p) (x : Fin (edgeCount c+1)→State) :
    (if ∀ i,Domain r p 4 (vertex c i) ((x i).val+1) then (1:ℝ) else 0)*signedKernelProduct K c x=
      (if BoundaryAllowed c x then 1 else 0)*signedKernelProduct K c x := by
  by_cases hz : signedKernelProduct K c x=0
  · simp only [hz,mul_zero]
  · have he : (∀ i,Domain r p 4 (vertex c i) ((x i).val+1)) ↔ BoundaryAllowed c x :=
      ⟨fun h _ => ⟨h 0,h (Fin.last _)⟩,fun h => signed_boundary_implies_domains K hsym hsupport c x h hz⟩
    simp only [he]

/-- Arbitrary signed physical weights can be included without moving absolute
values through this complete assignment sum. -/
theorem signed_unary_masks_sum (c : Component m r p) (weight : (Fin (edgeCount c+1)→State)→ℝ) :
    (∑ x,weight x*((if ∀ i,Domain r p 4 (vertex c i) ((x i).val+1) then (1:ℝ) else 0)*signedKernelProduct K c x))=
      ∑ x,weight x*((if BoundaryAllowed c x then 1 else 0)*signedKernelProduct K c x) := by
  apply Finset.sum_congr rfl
  intro x _
  rw [signed_unary_masks K hsym hsupport]

end Kernel

/-- Normalization removes exactly the two incidence half-weights. -/
def normalizedSignedKernel {m : ℕ} (A : Fin (m-1)→Fin (m-1)→State→State→ℝ)
    (i j : Fin (m-1)) (v w : State) : ℝ := A i j v w/(halfWeight v*halfWeight w)
lemma normalizedSignedKernel_symmetric {m : ℕ}
    (A : Fin (m-1)→Fin (m-1)→State→State→ℝ)
    (hsym : ∀ i j v w,A i j v w=A j i w v) (i j : Fin (m-1)) (v w : State) :
    normalizedSignedKernel A i j v w=normalizedSignedKernel A j i w v := by
  unfold normalizedSignedKernel
  rw [hsym,mul_comm]
lemma normalizedSignedKernel_support {m r p : ℕ}
    (A : Fin (m-1)→Fin (m-1)→State→State→ℝ)
    (hsupport : ∀ i j,StrongRuns.CarryStep r p i j → ∀ v w,A i j v w≠0 → v.val+1 ≤ 3)
    (i j : Fin (m-1)) (hc : StrongRuns.CarryStep r p i j) (v w : State)
    (hne : normalizedSignedKernel A i j v w≠0) : v.val+1 ≤ 3 := by
  apply hsupport i j hc v w
  intro hz
  apply hne
  simp only [normalizedSignedKernel,hz,zero_div]

end SubmittedGenus.CapFourMass.ActualComponent
