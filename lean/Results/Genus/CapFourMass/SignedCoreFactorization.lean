import Results.Genus.CapFourMass.PhysicalSourceFactorization
import Results.Genus.CapFourMass.SignedKernelValues

/-! The actual signed physical core factor is the original stable core term. -/
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators
namespace SubmittedGenus.CapFourMass.CarryLocalization
open RawGraph RawGraph.SourceModel RawGraph.Topology FixedPivot SourceCoreFactorization ActualComponent
attribute [local instance] Classical.propDecidable Classical.decEq

lemma coreStrongBound_eq_four_of_pos {r p : ℕ} (k l : Fin p)
    (h : 0<coreStrongBound r p k l) : coreStrongBound r p k l=4 := by
  unfold coreStrongBound at h ⊢
  split_ifs at h ⊢ <;> omega

section Core
variable {r N d : ℕ} (hd : 0<d) (hN : d<N) (hfar : r+2*d<N)
variable (choice : Option (CarryRepresentative N d hN)→Mode) (c : SourceComponent r N d)

include hfar in
/-- Ordinary physical constraints and all core vertex weights recover the
original full core term, independently of the chosen carry signs. -/
theorem signed_core_product (x : c→State) :
    coreUnaryProduct hN c x*coreEdgeProduct hN c (sourceSignedKernel hd hN choice) x=
      componentCoreTerm hN radius c (fun k => x (ownedCoreVertex hN c k)) := by
  by_cases hu : ∀k : CoreAt hN c,CoreDomain r (r+d) k.val.val ((x (ownedCoreVertex hN c k)).val+1)
  · rw [componentCoreTerm_eq_vertex_edge_product]
    unfold coreUnaryProduct coreEdgeProduct
    simp_rw [physical_core_domain hN hfar]
    apply congrArg₂ (·*·)
    · congr 1
      ext k
      simp only [Finset.mem_univ]
    · let gate : CoreAt hN c×CoreAt hN c→ℝ := fun ij =>
        if coreStrongBound r (r+d) ij.1.val.val ij.2.val.val ≤
          ((x (ownedCoreVertex hN c ij.1)).val+1)+((x (ownedCoreVertex hN c ij.2)).val+1) then 1 else 0
      change _=∏ij ∈ coreEdgeSet hN c,gate ij
      calc
        _=∏ij : {ij // ij∈coreEdgeSet hN c},gate ij.val := by
          apply Finset.prod_congr rfl
          rintro ⟨ij,hij⟩ _
          dsimp only [gate]

          have hs:=core_positive_strong hN c ij.1 ij.2 ((mem_coreEdgeSet hN c ij).mp hij).2
          have hv : Domain r (r+d) 4 (coreVertex hN ij.1.val).val ((x (ownedCoreVertex hN c ij.1)).val+1):=
            (physical_core_domain hN hfar ij.1.val _).mpr (hu ij.1)
          have hw : Domain r (r+d) 4 (coreVertex hN ij.2.val).val ((x (ownedCoreVertex hN c ij.2)).val+1):=
            (physical_core_domain hN hfar ij.2.val _).mpr (hu ij.2)
          change StrongRuns.StrongStep r (r+d) (coreVertex hN ij.1.val).val (coreVertex hN ij.2.val).val at hs
          rw [sourceSignedKernel_strong_domains hd hN choice hs _ _ hv hw]
          have hb := coreStrongBound_eq_four_of_pos (r:=r) (p:=r+d)
            ij.1.val.val ij.2.val.val ((mem_coreEdgeSet hN c ij).mp hij).2
          rw [hb]
        _=_ := Finset.prod_coe_sort (coreEdgeSet hN c) gate
  · have hz : coreUnaryProduct hN c x=0 := by
      unfold coreUnaryProduct
      simp_rw [physical_core_domain hN hfar]
      rw [Factorization.prod_gate,if_neg hu]
    have hx : ¬componentCoreAllowed hN c (fun k => x (ownedCoreVertex hN c k)):=fun h => hu h.1
    rw [hz,zero_mul,componentCoreTerm,if_neg hx]

end Core
end SubmittedGenus.CapFourMass.CarryLocalization
