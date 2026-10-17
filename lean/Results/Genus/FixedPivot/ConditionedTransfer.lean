import Results.Genus.FixedPivot.ConditionedBoundary

/-! Exact identification of every original conditioned tail with the carry matrix kernel. -/
namespace SubmittedGenus.FixedPivot
open RawGraph RawGraph.SourceModel RawGraph.Conditioning
open scoped BigOperators
noncomputable section
section Source
variable {m r p : ℕ} (hp : Parameters m r p 4) (hm : 2*p<m)

def sourceStartAllowed (x : Fin p→Fin 5) (c : TailRepresentative hp) (v : Fin 3) : Prop :=
  sourcePortAllowed hp x c.val (v.val+1)

def sourceFinishAllowed (x : Fin p→Fin 5) (c : TailRepresentative hp) (v : Fin 3) : Prop :=
  if c.val=portPartner (m-r) (p-r) (parameter_gap_lt hp) c.val then 2≤v.val+1
  else sourcePortAllowed hp x (portPartner (m-r) (p-r) (parameter_gap_lt hp) c.val) (v.val+1)

instance (x : Fin p→Fin 5) (c : TailRepresentative hp) : DecidablePred (sourceStartAllowed hp x c) := by
  intro v
  unfold sourceStartAllowed
  infer_instance
instance (x : Fin p→Fin 5) (c : TailRepresentative hp) : DecidablePred (sourceFinishAllowed hp x c) := by
  intro v
  unfold sourceFinishAllowed
  infer_instance

lemma conditioned_tail_unary_iff (x : Fin p→Fin 5) (c : TailRepresentative hp)
    (j : Fin (conditionedTailEdges hp c+1)) (v : Fin 3) :
    TailUnary (conditioningLayout hp hm) r p 4 x c j (ColorRestriction.positiveColor v) ↔
      ((c.val=portPartner (m-r) (p-r) (parameter_gap_lt hp) c.val ∧
        j.val=conditionedTailEdges hp c) → 2≤v.val+1) ∧
      (j.val=0 → sourceStartAllowed hp x c v) ∧
      ((c.val≠portPartner (m-r) (p-r) (parameter_gap_lt hp) c.val ∧
        j.val=conditionedTailEdges hp c) →
        sourcePortAllowed hp x (portPartner (m-r) (p-r) (parameter_gap_lt hp) c.val) (v.val+1)) := by
  rw [TailUnary,conditioned_tail_domain_iff,conditioned_core_tail_iff]
  have hv:=v.isLt
  simp only [ColorRestriction.positiveColor_val,sourceStartAllowed]
  constructor
  · rintro ⟨⟨_,_,hl⟩,hs,hf⟩
    exact ⟨hl,hs,hf⟩
  · rintro ⟨hl,hs,hf⟩
    exact ⟨⟨by omega,by omega,hl⟩,hs,hf⟩

/-- The full admissibility predicate is precisely endpoint restrictions and the
original sum-at-least-three tests along consecutive tail coordinates. -/
theorem conditionedTailAllowed_iff_kernel (x : Fin p→Fin 5) (c : TailRepresentative hp)
    (y : Fin (conditionedTailEdges hp c+1)→Fin 3) :
    TailAllowed (conditioningLayout hp hm) r p 4 x c (fun j => ColorRestriction.positiveColor (y j)) ↔
      CarryKernelAllowed (conditionedTailEdges hp c) (sourceStartAllowed hp x c)
        (sourceFinishAllowed hp x c) y := by
  unfold TailAllowed CarryKernelAllowed
  simp only [conditioned_tail_unary_iff,ColorRestriction.positiveColor_val,
    show (conditioningLayout hp hm).cycle c=false from rfl,Bool.false_eq_true,false_implies,and_true]
  constructor
  · rintro ⟨hu,he⟩
    refine ⟨(hu 0).2.1 rfl,?_,?_⟩
    swap
    · intro j
      have h:=he j
      exact (conditioned_tail_edge hp hm c j).symm.le.trans h
    by_cases hf : c.val=portPartner (m-r) (p-r) (parameter_gap_lt hp) c.val
    · rw [sourceFinishAllowed,if_pos hf]
      exact (hu (Fin.last _)).1 ⟨hf,rfl⟩
    · rw [sourceFinishAllowed,if_neg hf]
      exact (hu (Fin.last _)).2.2 ⟨hf,rfl⟩
  · rintro ⟨hs,hf,he⟩
    refine ⟨?_,?_⟩
    swap
    · intro j
      exact (conditioned_tail_edge hp hm c j).le.trans (he j)
    intro j
    have hzero : j.val=0 → j=0 := fun h => Fin.ext h
    have hlast : j.val=conditionedTailEdges hp c → j=Fin.last _ := fun h => Fin.ext h
    refine ⟨?_,?_,?_⟩
    · rintro ⟨hc,hj⟩
      rw [hlast hj]
      change 2≤(y (Fin.last (conditionedTailEdges hp c))).val+1
      exact (by simpa only [sourceFinishAllowed,if_pos hc] using hf)
    · intro hj
      rw [hzero hj]
      exact hs
    · rintro ⟨hc,hj⟩
      rw [hlast hj]
      change sourcePortAllowed hp x (portPartner (m-r) (p-r) (parameter_gap_lt hp) c.val)
        ((y (Fin.last (conditionedTailEdges hp c))).val+1)
      exact (by simpa only [sourceFinishAllowed,if_neg hc] using hf)

/-- This is the actual raw-source-to-M bridge: all finite words, alphabets,
loops, endpoints and coordinate weights have been discharged. -/
theorem conditioned_component_eq_kernel {R : Type*} [CommRing R] (z : R)
    (x : Fin p→Fin 5) (c : TailRepresentative hp) :
    Polynomial.eval₂ (Nat.castRingHom R) z (componentRun (conditioningLayout hp hm) r p 4 x c)=
      weightedCarryKernel z (conditionedTailEdges hp c)
        (fun v => if sourceStartAllowed hp x c v then 1 else 0)
        (fun v => if sourceFinishAllowed hp x c v then 1 else 0) := by
  rw [conditioned_component_three_colors hp hm,weightedCarryKernel_gated_source]
  change (Polynomial.eval₂RingHom (Nat.castRingHom R) z)
    (∑ y : Fin (conditionedTailEdges hp c+1)→Fin 3,
      tailTerm (conditioningLayout hp hm) r p 4 x c (fun j => ColorRestriction.positiveColor (y j)))=_
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro y _
  unfold tailTerm
  simp only [conditionedTailAllowed_iff_kernel hp hm]
  split_ifs <;> simp [Polynomial.coe_eval₂RingHom,ColorRestriction.positiveColor_val]
  rfl

/-- Source-exact finite core contraction in the rational carry convention. -/
theorem rawPolynomial_eval_eq_core_kernels {R : Type*} [CommRing R] (z : R) :
    Polynomial.eval₂ (Nat.castRingHom R) z (rawPolynomial m r p 4)=
      ∑ x : Fin p→Fin 5,
        Polynomial.eval₂ (Nat.castRingHom R) z (coreTerm (conditioningLayout hp hm) r p 4 x)*
        ∏ c : TailRepresentative hp,
          weightedCarryKernel z (conditionedTailEdges hp c)
            (fun v => if sourceStartAllowed hp x c v then 1 else 0)
            (fun v => if sourceFinishAllowed hp x c v then 1 else 0) := by
  rw [rawPolynomial_eq_core_carry_transfers hp hm]
  change (Polynomial.eval₂RingHom (Nat.castRingHom R) z) _=_
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [map_mul,map_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro c _
  exact conditioned_component_eq_kernel hp hm z x c

end Source
end
end SubmittedGenus.FixedPivot
