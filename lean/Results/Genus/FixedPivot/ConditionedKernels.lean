import Results.Genus.FixedPivot.ConditionedSource
import Results.Genus.FixedPivot.SourceConstraints
import Results.Genus.FixedPivot.TailBoundary
import Results.Genus.FixedPivot.KernelSource
import Results.Genus.RawGraph.ColorRestriction

/-! Source-specific reduction of the conditioned tails to the exact three-state carry model. -/
namespace SubmittedGenus.FixedPivot
open RawGraph RawGraph.SourceModel RawGraph.Conditioning
open scoped BigOperators
noncomputable section

section Source
variable {m r p : ℕ} (hp : Parameters m r p 4) (hm : 2*p<m)

lemma conditioned_tail_gt (c : TailRepresentative hp) (j : Fin (conditionedTailEdges hp c+1)) :
    p<physical (tailVertex (conditioningLayout hp hm) c j) := by
  rw [conditioning_tail_physical]
  have hh:=carryTailLabel_vertex (m-r) (p-r) (parameter_gap_lt hp) c
    (conditionedTailIndex_lt hp hm c j)
  have hrp:=hp.2.1
  omega

lemma conditioned_tail_loop_iff (c : TailRepresentative hp) (j : Fin (conditionedTailEdges hp c+1)) :
    CarryLoop r p (tailVertex (conditioningLayout hp hm) c j) ↔
      c.val=portPartner (m-r) (p-r) (parameter_gap_lt hp) c.val ∧ j.val=conditionedTailEdges hp c := by
  unfold CarryLoop
  rw [conditioning_tail_physical]
  have hh:=carryTail_loop_iff (m-r) (p-r) (parameter_gap_lt hp) c
    (conditionedTailIndex_lt hp hm c j)
  have hrp:=hp.2.1
  have hpm:=hp.2.2.1
  unfold conditionedTailEdges
  constructor
  · intro h
    apply hh.1
    omega
  · intro h
    have hx:=hh.2 h
    omega

lemma conditioned_tail_domain_iff (c : TailRepresentative hp)
    (j : Fin (conditionedTailEdges hp c+1)) (v : ℕ) :
    Domain r p 4 (tailVertex (conditioningLayout hp hm) c j) v ↔
      1≤v ∧ v≤3 ∧
      ((c.val=portPartner (m-r) (p-r) (parameter_gap_lt hp) c.val ∧
        j.val=conditionedTailEdges hp c) → 2≤v) := by
  rw [tail_domain_iff hp.2.1 _ (conditioned_tail_gt hp hm c j),conditioned_tail_loop_iff]

lemma conditioned_tail_distinct (c : TailRepresentative hp) (j : Fin (conditionedTailEdges hp c)) :
    tailVertex (conditioningLayout hp hm) c j.castSucc≠
      tailVertex (conditioningLayout hp hm) c j.succ := by
  intro he
  have hh:=(conditioningLayout hp hm).label.injective he
  have hs:=Sum.inr.inj hh
  have hv:=congrArg (fun w : Σ c : TailRepresentative hp, Fin (conditionedTailEdges hp c+1) => w.2.val) hs
  change j.val=j.val+1 at hv
  omega

/-- Every transfer edge has exactly the original threshold3, with no weaker surrogate. -/
lemma conditioned_tail_edge (c : TailRepresentative hp) (j : Fin (conditionedTailEdges hp c)) :
    edgeBound r p 4 (tailVertex (conditioningLayout hp hm) c j.castSucc)
      (tailVertex (conditioningLayout hp hm) c j.succ)=3 := by
  rw [tail_edgeBound hp.2.1 _ _ (conditioned_tail_gt hp hm c j.castSucc)
    (conditioned_tail_gt hp hm c j.succ),if_neg (conditioned_tail_distinct hp hm c j)]
  apply if_pos
  rw [conditioning_tail_physical,conditioning_tail_physical]
  have hh:=(carryTail_incidence_iff (m-r) (p-r) (parameter_gap_lt hp) c
    (conditionedTailIndex_lt hp hm c j.castSucc) (conditionedTailIndex_lt hp hm c j.succ)).2
    (Or.inl (by rfl))
  apply (physical_carry_iff hp.2.1.le (by have:=hp.2.2.1; have:=hp.2.1; omega)).2
  exact hh

lemma conditioned_tail_color (x : Fin p→Fin 5) (c : TailRepresentative hp)
    (j : Fin (conditionedTailEdges hp c+1)) (v : Fin 5)
    (hv : TailUnary (conditioningLayout hp hm) r p 4 x c j v) :
    ColorRestriction.PositiveColor v := by
  have hh:=(conditioned_tail_domain_iff hp hm c j v.val).1 hv.1
  exact ⟨hh.1,hh.2.1⟩

/-- The actual source-conditioned transfer uses precisely physical colors1,2,3. -/
theorem conditioned_component_three_colors (x : Fin p→Fin 5) (c : TailRepresentative hp) :
    componentRun (conditioningLayout hp hm) r p 4 x c=
      ∑ y : Fin (conditionedTailEdges hp c+1)→Fin 3,
        tailTerm (conditioningLayout hp hm) r p 4 x c (fun j => ColorRestriction.positiveColor (y j)) := by
  exact ColorRestriction.componentRun_restrict (conditioningLayout hp hm) x c
    (conditioned_tail_color hp hm x c)

end Source
end
end SubmittedGenus.FixedPivot
