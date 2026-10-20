import Results.Genus.FixedPivot.ConditionedKernels

/-! Source core-tail inequalities occur only at the two specified carry endpoints. -/
namespace SubmittedGenus.FixedPivot
open RawGraph RawGraph.SourceModel RawGraph.Conditioning
noncomputable section
section Source
variable {m r p : ℕ} (hp : Parameters m r p 4) (hm : 2*p<m)

def conditionedPortIndex (a : Fin (p-r)) : Fin p :=
  ⟨r+a.val,by have := a.isLt; have := hp.2.1; omega⟩

lemma conditionedPortIndex_val (a : Fin (p-r)) : (conditionedPortIndex hp a).val=r+a.val := rfl

lemma conditioned_core_tail_edge (c : TailRepresentative hp)
    (j : Fin (conditionedTailEdges hp c+1)) (k : Fin p) :
    edgeBound r p 4 (coreVertex (conditioningLayout hp hm) k)
      (tailVertex (conditioningLayout hp hm) c j)=
      if ((c.val.val+1≠p-r ∧ j.val=0 ∧ k=conditionedPortIndex hp c.val) ∨
        (c.val≠portPartner (m-r) (p-r) (parameter_gap_lt hp) c.val ∧
          (portPartner (m-r) (p-r) (parameter_gap_lt hp) c.val).val+1≠p-r ∧
          j.val=conditionedTailEdges hp c ∧
          k=conditionedPortIndex hp (portPartner (m-r) (p-r) (parameter_gap_lt hp) c.val)))
      then 3 else 0 := by
  have hkrange:=k.isLt
  have hleft:=c.val.isLt
  have hright:=(portPartner (m-r) (p-r) (parameter_gap_lt hp) c.val).isLt
  have hrp:=hp.2.1
  have hpm:=hp.2.2.1
  have ht:=conditioned_tail_gt hp hm c j
  have hk : physical (coreVertex (conditioningLayout hp hm) k)≤p := by
    rw [conditioning_core_physical]; omega
  rw [edgeBound_symm,tail_core_edgeBound hp.2.1 _ _ ht hk]
  simp only [IsPivot,conditioning_core_physical,conditioning_tail_physical]
  by_cases hkr : r<k.val+1
  · have hx : 0<k.val+1-r ∧ k.val+1-r≤p-r := by omega
    have hh:=carryTail_port_incidence_iff (m-r) (p-r) (parameter_gap_positive hp)
      (parameter_gap_lt hp) c (conditionedTailIndex_lt hp hm c j) hx
    have hphys :
        (r+carryTailLabel (m-r) (p-r) (parameter_gap_lt hp) c j.val+(k.val+1)=m+r ∨
          r+carryTailLabel (m-r) (p-r) (parameter_gap_lt hp) c j.val+(k.val+1)=m+p) ↔
        CarryIncidence (m-r) (p-r)
          (carryTailLabel (m-r) (p-r) (parameter_gap_lt hp) c j.val) (k.val+1-r) := by
      unfold CarryIncidence
      omega
    simp only [hphys,hh]
    simp only [Fin.ext_iff,conditionedPortIndex_val]
    unfold conditionedTailEdges
    split_ifs <;> omega
  · have htail:=carryTailLabel_vertex (m-r) (p-r) (parameter_gap_lt hp) c
      (conditionedTailIndex_lt hp hm c j)
    simp only [Fin.ext_iff,conditionedPortIndex_val]
    split_ifs <;> omega

def sourcePortAllowed (x : Fin p→Fin 5) (a : Fin (p-r)) (v : ℕ) : Prop :=
  a.val+1=p-r ∨ 3≤(x (conditionedPortIndex hp a)).val+v

instance (x : Fin p→Fin 5) (a : Fin (p-r)) (v : ℕ) :
    Decidable (sourcePortAllowed hp x a v) := by unfold sourcePortAllowed; infer_instance

/-- Condition on the original core once; only the actual port endpoint tests remain. -/
theorem conditioned_core_tail_iff (x : Fin p→Fin 5) (c : TailRepresentative hp)
    (j : Fin (conditionedTailEdges hp c+1)) (v : ℕ) :
    (∀ k : Fin p,edgeBound r p 4 (coreVertex (conditioningLayout hp hm) k)
      (tailVertex (conditioningLayout hp hm) c j)≤(x k).val+v) ↔
    (j.val=0 → sourcePortAllowed hp x c.val v) ∧
    ((c.val≠portPartner (m-r) (p-r) (parameter_gap_lt hp) c.val ∧
      j.val=conditionedTailEdges hp c) →
      sourcePortAllowed hp x (portPartner (m-r) (p-r) (parameter_gap_lt hp) c.val) v) := by
  simp_rw [conditioned_core_tail_edge hp hm]
  unfold sourcePortAllowed
  constructor
  · intro h
    constructor
    · intro hj
      by_cases ha : c.val.val+1=p-r
      · exact Or.inl ha
      · right
        have hh:=h (conditionedPortIndex hp c.val)
        rw [if_pos (Or.inl ⟨ha,hj,rfl⟩)] at hh
        exact hh
    · rintro ⟨hf,hj⟩
      by_cases ha : (portPartner (m-r) (p-r) (parameter_gap_lt hp) c.val).val+1=p-r
      · exact Or.inl ha
      · right
        have hh:=h (conditionedPortIndex hp (portPartner (m-r) (p-r) (parameter_gap_lt hp) c.val))
        rw [if_pos (Or.inr ⟨hf,ha,hj,rfl⟩)] at hh
        exact hh
  · rintro ⟨hl,hr⟩ k
    split_ifs with h
    · rcases h with ⟨ha,hj,rfl⟩ | ⟨hf,ha,hj,rfl⟩
      · exact (hl hj).resolve_left ha
      · exact (hr ⟨hf,hj⟩).resolve_left ha
    · omega

end Source
end
end SubmittedGenus.FixedPivot
