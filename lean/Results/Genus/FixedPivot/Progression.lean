import Results.Genus.FixedPivot.PortCount
import Results.Genus.FixedPivot.CarryLayout

/-! Exact source carry topology under the original multiplicity step m↦m+d. -/
namespace SubmittedGenus.FixedPivot
open scoped BigOperators
section Progression
variable (N d : ℕ) (hN : d<N)

/-- The canonical port orbits agree in the next phase of the progression. -/
def carryRepresentativeProgression :
    CarryRepresentative N d hN ≃ CarryRepresentative (N+d) d (by omega) where
  toFun a:=⟨a.val,by rw [portPartner_progression]; exact a.property⟩
  invFun a:=⟨a.val,by rw [← portPartner_progression N d hN]; exact a.property⟩
  left_inv a:=rfl
  right_inv a:=rfl

lemma carryRepresentativeProgression_val (a : CarryRepresentative N d hN) :
    (carryRepresentativeProgression N d hN a).val=a.val := rfl

lemma componentPair_progression (a : CarryRepresentative N d hN) :
    (componentPair (N+d) d (by omega) (carryRepresentativeProgression N d hN a)).n=
      (componentPair N d hN a).n+1 :=
  (pairForPort_progression N d hN a.val).2

/-- Paired components gain two vertices and fixed components gain one vertex. -/
theorem carryComponentSize_progression (a : CarryRepresentative N d hN) :
    carryComponentSize (N+d) d (by omega) (carryRepresentativeProgression N d hN a)=
      carryComponentSize N d hN a+carryPortArity N d hN a := by
  unfold carryComponentSize carryPortArity
  rw [carryRepresentativeProgression_val,portPartner_progression N d hN,componentPair_progression N d hN]
  split_ifs <;> omega

/-- Path-edge lengths have the same exact increment, including the initial phase. -/
theorem carryComponentEdges_progression (a : CarryRepresentative N d hN) :
    carryComponentSize (N+d) d (by omega) (carryRepresentativeProgression N d hN a)-1=
      (carryComponentSize N d hN a-1)+carryPortArity N d hN a := by
  rw [carryComponentSize_progression]
  have hp:=carryComponentSize_positive N d hN a
  omega

/-- The sum of the actual component length increments is precisely d. -/
theorem carryComponent_total_increment :
    (∑ a : CarryRepresentative N d hN,
      carryComponentSize (N+d) d (by omega) (carryRepresentativeProgression N d hN a))=
      (∑ a : CarryRepresentative N d hN,carryComponentSize N d hN a)+d := by
  simp_rw [carryComponentSize_progression]
  rw [Finset.sum_add_distrib,carry_port_arity_sum]

/-- The total path-edge length increments, with the same port phases, sum to d. -/
theorem carryComponent_total_edge_increment :
    (∑ a : CarryRepresentative N d hN,
      (carryComponentSize (N+d) d (by omega) (carryRepresentativeProgression N d hN a)-1))=
      (∑ a : CarryRepresentative N d hN,(carryComponentSize N d hN a-1))+d := by
  simp_rw [carryComponentEdges_progression]
  rw [Finset.sum_add_distrib,carry_port_arity_sum]

end Progression
end SubmittedGenus.FixedPivot
