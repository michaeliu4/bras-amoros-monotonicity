import Results.Genus.FixedPivot.EndpointProduct
import Results.Genus.FixedPivot.KernelModes

/-! Exact pure-mode product over the actual source carry components. -/
namespace SubmittedGenus.FixedPivot
open scoped BigOperators
section Ring
variable {R : Type*} [CommRing R]
variable (N d : ℕ) (hd : 0<d) (hN : d<N) (hbig : 2*d<N)

/-- Rank-one endpoint factors eliminate the port pairing; only the actual
edge count, loop count and one surviving-port product remain. -/
theorem pure_component_product (z theta other bi ti di : R)
    (hb : theta+other=carryB z) (hc : theta*other=carryC z) (hbi : carryB z*bi=1)
    (start finish : CarryRepresentative N d hN→Fin 3→R)
    (g : Fin d→R) (loop : R)
    (hstart : ∀ a,carryWeightedDot z theta (start a)=g a.val)
    (hfinish : ∀ a,carryWeightedDot z theta (finish a)=
      if a.val=portPartner N d hN a.val then loop else g (portPartner N d hN a.val)) :
    (∏ a : CarryRepresentative N d hN,
      weightedModeAmplitude z theta other ti di (carryTailSize N d hN a-1) (start a) (finish a))=
      theta^(carryTailPathEdgeCount N d hN)*(bi*ti*di)^(Fintype.card (CarryRepresentative N d hN))*
      (∏ a : Fin d,g a)*loop^(carryFixedCount N d hN) := by
  classical
  simp_rw [weightedModeAmplitude_rank_one z theta other bi ti di hb hc hbi,hstart,hfinish]
  have he : (∏ a : CarryRepresentative N d hN,
      theta^(carryTailSize N d hN a-1)*(bi*ti*di)*g a.val*
        (if a.val=portPartner N d hN a.val then loop else g (portPartner N d hN a.val)))=
      (∏ a : CarryRepresentative N d hN,theta^(carryTailSize N d hN a-1)*(bi*ti*di))*
      (∏ a : CarryRepresentative N d hN,g a.val*
        (if a.val=portPartner N d hN a.val then loop else g (portPartner N d hN a.val))) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro a _
    ring
  rw [he,Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,Finset.prod_const,carry_endpoint_product]
  unfold carryTailPathEdgeCount
  simp only [Finset.card_univ]
  ring

include hd hbig in
/-- Removing the pivot port accounts for the exact original carry-edge exponent. -/
theorem pure_component_product_with_pivot (z theta other bi ti di : R)
    (hb : theta+other=carryB z) (hc : theta*other=carryC z) (hbi : carryB z*bi=1)
    (start finish : CarryRepresentative N d hN→Fin 3→R)
    (pivot : Fin d) (v : Fin d→R) (free loop : R)
    (hstart : ∀ a,carryWeightedDot z theta (start a)=
      if a.val=pivot then free else theta*v a.val)
    (hfinish : ∀ a,carryWeightedDot z theta (finish a)=
      if a.val=portPartner N d hN a.val then loop else
        if portPartner N d hN a.val=pivot then free else theta*v (portPartner N d hN a.val)) :
    (∏ a : CarryRepresentative N d hN,
      weightedModeAmplitude z theta other ti di (carryTailSize N d hN a-1) (start a) (finish a))=
      theta^(carrySourceEdgeCount N d)*(bi*ti*di)^(Fintype.card (CarryRepresentative N d hN))*
      free*loop^(carryFixedCount N d hN)*(∏ a ∈ Finset.univ.erase pivot,v a) := by
  rw [pure_component_product N d hN z theta other bi ti di hb hc hbi start finish
    (fun a => if a=pivot then free else theta*v a) loop hstart hfinish,
    carry_port_product_pivot]
  have he:=carryTailPathEdgeCount_add_ports N d hd hN hbig
  rw [← he,pow_add]
  ring

end Ring
end SubmittedGenus.FixedPivot
