import Results.Genus.FixedPivot.PhaseCounts

/-! Pairing-independent endpoint products from the actual source port bijection. -/
namespace SubmittedGenus.FixedPivot
open scoped BigOperators
section Product
variable {R : Type*} [CommMonoid R]
variable (N d : ℕ) (hN : d<N)

lemma carryPort_component_product (g : Fin d→R) (a : CarryRepresentative N d hN) :
    (∏ j : Fin (carryPortArity N d hN a),g (carryPortLabel N d hN ⟨a,j⟩))=
      g a.val*(if a.val=portPartner N d hN a.val then 1 else g (portPartner N d hN a.val)) := by
  unfold carryPortLabel
  by_cases hf : a.val=portPartner N d hN a.val
  · have ha : carryPortArity N d hN a=1 := by rw [carryPortArity,if_pos hf]
    rw [if_pos hf,mul_one]
    calc
      _ = ∏ j : Fin 1,g (if j.val=0 then a.val else portPartner N d hN a.val) :=
        Fintype.prod_equiv (finCongr ha) _ _ (fun _ => rfl)
      _ = _ := by simp [Fin.prod_univ_succ]
  · have ha : carryPortArity N d hN a=2 := by rw [carryPortArity,if_neg hf]
    rw [if_neg hf]
    calc
      _ = ∏ j : Fin 2,g (if j.val=0 then a.val else portPartner N d hN a.val) :=
        Fintype.prod_equiv (finCongr ha) _ _ (fun _ => rfl)
      _ = _ := by simp [Fin.prod_univ_succ]

/-- Every port endpoint is counted once, irrespective of the residue pairing. -/
theorem carry_endpoint_product (g : Fin d→R) (h : R) :
    (∏ a : CarryRepresentative N d hN,
      g a.val*(if a.val=portPartner N d hN a.val then h else g (portPartner N d hN a.val)))=
      (∏ a : Fin d,g a)*h^(carryFixedCount N d hN) := by
  classical
  have hp:=(carryPortEquiv N d hN).prod_comp g
  rw [Fintype.prod_sigma] at hp
  change (∏ a : CarryRepresentative N d hN,∏ j : Fin (carryPortArity N d hN a),
    g (carryPortLabel N d hN ⟨a,j⟩))=(∏ a : Fin d,g a) at hp
  simp_rw [carryPort_component_product N d hN] at hp
  have hloops : (∏ a : CarryRepresentative N d hN,
      if a.val=portPartner N d hN a.val then h else 1)=h^(carryFixedCount N d hN) := by
    rw [Finset.prod_ite,Finset.prod_const_one,mul_one,Finset.prod_const,carryFixedCount_eq_filter]
  rw [← hloops,← hp,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro a _
  split_ifs <;> simp

/-- One distinguished pivot becomes a free endpoint; each other physical port
contributes one theta and one core eigenvector entry. -/
theorem carry_port_product_pivot (pivot : Fin d) (theta beta : R) (v : Fin d→R) :
    (∏ a : Fin d,if a=pivot then beta else theta*v a)=
      theta^(d-1)*beta*(∏ a ∈ (Finset.univ.erase pivot),v a) := by
  classical
  rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ pivot)]
  simp only [ite_true]
  have hprod : (∏ a ∈ Finset.univ \ {pivot},if a=pivot then beta else theta*v a)=
      ∏ a ∈ Finset.univ.erase pivot,theta*v a := by
    rw [Finset.sdiff_singleton_eq_erase]
    apply Finset.prod_congr rfl
    intro a ha
    exact if_neg (Finset.ne_of_mem_erase ha)
  rw [hprod,Finset.prod_mul_distrib,Finset.prod_const]
  simp only [Finset.card_erase_of_mem (Finset.mem_univ pivot),Finset.card_univ,Fintype.card_fin]
  ac_rfl

end Product
end SubmittedGenus.FixedPivot
