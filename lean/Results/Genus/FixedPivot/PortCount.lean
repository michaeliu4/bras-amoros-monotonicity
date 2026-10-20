import Results.Genus.FixedPivot.CarryComponents

/-! Exact port-orbit incidence count: each paired path costs2 and each fixed path1. -/
namespace SubmittedGenus.FixedPivot
open scoped BigOperators
section Ports
variable (N d : ℕ) (hN : d<N)

def carryPortArity (a : CarryRepresentative N d hN) : ℕ :=
  if a.val=portPartner N d hN a.val then 1 else 2

lemma carryPortArity_pos (a : CarryRepresentative N d hN) : 0<carryPortArity N d hN a := by
  unfold carryPortArity
  split_ifs <;> omega

def carryPortLabel (v : Σ a : CarryRepresentative N d hN, Fin (carryPortArity N d hN a)) : Fin d :=
  if v.2.val=0 then v.1.val else portPartner N d hN v.1.val

lemma carryPortLabel_representative
    (v : Σ a : CarryRepresentative N d hN, Fin (carryPortArity N d hN a)) :
    carryRepresentative N d hN (carryPortLabel N d hN v)=v.1 := by
  unfold carryPortLabel
  split_ifs
  · exact carryRepresentative_of_rep N d hN v.1
  · rw [carryRepresentative_partner,carryRepresentative_of_rep]

lemma carryPortLabel_injective : Function.Injective (carryPortLabel N d hN) := by
  rintro ⟨a,i⟩ ⟨b,j⟩ he
  have ha:=carryPortLabel_representative N d hN ⟨a,i⟩
  have hb:=carryPortLabel_representative N d hN ⟨b,j⟩
  rw [he,hb] at ha
  have hab : a=b := ha.symm
  subst b
  have hi:=i.isLt
  have hj:=j.isLt
  have hij : i=j := by
    apply Fin.ext
    unfold carryPortLabel at he
    dsimp only at he
    by_cases hiz : i.val=0
    · by_cases hjz : j.val=0
      · omega
      · rw [if_pos hiz,if_neg hjz] at he
        simp only [carryPortArity,if_pos he] at hj
        omega
    · by_cases hjz : j.val=0
      · rw [if_neg hiz,if_pos hjz] at he
        simp only [carryPortArity,if_pos he.symm] at hi
        omega
      · unfold carryPortArity at hi hj
        split_ifs at hi hj <;> omega
  subst j
  rfl

lemma carryPortLabel_surjective : Function.Surjective (carryPortLabel N d hN) := by
  intro v
  let a:=carryRepresentative N d hN v
  by_cases ho : portPartner N d hN v≤v
  · have hav : a.val=v := max_eq_left ho
    refine ⟨⟨a,⟨0,carryPortArity_pos N d hN a⟩⟩,?_⟩
    simp [carryPortLabel,hav]
  · have hav : a.val=portPartner N d hN v := max_eq_right (le_of_not_ge ho)
    have hback : portPartner N d hN a.val=v := by rw [hav,portPartner_involutive]
    have hne : a.val≠portPartner N d hN a.val := by
      rw [hav,portPartner_involutive]
      intro h
      exact ho (le_of_eq h)
    refine ⟨⟨a,⟨1,by rw [carryPortArity,if_neg hne]; omega⟩⟩,?_⟩
    simpa only [carryPortLabel,if_neg (show (1 : ℕ)≠0 by omega)] using hback

/-- Every original port belongs to exactly one component endpoint slot. -/
noncomputable def carryPortEquiv :
    (Σ a : CarryRepresentative N d hN, Fin (carryPortArity N d hN a)) ≃ Fin d :=
  Equiv.ofBijective (carryPortLabel N d hN)
    ⟨carryPortLabel_injective N d hN,carryPortLabel_surjective N d hN⟩

/-- Exactly d carry-edge increments occur on a multiplicity progression. -/
theorem carry_port_arity_sum :
    (∑ a : CarryRepresentative N d hN, carryPortArity N d hN a)=d := by
  have hh:=Fintype.card_congr (carryPortEquiv N d hN)
  simpa only [Fintype.card_sigma,Fintype.card_fin] using hh

end Ports
end SubmittedGenus.FixedPivot
