import Results.Genus.FixedPivot.GeometricRationality

namespace SubmittedGenus.FixedPivot
open scoped BigOperators
noncomputable section
variable {R I : Type*} [CommRing R] [Fintype I]

private lemma erase_two_factor {J : Type*} [Fintype J] [DecidableEq J]
    (f : J→R) (a b k : J) (hab : a≠b) (hka : k≠a) (hkb : k≠b) :
    (∏j∈Finset.univ.erase k,f j)=
      f a*f b*(∏j∈((Finset.univ.erase k).erase a).erase b,f j) := by
  rw [←Finset.mul_prod_erase (Finset.univ.erase k) f (a:=a) (by simp [Ne.symm hka])]
  rw [←Finset.mul_prod_erase ((Finset.univ.erase k).erase a) f (a:=b)
    (by simp [Ne.symm hkb,Ne.symm hab])]
  ring

/-- Separate the two pure mode endpoints from all mixed modes over an
arbitrary commutative ring. No rate distinctness or denominator inversion. -/
theorem modeNumerator_eval_one_split {d : ℕ} (hd : 0<d)
    (rates : Fin (d+1)→R) (A : I→R) (index : I→Fin (d+1)) :
    ∃ M : R,
      Polynomial.eval 1 (modeNumerator rates A index)=
        (∏j∈(Finset.univ.erase (0 : Fin (d+1))).erase (Fin.last d),(1-rates j))*
          ((1-rates (Fin.last d))*(∑i∈Finset.univ.filter (fun i => index i=0),A i)+
           (1-rates 0)*(∑i∈Finset.univ.filter (fun i => index i=Fin.last d),A i))+
        (1-rates 0)*(1-rates (Fin.last d))*M := by
  classical
  let f := fun j => 1-rates j
  let mid := ∏j∈(Finset.univ.erase (0 : Fin (d+1))).erase (Fin.last d),f j
  let rem := fun k => ∏j∈((Finset.univ.erase k).erase (0 : Fin (d+1))).erase (Fin.last d),f j
  let M := ∑i,if index i≠0 ∧ index i≠Fin.last d then A i*rem (index i) else 0
  have hends : (0 : Fin (d+1))≠Fin.last d := by
    intro h
    have := congrArg Fin.val h
    simpa using (ne_of_gt hd).symm this
  have hzero : (∏j∈Finset.univ.erase (0 : Fin (d+1)),f j)=f (Fin.last d)*mid := by
    exact (Finset.mul_prod_erase _ f (by simp [Ne.symm hends])).symm
  have hlast : (∏j∈Finset.univ.erase (Fin.last d),f j)=f 0*mid := by
    have hh := (Finset.mul_prod_erase (Finset.univ.erase (Fin.last d)) f
      (show (0 : Fin (d+1))∈Finset.univ.erase (Fin.last d) by simp [hends])).symm
    have hs : (Finset.univ.erase (Fin.last d)).erase (0 : Fin (d+1)) =
        (Finset.univ.erase (0 : Fin (d+1))).erase (Fin.last d) := by
      ext j
      simp only [Finset.mem_erase]
      tauto
    simpa only [hs] using hh
  have hterm (i : I) : A i*(∏j∈Finset.univ.erase (index i),f j)=
      mid*(f (Fin.last d)*(if index i=0 then A i else 0)+
        f 0*(if index i=Fin.last d then A i else 0))+
      f 0*f (Fin.last d)*(if index i≠0 ∧ index i≠Fin.last d then A i*rem (index i) else 0) := by
    by_cases h0 : index i=0
    · rw [h0,hzero]
      simp [hends]
      ring
    by_cases hl : index i=Fin.last d
    · rw [hl,hlast]
      simp [Ne.symm hends]
      ring
    · rw [erase_two_factor f 0 (Fin.last d) (index i) hends h0 hl]
      simp only [h0,hl,if_false,ne_eq,not_false_eq_true,and_self,if_true,mul_zero,
        add_zero,zero_add]
      dsimp [rem]
      ring
  refine ⟨M,?_⟩
  unfold modeNumerator
  simp only [Polynomial.eval_finsetSum,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_prod,linearModeDenominator,Polynomial.eval_sub,Polynomial.eval_one,
    Polynomial.eval_X,mul_one]
  change (∑i,A i*(∏j∈Finset.univ.erase (index i),f j))= _
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  simp_rw [←Finset.mul_sum]
  simp only [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.sum_filter]
  simp only [M,Finset.sum_filter,f,mid]

#print axioms modeNumerator_eval_one_split
end
end SubmittedGenus.FixedPivot
