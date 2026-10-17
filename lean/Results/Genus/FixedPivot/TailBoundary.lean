import Results.Genus.FixedPivot.TailLayout

/-! Exact boundary locations of source core-to-tail edges and carry loops. -/
namespace SubmittedGenus.FixedPivot
section TailBoundary
variable (N d : ℕ) (hd : 0<d) (hN : d<N)

lemma carryComponentLabel_first (a : CarryRepresentative N d hN) :
    carryComponentLabel N d hN a 0=a.val.val+1 := by
  unfold carryComponentLabel
  by_cases hf : a.val=portPartner N d hN a.val
  · rw [if_pos hf,ResiduePair.fixed_port,componentPair_a]
  · rw [if_neg hf]
    simp only [Nat.zero_mod,ite_true,Nat.zero_div,ResiduePair.left,Nat.zero_mul,Nat.add_zero]
    exact componentPair_a N d hN a

lemma carryComponentLabel_last_paired (a : CarryRepresentative N d hN)
    (hf : a.val≠portPartner N d hN a.val) :
    carryComponentLabel N d hN a (carryComponentSize N d hN a-1)=
      (portPartner N d hN a.val).val+1 := by
  let L:=componentPair N d hN a
  have hn:=L.n_pos
  simp only [carryComponentLabel,carryComponentSize,if_neg hf]
  change (if (2*L.n-1)%2=0 then L.left ((2*L.n-1)/2)
    else L.right (L.n-1-(2*L.n-1)/2))=_
  rw [if_neg (by omega),show L.n-1-(2*L.n-1)/2=0 by omega]
  simpa only [ResiduePair.right,Nat.zero_mul,Nat.add_zero] using componentPair_b N d hN a

lemma carryTail_loop_iff (a : CarryRepresentative N d hN) {t : ℕ}
    (ht : t<carryTailSize N d hN a) :
    (2*carryTailLabel N d hN a t=N ∨ 2*carryTailLabel N d hN a t=N+d) ↔
      a.val=portPartner N d hN a.val ∧ t=carryTailSize N d hN a-1 := by
  have hh:=carryTail_incidence_iff N d hN a ht ht
  unfold CarryIncidence at hh
  constructor
  · intro h
    have h':=hh.1 (by omega)
    omega
  · intro h
    have h':=hh.2 (Or.inr (Or.inr ⟨h.1,h.2,h.2⟩))
    omega

include hd in
/-- Every source edge from a carry port to a retained tail is at the initial
endpoint, or the final endpoint of a paired class, with the correct port label. -/
theorem carryTail_port_incidence_iff (a : CarryRepresentative N d hN) {t x : ℕ}
    (ht : t<carryTailSize N d hN a) (hx : 0<x ∧ x≤d) :
    CarryIncidence N d (carryTailLabel N d hN a t) x ↔
      (x=a.val.val+1 ∧ t=0) ∨
      (a.val≠portPartner N d hN a.val ∧ x=(portPartner N d hN a.val).val+1 ∧
        t=carryTailSize N d hN a-1) := by
  have hfull:=carryTail_position N d hN a ht
  have hsize:=carryComponentSize_positive N d hN a
  constructor
  · intro hinc
    obtain ⟨b,s,hs⟩:=carryComponentLabel_surjective N d hd hN
      (show CarryVertex N x by unfold CarryVertex; omega)
    have hab : a=b := carry_incidence_same_component N d hd hN a b
      ⟨t+1,hfull⟩ s (by simpa only [carryTailLabel,hs] using hinc)
    subst b
    have hp:=(carryComponentLabel_port_iff N d hN a s.isLt).1 (by rw [hs]; exact hx.2)
    have he:=(carry_component_incidence_iff N d hN a hfull s.isLt).1
      (by simpa only [carryTailLabel,hs] using hinc)
    rcases hp with hz | ⟨hf,hl⟩
    · left
      have hlabel : x=a.val.val+1 := by rw [← hs,hz,carryComponentLabel_first]
      refine ⟨hlabel,?_⟩
      unfold carryTailSize carryPortArity at ht
      split_ifs at ht <;> omega
    · right
      have hlabel : x=(portPartner N d hN a.val).val+1 := by
        rw [← hs,hl,carryComponentLabel_last_paired N d hN a hf]
      refine ⟨hf,hlabel,?_⟩
      unfold carryTailSize carryPortArity at ht ⊢
      rw [if_neg hf] at ht ⊢
      omega
  · rintro (⟨rfl,rfl⟩ | ⟨hf,rfl,htlast⟩)
    · rw [← carryComponentLabel_first N d hN a]
      exact (carry_component_incidence_iff N d hN a hfull hsize).2 (Or.inr (Or.inl rfl))
    · rw [← carryComponentLabel_last_paired N d hN a hf]
      apply (carry_component_incidence_iff N d hN a hfull (by omega)).2
      left
      unfold carryTailSize carryPortArity at htlast ht
      rw [if_neg hf] at htlast ht
      omega

end TailBoundary
end SubmittedGenus.FixedPivot
