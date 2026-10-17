import Results.Genus.FixedPivot.CarryComponents

/-! Complete source edge coverage for the canonical residue-component layout. -/
namespace SubmittedGenus.FixedPivot
section Layout
variable (N d : ℕ) (hd : 0<d) (hN : d<N)

lemma canonical_right_port (a : Fin d) (k : ℕ) :
    carryVertexPort d hd ((pairForPort N d hN a).right k)=portPartner N d hN a := by
  unfold ResiduePair.right
  rw [← portPartner_val N d hN a]
  exact carryVertexPort_list d hd _ _

/-- Each actual carry incidence exchanges the paired residue classes. -/
theorem carry_incidence_port {x y : ℕ} (hx : CarryVertex N x) (hy : CarryVertex N y)
    (hxy : CarryIncidence N d x y) :
    carryVertexPort d hd y=portPartner N d hN (carryVertexPort d hd x) := by
  let a:=carryVertexPort d hd x
  let L:=pairForPort N d hN a
  let k:=residueIndex d x
  have hp : a.val+1=residuePort d x := by
    dsimp [a,carryVertexPort,residuePort]
  have he : x=L.left k := by
    change x=a.val+1+k*d
    rw [hp]
    exact residue_decomposition hx.1
  have hk : k<L.n := (L.left_vertex_iff k).1 (he ▸ hx)
  have hpa : carryVertexPort d hd (L.left k)=a := by
    exact carryVertexPort_list d hd a k
  rw [incidence_iff_reflections hx hy] at hxy
  rcases hxy with h | h
  · rw [h,he,L.reflectF_left hk,hpa]
    exact canonical_right_port N d hd hN a _
  · have hg : d<x := (reflectG_vertex_iff hx).1 (h ▸ hy)
    have hk0 : 0<k := by
      by_contra hh
      have hkz : k=0 := by omega
      have ha:=L.a_le
      rw [he,hkz] at hg
      simp only [ResiduePair.left,Nat.zero_mul,Nat.add_zero] at hg
      omega
    rw [h,he,L.reflectG_left hk0 hk,hpa]
    exact canonical_right_port N d hd hN a _

include hd in
/-- Every original carry edge is internal to precisely one canonical component. -/
theorem carry_incidence_same_component
    (a b : CarryRepresentative N d hN)
    (t : Fin (carryComponentSize N d hN a))
    (s : Fin (carryComponentSize N d hN b))
    (hxy : CarryIncidence N d (carryComponentLabel N d hN a t.val)
      (carryComponentLabel N d hN b s.val)) : a=b := by
  have hports:=carry_incidence_port N d hd hN
    (carryComponentLabel_vertex N d hN a t.isLt)
    (carryComponentLabel_vertex N d hN b s.isLt) hxy
  have hr:=congrArg (carryRepresentative N d hN) hports
  rw [carryRepresentative_partner,carryComponentLabel_representative,
    carryComponentLabel_representative] at hr
  exact hr.symm

/-- All and only consecutive path positions are ordinary incidences; a fixed
class has its one loop at the final position. -/
theorem carry_component_incidence_iff (a : CarryRepresentative N d hN) {t s : ℕ}
    (ht : t<carryComponentSize N d hN a) (hs : s<carryComponentSize N d hN a) :
    CarryIncidence N d (carryComponentLabel N d hN a t) (carryComponentLabel N d hN a s) ↔
      t+1=s ∨ s+1=t ∨
        (a.val=portPartner N d hN a.val ∧ t=carryComponentSize N d hN a-1 ∧
          s=carryComponentSize N d hN a-1) := by
  let L:=componentPair N d hN a
  by_cases hf : a.val=portPartner N d hN a.val
  · have hab : L.a=L.b := (componentPair_fixed N d hN a).2 hf
    simp only [carryComponentLabel,carryComponentSize,if_pos hf] at ht hs ⊢
    simpa only [iff_true_intro hf,true_and] using L.fixed_incidence_iff hab ht hs
  · have hab : L.a≠L.b := fun h => hf ((componentPair_fixed N d hN a).1 h)
    simp only [carryComponentLabel,carryComponentSize,if_neg hf] at ht hs ⊢
    simp only [iff_false_intro hf,false_and,or_false]
    change t<2*L.n at ht
    change s<2*L.n at hs
    by_cases hte : t%2=0
    · by_cases hse : s%2=0
      · rw [if_pos hte,if_pos hse]
        have hn:=L.paired_no_same_list_incidence hab (k := t/2) (l := s/2)
          (by omega) (by omega)
        exact iff_of_false hn (by omega)
      · rw [if_pos hte,if_neg hse]
        change CarryIncidence N d (L.pairedEven (t/2)) (L.pairedOdd (s/2)) ↔ _
        rw [L.paired_cross_incidence_iff hab (by omega) (by omega)]
        omega
    · by_cases hse : s%2=0
      · rw [if_neg hte,if_pos hse]
        have hsymm : CarryIncidence N d (L.pairedOdd (t/2)) (L.pairedEven (s/2)) ↔
            CarryIncidence N d (L.pairedEven (s/2)) (L.pairedOdd (t/2)) := by
          unfold CarryIncidence
          omega
        change CarryIncidence N d (L.pairedOdd (t/2)) (L.pairedEven (s/2)) ↔ _
        rw [hsymm,L.paired_cross_incidence_iff hab (by omega) (by omega)]
        omega
      · rw [if_neg hte,if_neg hse]
        have hn:=L.swap.paired_no_same_list_incidence (Ne.symm hab)
          (k := L.n-1-t/2) (l := L.n-1-s/2)
          (by change L.n-1-t/2<L.n; have hn:=L.n_pos; omega)
          (by change L.n-1-s/2<L.n; have hn:=L.n_pos; omega)
        exact iff_of_false hn (by omega)

end Layout
end SubmittedGenus.FixedPivot
