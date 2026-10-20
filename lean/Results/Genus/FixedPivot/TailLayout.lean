import Results.Genus.FixedPivot.CarryLayout
import Results.Genus.FixedPivot.PortCount

/-! Source carry components after their fixed-core port endpoints are removed. -/
namespace SubmittedGenus.FixedPivot
section Tail
variable (N d : ℕ) (hd : 0<d) (hN : d<N)

lemma componentPair_two (hbig : 2*d<N) (a : CarryRepresentative N d hN) :
    2≤(componentPair N d hN a).n := by
  let L:=componentPair N d hN a
  have hn:=L.n_pos
  have he:=L.endpoint
  have ha:=L.a_le
  have hb:=L.b_le
  by_contra h
  change ¬2≤L.n at h
  have hz : L.n-1=0 := by omega
  rw [hz,Nat.zero_mul,Nat.add_zero] at he
  omega

/-- In the exact full layout the only ports are the initial vertex and,
for a paired component, its final vertex. -/
lemma carryComponentLabel_port_iff (a : CarryRepresentative N d hN) {t : ℕ}
    (ht : t<carryComponentSize N d hN a) :
    carryComponentLabel N d hN a t≤d ↔
      t=0 ∨ (a.val≠portPartner N d hN a.val ∧ t=carryComponentSize N d hN a-1) := by
  let L:=componentPair N d hN a
  by_cases hf : a.val=portPartner N d hN a.val
  · simp only [carryComponentLabel,carryComponentSize,if_pos hf] at ht ⊢
    simp only [ne_eq,iff_true_intro hf,not_true_eq_false,false_and,or_false]
    change t<L.n at ht
    change L.left (zigzagIndex L.n t)≤d ↔ t=0
    rw [L.port_iff (zigzagIndex_lt ht)]
    unfold zigzagIndex
    split_ifs <;> omega
  · simp only [carryComponentLabel,carryComponentSize,if_neg hf] at ht ⊢
    simp only [iff_true_intro hf,true_and]
    change t<2*L.n at ht
    by_cases he : t%2=0
    · rw [if_pos he]
      change L.left (t/2)≤d ↔ t=0 ∨ t=2*L.n-1
      rw [L.port_iff (by omega)]
      omega
    · rw [if_neg he]
      change L.swap.left (L.n-1-t/2)≤d ↔ t=0 ∨ t=2*L.n-1
      rw [L.swap.port_iff (by change L.n-1-t/2<L.n; have hn:=L.n_pos; omega)]
      omega

def carryTailSize (a : CarryRepresentative N d hN) : ℕ :=
  carryComponentSize N d hN a-carryPortArity N d hN a

def carryTailLabel (a : CarryRepresentative N d hN) (t : ℕ) : ℕ :=
  carryComponentLabel N d hN a (t+1)

lemma carryTailSize_positive (hbig : 2*d<N) (a : CarryRepresentative N d hN) :
    0<carryTailSize N d hN a := by
  have hn:=componentPair_two N d hN hbig a
  unfold carryTailSize carryComponentSize carryPortArity
  split_ifs <;> omega

lemma carryTail_position (a : CarryRepresentative N d hN) {t : ℕ}
    (ht : t<carryTailSize N d hN a) : t+1<carryComponentSize N d hN a := by
  have ha:=carryPortArity_pos N d hN a
  unfold carryTailSize at ht
  omega

lemma carryTailLabel_vertex (a : CarryRepresentative N d hN) {t : ℕ}
    (ht : t<carryTailSize N d hN a) :
    d<carryTailLabel N d hN a t ∧ carryTailLabel N d hN a t<N := by
  have hb:=carryTail_position N d hN a ht
  have hv:=carryComponentLabel_vertex N d hN a hb
  refine ⟨?_,hv.2⟩
  have hp:=carryComponentLabel_port_iff N d hN a hb
  unfold carryTailLabel
  by_contra hh
  obtain h | ⟨hf,hl⟩:=hp.1 (by omega)
  · omega
  · unfold carryTailSize carryPortArity at ht
    rw [if_neg hf] at ht
    omega

include hd in
/-- Every tail coordinate is represented, with no new membership assumptions. -/
lemma carryTailLabel_surjective {x : ℕ} (hx : d<x ∧ x<N) :
    ∃ a : CarryRepresentative N d hN, ∃ t : Fin (carryTailSize N d hN a),
      carryTailLabel N d hN a t.val=x := by
  obtain ⟨a,s,hs⟩:=carryComponentLabel_surjective N d hd hN (show CarryVertex N x by
    unfold CarryVertex; omega)
  have hp:=carryComponentLabel_port_iff N d hN a s.isLt
  have hnp : ¬(s.val=0 ∨ (a.val≠portPartner N d hN a.val ∧
      s.val=carryComponentSize N d hN a-1)) := by
    intro h
    have hh:=hp.2 h
    rw [hs] at hh
    omega
  have hs0 : 0<s.val := by omega
  have ht : s.val-1<carryTailSize N d hN a := by
    have hh:=s.isLt
    unfold carryTailSize carryPortArity
    split_ifs with hf
    · omega
    · have hn : s.val≠carryComponentSize N d hN a-1 := by
        intro he
        exact hnp (Or.inr ⟨hf,he⟩)
      omega
  refine ⟨a,⟨s.val-1,ht⟩,?_⟩
  change carryComponentLabel N d hN a (s.val-1+1)=x
  rw [Nat.sub_add_cancel hs0]
  exact hs

def carryTailMap (v : Σ a : CarryRepresentative N d hN, Fin (carryTailSize N d hN a)) :
    {x : ℕ // d<x ∧ x<N} :=
  ⟨carryTailLabel N d hN v.1 v.2.val,carryTailLabel_vertex N d hN v.1 v.2.isLt⟩

include hd in
lemma carryTailMap_injective : Function.Injective (carryTailMap N d hN) := by
  rintro ⟨a,t⟩ ⟨b,s⟩ he
  have hv:=congrArg Subtype.val he
  change carryComponentLabel N d hN a (t.val+1)=carryComponentLabel N d hN b (s.val+1) at hv
  have hab:=carryComponentLabel_disjoint N d hd hN a b _ _ hv
  subst b
  have hh:=carryComponentLabel_injective N d hN a
    (a₁ := ⟨t.val+1,carryTail_position N d hN a t.isLt⟩)
    (a₂ := ⟨s.val+1,carryTail_position N d hN a s.isLt⟩) hv
  have hval:=congrArg Fin.val hh
  have hts : t=s := Fin.ext (by dsimp only at hval; omega)
  subst s
  rfl

include hd in
lemma carryTailMap_surjective : Function.Surjective (carryTailMap N d hN) := by
  rintro ⟨x,hx⟩
  obtain ⟨a,t,ht⟩:=carryTailLabel_surjective N d hd hN hx
  exact ⟨⟨a,t⟩,Subtype.ext ht⟩

/-- An explicit source bijection of all tail coordinates with their path positions. -/
noncomputable def carryTailEquiv :
    (Σ a : CarryRepresentative N d hN, Fin (carryTailSize N d hN a)) ≃
      {x : ℕ // d<x ∧ x<N} :=
  Equiv.ofBijective (carryTailMap N d hN)
    ⟨carryTailMap_injective N d hd hN,carryTailMap_surjective N d hd hN⟩

/-- The retained source incidences are the consecutive tail edges and the
unchanged terminal loop of each fixed residue class. -/
theorem carryTail_incidence_iff (a : CarryRepresentative N d hN) {t s : ℕ}
    (ht : t<carryTailSize N d hN a) (hs : s<carryTailSize N d hN a) :
    CarryIncidence N d (carryTailLabel N d hN a t) (carryTailLabel N d hN a s) ↔
      t+1=s ∨ s+1=t ∨ (a.val=portPartner N d hN a.val ∧
        t=carryTailSize N d hN a-1 ∧ s=carryTailSize N d hN a-1) := by
  unfold carryTailLabel
  rw [carry_component_incidence_iff N d hN a (carryTail_position N d hN a ht)
    (carryTail_position N d hN a hs)]
  unfold carryTailSize carryPortArity at *
  split_ifs at * with hf <;> omega

end Tail
end SubmittedGenus.FixedPivot
