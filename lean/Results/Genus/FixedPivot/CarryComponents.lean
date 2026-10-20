import Results.Genus.FixedPivot.PortInvolution

/-! A canonical, disjoint, exhaustive carry-component layout before pivot deletion. -/
namespace SubmittedGenus.FixedPivot

section Ports
variable (N d : ℕ) (hd : 0<d) (hN : d<N)

/-- Select the larger port in each involution orbit; thus the pivot port d
is always the initial port of its own component. -/
abbrev CarryRepresentative := {a : Fin d // portPartner N d hN a≤a}

def carryRepresentative (a : Fin d) : CarryRepresentative N d hN :=
  ⟨max a (portPartner N d hN a), by
    by_cases ha : a≤portPartner N d hN a
    · rw [max_eq_right ha,portPartner_involutive]
      exact ha
    · rw [max_eq_left (le_of_not_ge ha)]
      exact le_of_not_ge ha⟩

lemma carryRepresentative_of_rep (a : CarryRepresentative N d hN) :
    carryRepresentative N d hN a.val=a := by
  apply Subtype.ext
  exact max_eq_left a.property

lemma carryRepresentative_partner (a : Fin d) :
    carryRepresentative N d hN (portPartner N d hN a)=carryRepresentative N d hN a := by
  apply Subtype.ext
  change max (portPartner N d hN a) (portPartner N d hN (portPartner N d hN a))=
    max a (portPartner N d hN a)
  rw [portPartner_involutive,max_comm]

lemma residuePort_of_list {a k : ℕ} (ha : 0<a) (had : a≤d) :
    residuePort d (a+k*d)=a := by
  have hb:=residuePort_bounds (x := a+k*d) (show 0<d by omega)
  have he:=residue_decomposition (d := d) (x := a+k*d) (by omega)
  exact (residue_list_unique (by omega) hb.2 ha had he.symm).1

def carryVertexPort (hd : 0<d) (x : ℕ) : Fin d :=
  ⟨(x-1)%d,Nat.mod_lt _ hd⟩

lemma carryVertexPort_list (a : Fin d) (k : ℕ) :
    carryVertexPort (d := d) (hd := hd) (a.val+1+k*d)=a := by
  apply Fin.ext
  unfold carryVertexPort
  dsimp only
  have he:=residuePort_of_list d (a := a.val+1) (k := k) (by omega) (by have:=a.isLt; omega)
  unfold residuePort at he
  omega

def componentPair (a : CarryRepresentative N d hN) : ResiduePair N d := pairForPort N d hN a.val

def carryComponentSize (a : CarryRepresentative N d hN) : ℕ :=
  if a.val=portPartner N d hN a.val then (componentPair N d hN a).n
  else 2*(componentPair N d hN a).n

def carryComponentLabel (a : CarryRepresentative N d hN) (t : ℕ) : ℕ :=
  if a.val=portPartner N d hN a.val then (componentPair N d hN a).fixedVertex t
  else if t%2=0 then (componentPair N d hN a).left (t/2)
  else (componentPair N d hN a).right ((componentPair N d hN a).n-1-t/2)

lemma componentPair_a (a : CarryRepresentative N d hN) :
    (componentPair N d hN a).a=a.val.val+1 := rfl

lemma componentPair_b (a : CarryRepresentative N d hN) :
    (componentPair N d hN a).b=(portPartner N d hN a.val).val+1 :=
  (portPartner_val N d hN a.val).symm

lemma componentPair_fixed (a : CarryRepresentative N d hN) :
    (componentPair N d hN a).a=(componentPair N d hN a).b ↔
      a.val=portPartner N d hN a.val := by
  rw [componentPair_a,componentPair_b]
  constructor
  · intro he
    apply Fin.ext
    omega
  · intro he
    exact congrArg (fun i : Fin d => i.val+1) he

lemma carryComponentSize_positive (a : CarryRepresentative N d hN) :
    0<carryComponentSize N d hN a := by
  have hn:=(componentPair N d hN a).n_pos
  unfold carryComponentSize
  split_ifs <;> omega

lemma carryComponentLabel_vertex (a : CarryRepresentative N d hN) {t : ℕ}
    (ht : t<carryComponentSize N d hN a) :
    CarryVertex N (carryComponentLabel N d hN a t) := by
  unfold carryComponentLabel carryComponentSize at *
  split_ifs at * with hf he
  · exact (componentPair N d hN a).fixed_vertex ht
  · exact (componentPair N d hN a).left_vertex (by omega)
  · exact (componentPair N d hN a).right_vertex (by
      have hn:=(componentPair N d hN a).n_pos
      omega)

lemma carryComponentLabel_port (a : CarryRepresentative N d hN) (t : ℕ) :
    carryVertexPort (d := d) (hd := hd) (carryComponentLabel N d hN a t)=a.val ∨
      carryVertexPort (d := d) (hd := hd) (carryComponentLabel N d hN a t)=portPartner N d hN a.val := by
  unfold carryComponentLabel
  split_ifs with hf he
  · left
    unfold ResiduePair.fixedVertex ResiduePair.left
    rw [componentPair_a]
    exact carryVertexPort_list (d := d) (hd := hd) a.val _
  · left
    unfold ResiduePair.left
    rw [componentPair_a]
    exact carryVertexPort_list (d := d) (hd := hd) a.val _
  · right
    unfold ResiduePair.right
    rw [componentPair_b]
    exact carryVertexPort_list (d := d) (hd := hd) (portPartner N d hN a.val) _

lemma carryComponentLabel_representative (a : CarryRepresentative N d hN) (t : ℕ) :
    carryRepresentative N d hN (carryVertexPort (d := d) (hd := hd) (carryComponentLabel N d hN a t))=a := by
  rcases carryComponentLabel_port N d hd hN a t with h | h
  · rw [h,carryRepresentative_of_rep]
  · rw [h,carryRepresentative_partner,carryRepresentative_of_rep]

include hd in
/-- Distinct component representatives label disjoint actual carry vertices. -/
lemma carryComponentLabel_disjoint (a b : CarryRepresentative N d hN) (t s : ℕ)
    (he : carryComponentLabel N d hN a t=carryComponentLabel N d hN b s) : a=b := by
  have ha:=carryComponentLabel_representative N d hd hN a t
  have hb:=carryComponentLabel_representative N d hd hN b s
  rw [he,hb] at ha
  exact ha.symm

lemma carryComponentLabel_injective (a : CarryRepresentative N d hN) :
    Function.Injective (fun t : Fin (carryComponentSize N d hN a) =>
      carryComponentLabel N d hN a t.val) := by
  intro t s he
  have ht:=t.isLt
  have hs:=s.isLt
  by_cases hf : a.val=portPartner N d hN a.val
  · simp only [carryComponentSize,if_pos hf] at ht hs
    simp only [carryComponentLabel,if_pos hf,ResiduePair.fixedVertex] at he
    have hh:=(componentPair N d hN a).left_injective he
    have hinj:=zigzagIndex_injective (componentPair N d hN a).n
    have heFin : (⟨zigzagIndex (componentPair N d hN a).n t.val,zigzagIndex_lt ht⟩ :
        Fin (componentPair N d hN a).n)=
      ⟨zigzagIndex (componentPair N d hN a).n s.val,zigzagIndex_lt hs⟩ := Fin.ext hh
    have := congrArg Fin.val (hinj (a₁ := ⟨t.val,ht⟩) (a₂ := ⟨s.val,hs⟩) heFin)
    exact Fin.ext this
  · simp only [carryComponentSize,if_neg hf] at ht hs
    have hab : (componentPair N d hN a).a≠(componentPair N d hN a).b :=
      fun h => hf ((componentPair_fixed N d hN a).1 h)
    simp only [carryComponentLabel,if_neg hf] at he
    split_ifs at he with hte hse hse
    · have hh:=(componentPair N d hN a).left_injective he
      apply Fin.ext
      omega
    · exact False.elim ((componentPair N d hN a).lists_disjoint hab _ _ he)
    · exact False.elim ((componentPair N d hN a).lists_disjoint hab _ _ he.symm)
    · have hh:=(componentPair N d hN a).right_injective he
      apply Fin.ext
      omega

lemma carryComponent_covers_left (a : CarryRepresentative N d hN) {k : ℕ}
    (hk : k<(componentPair N d hN a).n) :
    ∃ t : Fin (carryComponentSize N d hN a),
      carryComponentLabel N d hN a t.val=(componentPair N d hN a).left k := by
  by_cases hf : a.val=portPartner N d hN a.val
  · let t:Fin (componentPair N d hN a).n :=
      (zigzagEquiv (componentPair N d hN a).n).symm ⟨k,hk⟩
    have ht : t.val<carryComponentSize N d hN a := by
      rw [carryComponentSize,if_pos hf]
      exact t.isLt
    refine ⟨⟨t.val,ht⟩, ?_⟩
    rw [carryComponentLabel,if_pos hf]
    unfold ResiduePair.fixedVertex
    congr 1
    have hh:=(zigzagEquiv (componentPair N d hN a).n).apply_symm_apply ⟨k,hk⟩
    exact congrArg Fin.val hh
  · refine ⟨⟨2*k,by rw [carryComponentSize,if_neg hf]; omega⟩,?_⟩
    change carryComponentLabel N d hN a (2*k)=_
    rw [carryComponentLabel,if_neg hf,if_pos (by omega)]
    congr 1
    omega

lemma carryComponent_covers_right (a : CarryRepresentative N d hN) {k : ℕ}
    (hk : k<(componentPair N d hN a).n) :
    ∃ t : Fin (carryComponentSize N d hN a),
      carryComponentLabel N d hN a t.val=(componentPair N d hN a).right k := by
  by_cases hf : a.val=portPartner N d hN a.val
  · have he : (componentPair N d hN a).right k=(componentPair N d hN a).left k := by
      unfold ResiduePair.right ResiduePair.left
      rw [← (componentPair_fixed N d hN a).2 hf]
    rw [he]
    exact carryComponent_covers_left N d hN a hk
  · refine ⟨⟨2*((componentPair N d hN a).n-1-k)+1,by
      rw [carryComponentSize,if_neg hf]
      omega⟩,?_⟩
    change carryComponentLabel N d hN a (2*((componentPair N d hN a).n-1-k)+1)=_
    rw [carryComponentLabel,if_neg hf,if_neg (by omega)]
    congr 1
    omega

include hd in
/-- Every actual shifted carry vertex occurs in one of the canonical paths. -/
theorem carryComponentLabel_surjective {x : ℕ} (hx : CarryVertex N x) :
    ∃ (a : CarryRepresentative N d hN) (t : Fin (carryComponentSize N d hN a)),
      carryComponentLabel N d hN a t.val=x := by
  let v:=carryVertexPort (d := d) (hd := hd) x
  let a:=carryRepresentative N d hN v
  let k:=residueIndex d x
  have hp : v.val+1=residuePort d x := by
    have hh:=residuePort_bounds (x := x) hd
    dsimp [v,carryVertexPort,residuePort]
  have he : x=v.val+1+k*d := by rw [hp]; exact residue_decomposition hx.1
  have hk : k<(pairForPort N d hN v).n := by
    apply (ResiduePair.left_vertex_iff _ _).1
    change CarryVertex N (v.val+1+k*d)
    rwa [← he]
  by_cases ho : portPartner N d hN v≤v
  · have hav : a.val=v := max_eq_left ho
    have hn : (componentPair N d hN a).n=(pairForPort N d hN v).n := by
      unfold componentPair
      rw [hav]
    obtain ⟨t,ht⟩:=carryComponent_covers_left N d hN a (by rw [hn]; exact hk)
    refine ⟨a,t,?_⟩
    rw [ht]
    change (componentPair N d hN a).a+k*d=x
    rw [componentPair_a,hav]
    exact he.symm
  · have hav : a.val=portPartner N d hN v := max_eq_right (le_of_not_ge ho)
    have hn : (componentPair N d hN a).n=(pairForPort N d hN v).n := by
      unfold componentPair
      rw [hav]
      exact (pairForPort_partner N d hN v).2
    have hb : (componentPair N d hN a).b=v.val+1 := by
      unfold componentPair
      rw [hav]
      exact (pairForPort_partner N d hN v).1
    obtain ⟨t,ht⟩:=carryComponent_covers_right N d hN a (by rw [hn]; exact hk)
    refine ⟨a,t,?_⟩
    rw [ht]
    change (componentPair N d hN a).b+k*d=x
    rw [hb]
    exact he.symm

/-- A single global map from disjoint component positions to actual carry vertices. -/
def carryLayoutMap (v : Σ a : CarryRepresentative N d hN, Fin (carryComponentSize N d hN a)) :
    {x : ℕ // CarryVertex N x} :=
  ⟨carryComponentLabel N d hN v.1 v.2.val,carryComponentLabel_vertex N d hN v.1 v.2.isLt⟩

include hd in
theorem carryLayoutMap_injective : Function.Injective (carryLayoutMap N d hN) := by
  rintro ⟨a,t⟩ ⟨b,s⟩ he
  have hv:=congrArg Subtype.val he
  change carryComponentLabel N d hN a t.val=carryComponentLabel N d hN b s.val at hv
  have hab:=carryComponentLabel_disjoint N d hd hN a b t.val s.val hv
  subst b
  have hts:=carryComponentLabel_injective N d hN a hv
  subst s
  rfl

include hd in
theorem carryLayoutMap_surjective : Function.Surjective (carryLayoutMap N d hN) := by
  rintro ⟨x,hx⟩
  obtain ⟨a,t,ht⟩:=carryComponentLabel_surjective N d hd hN hx
  refine ⟨⟨a,t⟩,?_⟩
  apply Subtype.ext
  exact ht

/-- Complete source coverage and no duplicate physical vertices are proved, not asserted. -/
noncomputable def carryLayoutEquiv :
    (Σ a : CarryRepresentative N d hN, Fin (carryComponentSize N d hN a)) ≃
      {x : ℕ // CarryVertex N x} :=
  Equiv.ofBijective (carryLayoutMap N d hN)
    ⟨carryLayoutMap_injective N d hd hN,carryLayoutMap_surjective N d hd hN⟩

end Ports
end SubmittedGenus.FixedPivot
