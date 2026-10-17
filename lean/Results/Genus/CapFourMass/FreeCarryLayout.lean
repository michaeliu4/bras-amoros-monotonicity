import Results.Genus.CapFourMass.CarryLocalization

/-! Exact carry-run layout after deletion of the maximum-four pivot.  Unlike
the conditioned tail, this layout retains every surviving core port. -/
noncomputable section
namespace SubmittedGenus.CapFourMass.CarryLocalization
open FixedPivot

section Layout
variable (N d : ℕ) (hd : 0<d) (hN : d<N)

/-- Since each representative is the larger port, the deleted pivot can only
be the initial position of its canonical carry path. -/
lemma fullLabel_eq_pivot_iff (a : CarryRepresentative N d hN) {t : ℕ}
    (ht : t<carryComponentSize N d hN a) :
    carryComponentLabel N d hN a t=d ↔ a.val.val+1=d ∧ t=0 := by
  constructor
  · intro he
    rcases (carryComponentLabel_port_iff N d hN a ht).mp he.le with hz | ⟨hf,hl⟩
    · subst t
      exact ⟨(carryComponentLabel_first N d hN a).symm.trans he,rfl⟩
    · rw [hl,carryComponentLabel_last_paired N d hN a hf] at he
      have hle : (portPartner N d hN a.val).val≤a.val.val := a.property
      have ha:=a.val.isLt
      exact False.elim (hf (Fin.ext (by omega)))
  · rintro ⟨ha,rfl⟩
    exact (carryComponentLabel_first N d hN a).trans ha

/-- Exactly the pivot endpoint is removed; other core ports remain. -/
def deletedPrefix (a : CarryRepresentative N d hN) : ℕ :=
  if a.val.val+1=d then 1 else 0

def freeCarrySize (a : CarryRepresentative N d hN) : ℕ :=
  carryComponentSize N d hN a-deletedPrefix N d hN a

def freeCarryLabel (a : CarryRepresentative N d hN) (t : ℕ) : ℕ :=
  carryComponentLabel N d hN a (t+deletedPrefix N d hN a)

lemma deletedPrefix_le_one (a : CarryRepresentative N d hN) : deletedPrefix N d hN a≤1 := by
  unfold deletedPrefix
  split_ifs <;> omega

lemma componentSize_two (hbig : 2*d<N) (a : CarryRepresentative N d hN) :
    2≤carryComponentSize N d hN a := by
  have hh:=componentPair_two N d hN hbig a
  unfold carryComponentSize
  split_ifs <;> omega

lemma freeCarrySize_positive (hbig : 2*d<N) (a : CarryRepresentative N d hN) :
    0<freeCarrySize N d hN a := by
  have := componentSize_two N d hN hbig a
  have := deletedPrefix_le_one N d hN a
  unfold freeCarrySize
  omega

lemma freeCarry_position (a : CarryRepresentative N d hN) {t : ℕ}
    (ht : t<freeCarrySize N d hN a) :
    t+deletedPrefix N d hN a<carryComponentSize N d hN a := by
  unfold freeCarrySize at ht
  omega

lemma freeCarryLabel_vertex (a : CarryRepresentative N d hN) {t : ℕ}
    (ht : t<freeCarrySize N d hN a) :
    0<freeCarryLabel N d hN a t ∧ freeCarryLabel N d hN a t<N ∧
      freeCarryLabel N d hN a t≠d := by
  have hv:=carryComponentLabel_vertex N d hN a (freeCarry_position N d hN a ht)
  refine ⟨hv.1,hv.2,?_⟩
  intro he
  have hh:=(fullLabel_eq_pivot_iff N d hN a (freeCarry_position N d hN a ht)).mp he
  simp only [deletedPrefix,if_pos hh.1] at hh
  omega

/-- Retained carry vertices have one canonical run position, including ports. -/
def freeCarryMap (v : Σ a : CarryRepresentative N d hN,Fin (freeCarrySize N d hN a)) :
    {x : ℕ // 0<x ∧ x<N ∧ x≠d} :=
  ⟨freeCarryLabel N d hN v.1 v.2.val,freeCarryLabel_vertex N d hN v.1 v.2.isLt⟩

include hd in
lemma freeCarryMap_injective : Function.Injective (freeCarryMap N d hN) := by
  rintro ⟨a,t⟩ ⟨b,s⟩ he
  have hv:=congrArg Subtype.val he
  have hab:=carryComponentLabel_disjoint N d hd hN a b
    (t.val+deletedPrefix N d hN a) (s.val+deletedPrefix N d hN b) hv
  subst b
  have hts:=carryComponentLabel_injective N d hN a
    (a₁:=⟨t.val+deletedPrefix N d hN a,freeCarry_position N d hN a t.isLt⟩)
    (a₂:=⟨s.val+deletedPrefix N d hN a,freeCarry_position N d hN a s.isLt⟩) hv
  have hv':=congrArg Fin.val hts
  change t.val+deletedPrefix N d hN a=s.val+deletedPrefix N d hN a at hv'
  have he' : t=s := Fin.ext (by omega)
  subst s
  rfl

include hd in
lemma freeCarryMap_surjective : Function.Surjective (freeCarryMap N d hN) := by
  rintro ⟨x,hx⟩
  obtain ⟨a,t,he⟩:=carryComponentLabel_surjective N d hd hN ⟨hx.1,hx.2.1⟩
  have hp : deletedPrefix N d hN a≤t.val := by
    unfold deletedPrefix
    split_ifs with ha
    · by_contra hn
      have ht : t.val=0 := by omega
      have hh:=(fullLabel_eq_pivot_iff N d hN a t.isLt).mpr ⟨ha,ht⟩
      exact hx.2.2 (he.symm.trans hh)
    · omega
  let s : Fin (freeCarrySize N d hN a):=⟨t.val-deletedPrefix N d hN a,by
    have ht:=t.isLt
    unfold freeCarrySize
    omega⟩
  refine ⟨⟨a,s⟩,Subtype.ext ?_⟩
  change carryComponentLabel N d hN a (t.val-deletedPrefix N d hN a+deletedPrefix N d hN a)=x
  rw [Nat.sub_add_cancel hp]
  exact he

/-- A proved global coordinate equivalence, not a run-layout certificate. -/
def freeCarryEquiv :
    (Σ a : CarryRepresentative N d hN,Fin (freeCarrySize N d hN a)) ≃
      {x : ℕ // 0<x ∧ x<N ∧ x≠d} :=
  Equiv.ofBijective (freeCarryMap N d hN)
    ⟨freeCarryMap_injective N d hd hN,freeCarryMap_surjective N d hd hN⟩

/-- All retained carry incidences are exactly consecutive run positions, or
the final loop of a fixed residue class. -/
theorem freeCarry_incidence_iff (a : CarryRepresentative N d hN) {t s : ℕ}
    (ht : t<freeCarrySize N d hN a) (hs : s<freeCarrySize N d hN a) :
    CarryIncidence N d (freeCarryLabel N d hN a t) (freeCarryLabel N d hN a s) ↔
      t+1=s ∨ s+1=t ∨
        (a.val=portPartner N d hN a.val ∧ t=freeCarrySize N d hN a-1 ∧
          s=freeCarrySize N d hN a-1) := by
  have hh:=carry_component_incidence_iff N d hN a
    (freeCarry_position N d hN a ht) (freeCarry_position N d hN a hs)
  unfold freeCarryLabel
  rw [hh]
  unfold freeCarrySize at ht hs ⊢
  omega

include hd in
/-- Different canonical runs have no retained carry incidence. -/
theorem freeCarry_incidence_same (a b : CarryRepresentative N d hN)
    (t : Fin (freeCarrySize N d hN a)) (s : Fin (freeCarrySize N d hN b))
    (hinc : CarryIncidence N d (freeCarryLabel N d hN a t.val) (freeCarryLabel N d hN b s.val)) : a=b :=
  carry_incidence_same_component N d hd hN a b
    ⟨t.val+deletedPrefix N d hN a,freeCarry_position N d hN a t.isLt⟩
    ⟨s.val+deletedPrefix N d hN b,freeCarry_position N d hN b s.isLt⟩ hinc

/-- A retained carry loop occurs only at the final vertex of a fixed class. -/
theorem freeCarry_loop_iff (a : CarryRepresentative N d hN) {t : ℕ}
    (ht : t<freeCarrySize N d hN a) :
    (2*freeCarryLabel N d hN a t=N ∨ 2*freeCarryLabel N d hN a t=N+d) ↔
      a.val=portPartner N d hN a.val ∧ t=freeCarrySize N d hN a-1 := by
  have hh:=freeCarry_incidence_iff N d hN a ht ht
  unfold CarryIncidence at hh
  omega

/-- Every surviving core port is an endpoint of the retained carry run. -/
theorem freeCarry_port_iff (a : CarryRepresentative N d hN) {t : ℕ}
    (ht : t<freeCarrySize N d hN a) :
    freeCarryLabel N d hN a t≤d ↔
      (t=0 ∧ deletedPrefix N d hN a=0) ∨
      (a.val≠portPartner N d hN a.val ∧ t=freeCarrySize N d hN a-1) := by
  have hh:=carryComponentLabel_port_iff N d hN a (freeCarry_position N d hN a ht)
  unfold freeCarryLabel
  rw [hh]
  unfold freeCarrySize at ht ⊢
  omega

/-- Internal carry-run vertices are strictly outside the finite core. -/
lemma freeCarry_internal_gt (a : CarryRepresentative N d hN) {t : ℕ}
    (ht : t<freeCarrySize N d hN a) (hfirst : 0<t) (hlast : t+1<freeCarrySize N d hN a) :
    d<freeCarryLabel N d hN a t := by
  have hh:=freeCarry_port_iff N d hN a ht
  omega

/-- The only zero-edge carry run is a fixed class whose initial pivot was
removed. Its single surviving vertex has the actual final carry loop. -/
theorem freeCarry_zero_edge (hbig : 2*d<N) (a : CarryRepresentative N d hN)
    (hz : freeCarrySize N d hN a=1) :
    a.val.val+1=d ∧ a.val=portPartner N d hN a.val ∧ carryTailSize N d hN a=1 := by
  have hn:=componentPair_two N d hN hbig a
  have hp:=deletedPrefix_le_one N d hN a
  have hs:=componentSize_two N d hN hbig a
  have hf : a.val=portPartner N d hN a.val := by
    by_contra hne
    simp only [freeCarrySize,carryComponentSize,if_neg hne] at hz
    omega
  have he : deletedPrefix N d hN a=1 := by
    unfold freeCarrySize at hz
    omega
  have ha : a.val.val+1=d := by
    unfold deletedPrefix at he
    split_ifs at he <;> omega
  refine ⟨ha,hf,?_⟩
  unfold carryTailSize carryPortArity
  rw [if_pos hf]
  unfold freeCarrySize at hz
  rwa [he] at hz

end Layout
end SubmittedGenus.CapFourMass.CarryLocalization
