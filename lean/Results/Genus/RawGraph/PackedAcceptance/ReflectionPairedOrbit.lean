import Results.Genus.RawGraph.PackedAcceptance.ReflectionCoset
import Results.Genus.RawGraph.PackedAcceptance.ReflectionOrbitDelete

/-! Computable alternating orders for paired translation cosets in the original
two-reflection graph. No enumeration oracle or noncomputable finite equivalence. -/
namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionPairedOrbit

/-- Even positions visit the first coset and odd positions its reflected mate. -/
def parityEquiv (L : ℕ) : Fin (2*L) ≃ Bool × Fin L where
  toFun j := (decide (j.val%2=1),⟨j.val/2,by have:=j.isLt; omega⟩)
  invFun q := ⟨2*q.2.val+(if q.1 then 1 else 0),by have:=q.2.isLt; split <;> omega⟩
  left_inv j := by
    apply Fin.ext
    change 2*(j.val/2)+(if decide (j.val%2=1) then 1 else 0)=j.val
    by_cases hp : j.val%2=1 <;> simp [hp] <;> omega
  right_inv q := by
    rcases q with ⟨b,k⟩
    cases b <;> apply Prod.ext
    · simp
    · apply Fin.ext
      change (2*k.val+0)/2=k.val
      omega
    · simp
    · apply Fin.ext
      change (2*k.val+1)/2=k.val
      omega

@[simp] lemma parityEquiv_symm_even (L : ℕ) (k : Fin L) :
    ((parityEquiv L).symm (false,k)).val=2*k.val := rfl
@[simp] lemma parityEquiv_symm_odd (L : ℕ) (k : Fin L) :
    ((parityEquiv L).symm (true,k)).val=2*k.val+1 := rfl

/-- Reduction of the actual full residue graph to its translation-coset label. -/
def reduce (g L : ℕ) : ZMod (g*L) →+* ZMod g :=
  ZMod.castHom (Nat.dvd_mul_right g L) (ZMod g)

lemma reduce_val (g L : ℕ) (hg : 0<g) (hL : 0<L) (x : ZMod (g*L)) :
    (reduce g L x).val=x.val%g := by
  letI : NeZero (g*L) := ⟨ne_of_gt (Nat.mul_pos hg hL)⟩
  simp only [reduce,ZMod.castHom_apply,ZMod.cast_eq_val,ZMod.val_natCast]

lemma reduce_reflect (g L r : ℕ) (x : ZMod (g*L)) :
    reduce g L ((r : ZMod (g*L))-x)=(r : ZMod g)-reduce g L x := by
  rw [map_sub,map_natCast]

/-- Correct modular partner, including a>r. Natural truncated subtraction
is never used to represent a reflection. -/
def partner (g r : ℕ) (hg : 0<g) (a : Fin g) : Fin g :=
  letI : NeZero g := ⟨ne_of_gt hg⟩
  ⟨((r : ZMod g)-(a.val : ZMod g)).val,ZMod.val_lt _⟩

@[simp] lemma partner_val (g r : ℕ) (hg : 0<g) (a : Fin g) :
    (partner g r hg a).val=((r : ZMod g)-(a.val : ZMod g)).val := rfl

lemma partner_involutive (g r : ℕ) (hg : 0<g) : Function.Involutive (partner g r hg) := by
  letI : NeZero g := ⟨ne_of_gt hg⟩
  intro a
  apply Fin.ext
  simp only [partner_val,ZMod.natCast_zmod_val,sub_sub_cancel,ZMod.val_natCast,Nat.mod_eq_of_lt a.isLt]

/-- Reflection sends precisely the a-coset to its proved modular partner. -/
lemma reflect_coset (g L r : ℕ) (hg : 0<g) (hL : 0<L) (a : Fin g) (x : ZMod (g*L))
    (hx : x.val%g=a.val) :
    ((r : ZMod (g*L))-x).val%g=(partner g r hg a).val := by
  letI : NeZero g := ⟨ne_of_gt hg⟩
  have he : reduce g L x=(a.val : ZMod g) := by
    rw [← ZMod.natCast_zmod_val (reduce g L x),reduce_val g L hg hL,hx]
  rw [← reduce_val g L hg hL,reduce_reflect,he,partner_val]


section Cosets
variable {g L : ℕ} [NeZero g] [NeZero L]
open ReflectionCoset

abbrev mate (r : ℕ) (a : Fin g) : Fin g := partner g r (NeZero.pos g) a

abbrev PairedCosets (r : ℕ) (a : Fin g) :=
  {x : ZMod (g*L) // x.val%g=a.val ∨ x.val%g=(mate r a).val}

def reflectionEquiv (r : ℕ) (a : Fin g) : Coset g L a ≃ Coset g L (mate r a) where
  toFun x := ⟨(r : ZMod (g*L))-x.val,reflect_coset g L r (NeZero.pos g) (NeZero.pos L) a x.val x.property⟩
  invFun y := ⟨(r : ZMod (g*L))-y.val,by
    have hh:=reflect_coset g L r (NeZero.pos g) (NeZero.pos L) (mate r a) y.val y.property
    simpa only [mate,partner_involutive g r (NeZero.pos g) a] using hh⟩
  left_inv x := Subtype.ext (sub_sub_cancel _ _)
  right_inv y := Subtype.ext (sub_sub_cancel _ _)

def splitCosets (r : ℕ) (a : Fin g) (ha : a≠mate r a) :
    Coset g L a ⊕ Coset g L (mate r a) ≃ PairedCosets (L:=L) r a where
  toFun x := match x with
    | .inl x => ⟨x.val,Or.inl x.property⟩
    | .inr y => ⟨y.val,Or.inr y.property⟩
  invFun x := if hx : x.val.val%g=a.val then .inl ⟨x.val,hx⟩
    else .inr ⟨x.val,x.property.resolve_left hx⟩
  left_inv x := by
    cases x with
    | inl x => simp only [dif_pos x.property]
    | inr y =>
      have hn : ¬y.val.val%g=a.val := by
        intro he
        exact ha (Fin.ext (he.symm.trans y.property))
      simp only [dif_neg hn]
  right_inv x := by
    dsimp only
    split_ifs <;> rfl

def boolSumEquiv (L : ℕ) : Bool × Fin L ≃ Fin L ⊕ Fin L where
  toFun x := if x.1 then .inr x.2 else .inl x.2
  invFun x := match x with | .inl k => (false,k) | .inr k => (true,k)
  left_inv x := by rcases x with ⟨b,k⟩; cases b <;> rfl
  right_inv x := by cases x <;> rfl

/-- A computable alternating order of two reflected cosets, from any explicit
coordinate order on the first coset. Its inverse tests the actual coset label. -/
def order (r : ℕ) (a : Fin g) (ha : a≠mate r a) (e : Fin L ≃ Coset g L a) :
    Fin (2*L) ≃ PairedCosets (L:=L) r a :=
  (parityEquiv L).trans ((boolSumEquiv L).trans
    ((Equiv.sumCongr e (e.trans (reflectionEquiv r a))).trans (splitCosets r a ha)))

lemma order_even (r : ℕ) (a : Fin g) (ha : a≠mate r a) (e : Fin L ≃ Coset g L a) (k : Fin L) :
    (order r a ha e ((parityEquiv L).symm (false,k))).val=(e k).val := by
  simp only [order,Equiv.trans_apply,Equiv.apply_symm_apply]
  rfl

lemma order_odd (r : ℕ) (a : Fin g) (ha : a≠mate r a) (e : Fin L ≃ Coset g L a) (k : Fin L) :
    (order r a ha e ((parityEquiv L).symm (true,k))).val=(r : ZMod (g*L))-(e k).val := by
  simp only [order,Equiv.trans_apply,Equiv.apply_symm_apply]
  rfl

/-- Multiplication by an explicit unit, with its executable inverse. -/
def scale (u : (ZMod L)ˣ) : ZMod L ≃ ZMod L where
  toFun x := (u : ZMod L)*x
  invFun x := ((u⁻¹ : (ZMod L)ˣ) : ZMod L)*x
  left_inv x := by simp [← mul_assoc]
  right_inv x := by simp [← mul_assoc]

def unitCoordinates (u : (ZMod L)ˣ) : Fin L ≃ Fin L :=
  (ZMod.finEquiv L).toEquiv.trans ((scale u).trans (ZMod.finEquiv L).symm.toEquiv)

lemma unitCoordinates_val (u : (ZMod L)ˣ) (k : Fin L) :
    (unitCoordinates u k).val=((u : ZMod L)*(k.val : ZMod L)).val := by
  cases L with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
    have hk:=ZMod.natCast_zmod_val ((ZMod.finEquiv (n+1)) k)
    change (k.val : ZMod (n+1))=(ZMod.finEquiv (n+1)) k at hk
    rw [hk]
    rfl

/-- The original translation orbit within the first residue class. -/
def orbit (a : Fin g) (δ : ℕ) (hc : Nat.Coprime δ L) : Fin L ≃ Coset g L a :=
  (unitCoordinates (ZMod.unitOfCoprime δ hc)).trans (ReflectionCoset.equiv a)

lemma orbit_val (a : Fin g) (δ : ℕ) (hc : Nat.Coprime δ L) (k : Fin L) :
    ((orbit a δ hc k).val).val=a.val+g*((δ*k.val)%L) := by
  rw [orbit,Equiv.trans_apply,ReflectionCoset.equiv_apply_val,unitCoordinates_val]
  change a.val+g*((δ : ZMod L)*(k.val : ZMod L)).val= _
  rw [← Nat.cast_mul,ZMod.val_natCast]

omit [NeZero g] [NeZero L] in
lemma cast_mul_mod (n : ℕ) :
    ((g*(n%L) : ℕ) : ZMod (g*L))=((g*n : ℕ) : ZMod (g*L)) := by
  have hh : g*n=g*(n%L)+(g*L)*(n/L) := by
    have h:=Nat.mod_add_div n L
    nlinarith
  have hz : ((g*L*(n/L) : ℕ) : ZMod (g*L))=0 := by
    rw [Nat.cast_mul,ZMod.natCast_self,zero_mul]
  conv_rhs => rw [hh]
  simp only [Nat.cast_add,hz,add_zero]

lemma orbit_value (a : Fin g) (δ : ℕ) (hc : Nat.Coprime δ L) (k : Fin L) :
    (orbit a δ hc k).val=(a.val : ZMod (g*L))+(g : ZMod (g*L))*δ*k.val := by
  rw [← ZMod.natCast_zmod_val (orbit a δ hc k).val,orbit_val,Nat.cast_add,cast_mul_mod]
  simp only [Nat.cast_mul,mul_assoc]

def next (k : Fin L) : Fin L := ⟨(k.val+1)%L,Nat.mod_lt _ (NeZero.pos L)⟩

lemma orbit_next (a : Fin g) (δ : ℕ) (hc : Nat.Coprime δ L) (k : Fin L) :
    (orbit a δ hc (next k)).val=(orbit a δ hc k).val+((g*δ : ℕ) : ZMod (g*L)) := by
  rw [orbit_value,orbit_value]
  have hh:=cast_mul_mod (g:=g) (L:=L) (k.val+1)
  simp only [Nat.cast_mul,Nat.cast_add,Nat.cast_one] at hh
  change (a.val : ZMod (g*L))+(g : ZMod (g*L))*δ*((k.val+1)%L : ℕ) = _
  calc
    _=(a.val : ZMod (g*L))+(δ : ZMod (g*L))*((g : ZMod (g*L))*((k.val+1)%L : ℕ)) := by ring
    _=(a.val : ZMod (g*L))+(δ : ZMod (g*L))*((g : ZMod (g*L))*(k.val+1)) := by rw [hh]
    _=_ := by simp only [Nat.cast_mul]; ring

def canonicalOrder (r : ℕ) (a : Fin g) (ha : a≠mate r a) (δ : ℕ) (hc : Nat.Coprime δ L) :
    Fin (2*L) ≃ PairedCosets (L:=L) r a := order r a ha (orbit a δ hc)

lemma canonicalOrder_even (r : ℕ) (a : Fin g) (ha : a≠mate r a)
    (δ : ℕ) (hc : Nat.Coprime δ L) (k : Fin L) :
    (canonicalOrder r a ha δ hc ((parityEquiv L).symm (false,k))).val.val=
      a.val+g*((δ*k.val)%L) := by
  rw [canonicalOrder,order_even,orbit_val]

lemma canonicalOrder_odd (r : ℕ) (a : Fin g) (ha : a≠mate r a)
    (δ : ℕ) (hc : Nat.Coprime δ L) (k : Fin L) :
    (canonicalOrder r a ha δ hc ((parityEquiv L).symm (true,k))).val=
      (r : ZMod (g*L))-((a.val+g*((δ*k.val)%L) : ℕ) : ZMod (g*L)) := by
  rw [canonicalOrder,order_odd,← ZMod.natCast_zmod_val (orbit a δ hc k).val,orbit_val]

/-- Consecutive positions or the single closing edge of the displayed cycle. -/
def CycleAdjacent (i j : Fin (2*L)) : Prop :=
  i.val+1=j.val ∨ j.val+1=i.val ∨
    (i.val=0 ∧ j.val+1=2*L) ∨ (j.val=0 ∧ i.val+1=2*L)

omit [NeZero L] in
lemma CycleAdjacent.symm {i j : Fin (2*L)} (h : CycleAdjacent i j) : CycleAdjacent j i := by
  unfold CycleAdjacent at *
  tauto

omit [NeZero L] in
lemma adjacent_even_odd (k : Fin L) :
    CycleAdjacent ((parityEquiv L).symm (false,k)) ((parityEquiv L).symm (true,k)) := by
  exact Or.inl rfl

lemma adjacent_next_odd (k : Fin L) :
    CycleAdjacent ((parityEquiv L).symm (false,next k)) ((parityEquiv L).symm (true,k)) := by
  by_cases h : k.val+1<L
  · right; left
    change 2*k.val+1+1=2*((k.val+1)%L)
    rw [Nat.mod_eq_of_lt h]
    omega
  · right; right; left
    have he : k.val+1=L := by have:=k.isLt; omega
    simp only [parityEquiv_symm_even,parityEquiv_symm_odd,next,he,Nat.mod_self,mul_zero]
    constructor
    · trivial
    · omega

lemma same_coset_sum_ne (r : ℕ) (a : Fin g) (ha : a≠mate r a)
    (x y : ZMod (g*L)) (hx : x.val%g=a.val) (hy : y.val%g=a.val) :
    reduce g L (x+y)≠(r : ZMod g) := by
  intro h
  have hx' : reduce g L x=(a.val : ZMod g) := by
    rw [← ZMod.natCast_zmod_val (reduce g L x),reduce_val g L (NeZero.pos g) (NeZero.pos L),hx]
  have hy' : reduce g L y=(r : ZMod g)-(a.val : ZMod g) := by
    rw [map_add,hx'] at h
    exact eq_sub_of_add_eq' h
  have hv:=congrArg ZMod.val hy'
  rw [reduce_val g L (NeZero.pos g) (NeZero.pos L),hy] at hv
  exact ha (Fin.ext hv)

lemma mate_ne (r : ℕ) (a : Fin g) (ha : a≠mate r a) : mate r a≠mate r (mate r a) := by
  rw [show mate r (mate r a)=a from partner_involutive g r (NeZero.pos g) a]
  exact Ne.symm ha

omit [NeZero g] in
lemma even_odd_of_pair (r : ℕ) (a : Fin g)
    (e : Fin L ≃ Coset g L a) (gap : ZMod (g*L))
    (hstep : ∀ k, (e (next k)).val=(e k).val+gap) (k l : Fin L)
    (h : (e k).val+((r : ZMod (g*L))-(e l).val)=(r : ZMod (g*L)) ∨
      (e k).val+((r : ZMod (g*L))-(e l).val)=(r : ZMod (g*L))+gap) :
    CycleAdjacent ((parityEquiv L).symm (false,k)) ((parityEquiv L).symm (true,l)) := by
  rcases h with h|h
  · have he : (e k).val=(e l).val := by
      calc
        _=((e k).val+((r : ZMod (g*L))-(e l).val))-r+(e l).val := by ring
        _=_ := by rw [h]; ring
    have hk:=e.injective (Subtype.ext he)
    subst k
    exact adjacent_even_odd l
  · have he : (e k).val=(e (next l)).val := by
      rw [hstep]
      calc
        _=((e k).val+((r : ZMod (g*L))-(e l).val))-r+(e l).val := by ring
        _=_ := by rw [h]; ring
    have hk:=e.injective (Subtype.ext he)
    subst k
    exact adjacent_next_odd l

/-- Source-exact coverage of both reflections, assuming only the actual orbit
translation identity and that the gap preserves the coset label. -/
lemma order_adjacent (r : ℕ) (a : Fin g) (ha : a≠mate r a)
    (e : Fin L ≃ Coset g L a) (gap : ZMod (g*L))
    (hgap : reduce g L gap=0) (hstep : ∀ k, (e (next k)).val=(e k).val+gap)
    (i j : Fin (2*L))
    (h : (order r a ha e i).val+(order r a ha e j).val=(r : ZMod (g*L)) ∨
      (order r a ha e i).val+(order r a ha e j).val=(r : ZMod (g*L))+gap) :
    CycleAdjacent i j := by
  obtain ⟨⟨b,k⟩,rfl⟩ := (parityEquiv L).symm.surjective i
  obtain ⟨⟨c,l⟩,rfl⟩ := (parityEquiv L).symm.surjective j
  have hred : reduce g L ((order r a ha e ((parityEquiv L).symm (b,k))).val+
      (order r a ha e ((parityEquiv L).symm (c,l))).val)=(r : ZMod g) := by
    rcases h with h|h
    · rw [h,map_natCast]
    · rw [h,map_add,map_natCast,hgap,add_zero]
  cases b <;> cases c
  · rw [order_even,order_even] at hred
    exact (same_coset_sum_ne r a ha _ _ (e k).property (e l).property hred).elim
  · rw [order_even,order_odd] at h
    exact even_odd_of_pair r a e gap hstep k l h
  · rw [order_odd,order_even] at h
    rw [add_comm ((r : ZMod (g*L))-(e k).val)] at h
    exact (even_odd_of_pair r a e gap hstep l k h).symm
  · rw [order_odd,order_odd] at hred
    exact (same_coset_sum_ne r (mate r a) (mate_ne r a ha) _ _
      (reflectionEquiv r a (e k)).property (reflectionEquiv r a (e l)).property hred).elim

lemma canonicalOrder_adjacent (r : ℕ) (a : Fin g) (ha : a≠mate r a)
    (δ : ℕ) (hc : Nat.Coprime δ L) (i j : Fin (2*L))
    (h : (canonicalOrder r a ha δ hc i).val+(canonicalOrder r a ha δ hc j).val=(r : ZMod (g*L)) ∨
      (canonicalOrder r a ha δ hc i).val+(canonicalOrder r a ha δ hc j).val=((r+g*δ : ℕ) : ZMod (g*L))) :
    CycleAdjacent i j := by
  apply order_adjacent r a ha (orbit a δ hc) ((g*δ : ℕ) : ZMod (g*L))
  · rw [map_natCast,Nat.cast_mul,ZMod.natCast_self,zero_mul]
  · exact orbit_next a δ hc
  · simpa only [canonicalOrder,Nat.cast_add] using h


lemma canonicalOrder_zero (r : ℕ) (ha : (0 : Fin g)≠mate r 0)
    (δ : ℕ) (hc : Nat.Coprime δ L) :
    (canonicalOrder r 0 ha δ hc 0).val=0 := by
  have h:=canonicalOrder_even r 0 ha δ hc (0 : Fin L)
  have hz : (parityEquiv L).symm (false,(0 : Fin L))=0 := by
    apply Fin.ext
    simp only [parityEquiv_symm_even,Fin.val_zero,Nat.mul_zero]
  rw [hz] at h
  simp only [Fin.val_zero,Nat.mul_zero,Nat.zero_mod,Nat.add_zero] at h
  rw [← ZMod.natCast_zmod_val (canonicalOrder r 0 ha δ hc 0).val,h,Nat.cast_zero]

/-- Arithmetic index transport for the generic zero-deletion adapter. -/
def zeroIndexedOrder (r : ℕ) (ha : (0 : Fin g)≠mate r 0)
    (δ : ℕ) (hc : Nat.Coprime δ L) : Fin ((2*L-2)+2) ≃ PairedCosets (g:=g) (L:=L) r 0 :=
  (finCongr (by have:=NeZero.pos L; omega)).trans (canonicalOrder r 0 ha δ hc)

lemma zeroIndexedOrder_zero (r : ℕ) (ha : (0 : Fin g)≠mate r 0)
    (δ : ℕ) (hc : Nat.Coprime δ L) :
    (zeroIndexedOrder r ha δ hc ⟨0,by omega⟩).val=0 := by
  exact canonicalOrder_zero r ha δ hc

/-- Deleting the unique zero residue turns its paired cycle into one explicit
path. All other paired classes retain their full cycles. -/
def zeroDeletedOrder (r : ℕ) (ha : (0 : Fin g)≠mate r 0)
    (δ : ℕ) (hc : Nat.Coprime δ L) :
    Fin (2*L-1) ≃ {x : PairedCosets (g:=g) (L:=L) r 0 // x.val≠0} :=
  (finCongr (by have:=NeZero.pos L; omega : 2*L-1=(2*L-2)+1)).trans
    (ReflectionOrbitDelete.deleteSubtypeZero (zeroIndexedOrder r ha δ hc)
      ⟨0,by omega⟩ (zeroIndexedOrder_zero r ha δ hc))

lemma zeroDeletedOrder_val (r : ℕ) (ha : (0 : Fin g)≠mate r 0)
    (δ : ℕ) (hc : Nat.Coprime δ L) (j : Fin (2*L-1)) :
    (zeroDeletedOrder r ha δ hc j).val.val=
      (canonicalOrder r 0 ha δ hc ⟨j.val+1,by have:=j.isLt; omega⟩).val := by
  rw [zeroDeletedOrder,Equiv.trans_apply,ReflectionOrbitDelete.deleteSubtypeZero_val]
  change (canonicalOrder r 0 ha δ hc _).val=(canonicalOrder r 0 ha δ hc _).val
  congr 2

lemma zeroDeletedOrder_adjacent (r : ℕ) (ha : (0 : Fin g)≠mate r 0)
    (δ : ℕ) (hc : Nat.Coprime δ L) (i j : Fin (2*L-1))
    (h : (zeroDeletedOrder r ha δ hc i).val.val+(zeroDeletedOrder r ha δ hc j).val.val=(r : ZMod (g*L)) ∨
      (zeroDeletedOrder r ha δ hc i).val.val+(zeroDeletedOrder r ha δ hc j).val.val=
        ((r+g*δ : ℕ) : ZMod (g*L))) :
    i.val+1=j.val ∨ j.val+1=i.val := by
  rw [zeroDeletedOrder_val,zeroDeletedOrder_val] at h
  have hh:=canonicalOrder_adjacent r 0 ha δ hc _ _ h
  dsimp only [CycleAdjacent] at hh
  omega

/-- Every displayed even/odd edge is the original r-reflection. -/
lemma canonicalOrder_even_odd_sum (r : ℕ) (a : Fin g) (ha : a≠mate r a)
    (δ : ℕ) (hc : Nat.Coprime δ L) (k : Fin L) :
    (canonicalOrder r a ha δ hc ((parityEquiv L).symm (false,k))).val+
      (canonicalOrder r a ha δ hc ((parityEquiv L).symm (true,k))).val=(r : ZMod (g*L)) := by
  rw [canonicalOrder,order_even,order_odd]
  ring

/-- Every displayed odd/next-even edge is the original p-reflection,
including the last-to-first closing edge. -/
lemma canonicalOrder_next_odd_sum (r : ℕ) (a : Fin g) (ha : a≠mate r a)
    (δ : ℕ) (hc : Nat.Coprime δ L) (k : Fin L) :
    (canonicalOrder r a ha δ hc ((parityEquiv L).symm (false,next k))).val+
      (canonicalOrder r a ha δ hc ((parityEquiv L).symm (true,k))).val=
        ((r+g*δ : ℕ) : ZMod (g*L)) := by
  rw [canonicalOrder,order_even,order_odd,orbit_next,Nat.cast_add]
  ring

end Cosets
/-- Cheap executable full-cycle fixture: M=8,r=1,p=5, paired classes0 and1. -/
lemma fixture_eight_zero :
    List.ofFn (fun j : Fin 4 =>
      (canonicalOrder (g:=4) (L:=2) 1 0 (by decide +kernel) 1 (by decide) j).val.val)=
      [0,1,4,5] := by decide +kernel

/-- The second paired cycle of the same original graph. -/
lemma fixture_eight_two :
    List.ofFn (fun j : Fin 4 =>
      (canonicalOrder (g:=4) (L:=2) 1 2 (by decide +kernel) 1 (by decide) j).val.val)=
      [2,7,6,3] := by decide +kernel

lemma fixture_twelve_zero :
    List.ofFn (fun j : Fin 4 =>
      (canonicalOrder (g:=6) (L:=2) 2 0 (by decide +kernel) 1 (by decide) j).val.val)=
      [0,2,6,8] := by decide +kernel

lemma fixture_twelve_three :
    List.ofFn (fun j : Fin 4 =>
      (canonicalOrder (g:=6) (L:=2) 2 3 (by decide +kernel) 1 (by decide) j).val.val)=
      [3,11,9,5] := by decide +kernel

lemma fixture_eight_deleted :
    List.ofFn (fun j : Fin 3 =>
      (zeroDeletedOrder (g:=4) (L:=2) 1 (by decide +kernel) 1 (by decide) j).val.val.val)=
      [1,4,5] := by decide +kernel

end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionPairedOrbit
