import Results.Genus.CapFourMass.SignedReflectionSplit

/-! The fixed zero orbit splits into two strict paths after zero and both
original pivots are removed. Empty sides are kept as empty finite types. -/
namespace SubmittedGenus.CapFourMass.SignedReflectionZeroFixed
open RawGraph RawGraph.SourceModel RawGraph.Topology RawGraph.PackedAcceptance
open ReflectionPairedOrbit ReflectionComponentOrders
open SignedReflectionFreeBlock

variable {g : ℕ} [NeZero g]

abbrev order (n r δ : ℕ) (hfix : (0:Fin g)=mate r 0) (hc : Nat.Coprime δ (n+2)) :=
  SignedReflectionFixed.residueOrder n r (0:Fin g) hfix δ hc

def zeroResidue (n r : ℕ) : PairedCosets (g:=g) (L:=n+2) r 0 := ⟨0,Or.inl (by simp)⟩

def zeroIndex (n r δ : ℕ) (hfix : (0:Fin g)=mate r 0) (hc : Nat.Coprime δ (n+2)) : Fin (n+2) :=
  (order n r δ hfix hc).symm (zeroResidue n r)

lemma zero_value (n r δ : ℕ) (hfix : (0:Fin g)=mate r 0) (hc : Nat.Coprime δ (n+2)) :
    (order n r δ hfix hc (zeroIndex n r δ hfix hc)).val=0 := by
  exact congrArg Subtype.val ((order n r δ hfix hc).apply_symm_apply (zeroResidue n r))

lemma fixed_zero_mod (r : ℕ) (hfix : (0:Fin g)=mate r 0) : r%g=0 := by
  have hh:=congrArg Fin.val hfix
  change 0=(mate r (0:Fin g)).val at hh
  rw [SignedReflectionPaired.mate_zero_val] at hh
  exact hh.symm

def targetResidue (n r t : ℕ) (htm : t<g*(n+2)) (ht0 : t%g=0) :
    PairedCosets (g:=g) (L:=n+2) r 0 := ⟨(t:ZMod (g*(n+2))),Or.inl (by
      rw [ZMod.val_natCast,Nat.mod_eq_of_lt htm,ht0]; rfl)⟩

/-- The two distinct original pivots are exactly zero's two path neighbors.
Their order can depend on parity, so no orientation is assumed. -/
theorem pivot_neighbors (n r p δ : ℕ) (hp : p=r+g*δ) (hr0 : 0<r)
    (hrp : r<p) (hpm : p<g*(n+2)) (hfix : (0:Fin g)=mate r 0)
    (hc : Nat.Coprime δ (n+2)) :
    ∃u v : Fin (n+2),
      (order n r δ hfix hc u).val=(r:ZMod (g*(n+2))) ∧
      (order n r δ hfix hc v).val=(p:ZMod (g*(n+2))) ∧ u≠v ∧
      ((zeroIndex n r δ hfix hc).val+1=u.val ∨ u.val+1=(zeroIndex n r δ hfix hc).val) ∧
      ((zeroIndex n r δ hfix hc).val+1=v.val ∨ v.val+1=(zeroIndex n r δ hfix hc).val) := by
  have hrm : r<g*(n+2) := by omega
  have hrmod:=fixed_zero_mod r hfix
  have hpmod : p%g=0 := by rw [hp]; simpa [Nat.add_mod] using hrmod
  let e:=order n r δ hfix hc
  let u:=e.symm (targetResidue n r r hrm hrmod)
  let v:=e.symm (targetResidue n r p hpm hpmod)
  have hu : (e u).val=(r:ZMod (g*(n+2))) :=
    congrArg Subtype.val (e.apply_symm_apply (targetResidue n r r hrm hrmod))
  have hv : (e v).val=(p:ZMod (g*(n+2))) :=
    congrArg Subtype.val (e.apply_symm_apply (targetResidue n r p hpm hpmod))
  have hz:=zero_value n r δ hfix hc
  change (e (zeroIndex n r δ hfix hc)).val=0 at hz
  have hku : zeroIndex n r δ hfix hc≠u := by
    intro he
    have hh:=congrArg (fun j=>(e j).val) he
    rw [hz,hu] at hh
    exact pivot_ne_zero n r hr0 hrm hh.symm
  have hkv : zeroIndex n r δ hfix hc≠v := by
    intro he
    have hh:=congrArg (fun j=>(e j).val) he
    rw [hz,hv] at hh
    exact pivot_ne_zero n p (by omega) hpm hh.symm
  have huv : u≠v := by
    intro he
    have hh:=congrArg (fun j=>(e j).val.val) he
    change (e u).val.val=(e v).val.val at hh
    rw [hu,hv,ZMod.val_natCast,ZMod.val_natCast,Nat.mod_eq_of_lt hrm,Nat.mod_eq_of_lt hpm] at hh
    omega
  refine ⟨u,v,hu,hv,huv,?_,?_⟩
  · apply ReflectionFixedOrbit.adjacent_of_pair n (0:Fin g)
      (r:ZMod (g*(n+2))) (p:ZMod (g*(n+2)))
      (fixed_origin n r 0 hfix) (gapUnit n δ hc) (gap_value n r p δ hc hp) _ _ hku
    change (e (zeroIndex n r δ hfix hc)).val+(e u).val=(r:ZMod (g*(n+2))) ∨ _
    exact Or.inl (by rw [hz,hu,zero_add])
  · apply ReflectionFixedOrbit.adjacent_of_pair n (0:Fin g)
      (r:ZMod (g*(n+2))) (p:ZMod (g*(n+2)))
      (fixed_origin n r 0 hfix) (gapUnit n δ hc) (gap_value n r p δ hc hp) _ _ hkv
    change (e (zeroIndex n r δ hfix hc)).val+(e v).val=(r:ZMod (g*(n+2))) ∨
      (e (zeroIndex n r δ hfix hc)).val+(e v).val=(p:ZMod (g*(n+2)))
    exact Or.inr (by rw [hz,hv,zero_add])

/-- Zero is strictly internal; deleting its neighbors may still empty either
side. The three forbidden positions are never artificially concatenated. -/
theorem zero_interior (n r p δ : ℕ) (hp : p=r+g*δ) (hr0 : 0<r)
    (hrp : r<p) (hpm : p<g*(n+2)) (hfix : (0:Fin g)=mate r 0)
    (hc : Nat.Coprime δ (n+2)) :
    1≤(zeroIndex n r δ hfix hc).val ∧ (zeroIndex n r δ hfix hc).val+1<n+2 := by
  obtain ⟨u,v,_,_,huv,hu,hv⟩:=pivot_neighbors n r p δ hp hr0 hrp hpm hfix hc
  exact SignedReflectionSplit.interior_of_neighbors _ u v hu hv huv

theorem keep_iff (n r p δ : ℕ) (hp : p=r+g*δ) (hr0 : 0<r)
    (hrp : r<p) (hpm : p<g*(n+2)) (hfix : (0:Fin g)=mate r 0)
    (hc : Nat.Coprime δ (n+2)) (j : Fin (n+2)) :
    (j.val+1<(zeroIndex n r δ hfix hc).val ∨ (zeroIndex n r δ hfix hc).val+1<j.val) ↔
      Keep n r p (order n r δ hfix hc j) := by
  obtain ⟨u,v,hu,hv,huv,hku,hkv⟩:=pivot_neighbors n r p δ hp hr0 hrp hpm hfix hc
  let e:=order n r δ hfix hc
  have hz:=zero_value n r δ hfix hc
  have h0 : (e j).val=0 ↔ j=zeroIndex n r δ hfix hc := by
    constructor
    · intro h; exact e.injective (Subtype.ext (h.trans hz.symm))
    · intro h; exact h ▸ hz
  have h1 : (e j).val=(r:ZMod (g*(n+2))) ↔ j=u := by
    constructor
    · intro h; exact e.injective (Subtype.ext (h.trans hu.symm))
    · intro h; exact h ▸ hu
  have h2 : (e j).val=(p:ZMod (g*(n+2))) ↔ j=v := by
    constructor
    · intro h; exact e.injective (Subtype.ext (h.trans hv.symm))
    · intro h; exact h ▸ hv
  change _ ↔ ((e j).val≠0 ∧ (e j).val≠(r:ZMod (g*(n+2))) ∧ (e j).val≠(p:ZMod (g*(n+2))))
  simp only [Ne,h0,h1,h2]
  exact SignedReflectionSplit.outside_neighbors_iff _ u v j hku hkv huv

abbrev Positions (n r δ : ℕ) (hfix : (0:Fin g)=mate r 0) (hc : Nat.Coprime δ (n+2)) :=
  SignedReflectionSplit.Positions n (zeroIndex n r δ hfix hc)

def residueEquiv (n r p δ : ℕ) (hp : p=r+g*δ) (hr0 : 0<r)
    (hrp : r<p) (hpm : p<g*(n+2)) (hfix : (0:Fin g)=mate r 0)
    (hc : Nat.Coprime δ (n+2)) :
    Positions n r δ hfix hc ≃ FreeResidue n r p (0:Fin g) :=
  (SignedReflectionSplit.equiv n (zeroIndex n r δ hfix hc)).trans
    ((order n r δ hfix hc).subtypeEquiv (fun j=>keep_iff n r p δ hp hr0 hrp hpm hfix hc j))

@[simp] lemma residueEquiv_value (n r p δ : ℕ) (hp : p=r+g*δ) (hr0 : 0<r)
    (hrp : r<p) (hpm : p<g*(n+2)) (hfix : (0:Fin g)=mate r 0)
    (hc : Nat.Coprime δ (n+2)) (i : Positions n r δ hfix hc) :
    (residueEquiv n r p δ hp hr0 hrp hpm hfix hc i).val.val=
      (order n r δ hfix hc (SignedReflectionSplit.index n (zeroIndex n r δ hfix hc) i)).val := rfl

def splitEquiv (n r p δ : ℕ) (hp : p=r+g*δ) (hr0 : 0<r)
    (hrp : r<p) (hpm : p<g*(n+2)) (hfix : (0:Fin g)=mate r 0)
    (hc : Nat.Coprime δ (n+2)) :
    Positions n r δ hfix hc ≃ {v : FreeVertex (g*(n+2)) r p // SignedReflectionPaired.InBlock n r p 0 v} :=
  (residueEquiv n r p δ hp hr0 hrp hpm hfix hc).trans
    (SignedReflectionFreeBlock.equiv n r p (by omega) hpm 0)

/-- Exactly the two separate path adjacency relations survive. -/
theorem original_adjacency_iff (n r p δ : ℕ) (hp : p=r+g*δ) (hr0 : 0<r)
    (hrp : r<p) (hpm : p<g*(n+2)) (hfix : (0:Fin g)=mate r 0)
    (hc : Nat.Coprime δ (n+2)) (i j : Positions n r δ hfix hc) :
    (freeGraph (g*(n+2)) r p).Adj
      ((splitEquiv n r p δ hp hr0 hrp hpm hfix hc) i).val
      ((splitEquiv n r p δ hp hr0 hrp hpm hfix hc) j).val ↔
      SignedReflectionSplit.Adjacent n (zeroIndex n r δ hfix hc) i j := by
  change (freeGraph (g*(n+2)) r p).Adj
    (vertex n r p 0 (residueEquiv n r p δ hp hr0 hrp hpm hfix hc i))
    (vertex n r p 0 (residueEquiv n r p δ hp hr0 hrp hpm hfix hc j)) ↔ _
  rw [vertex_adjacent_iff n r p (by omega) hpm 0]
  simp only [residueEquiv_value]
  let k:=zeroIndex n r δ hfix hc
  let ix:=SignedReflectionSplit.index n k
  have hadj:=SignedReflectionFixed.adjacent_iff_pair n (0:Fin g)
    (r:ZMod (g*(n+2))) (p:ZMod (g*(n+2)))
    (fixed_origin n r 0 hfix) (gapUnit n δ hc) (gap_value n r p δ hc hp) (ix i) (ix j)
  constructor
  · rintro ⟨hne,hp⟩
    apply (SignedReflectionSplit.index_adjacent_iff n k i j).mp
    apply hadj.mpr
    refine ⟨?_,hp⟩
    intro he
    exact hne (congrArg (residueEquiv n r p δ ‹p=r+g*δ› hr0 hrp hpm hfix hc)
      (SignedReflectionSplit.index_injective n k he))
  · intro h
    have hpos:=(SignedReflectionSplit.index_adjacent_iff n k i j).mpr h
    have hh:=hadj.mp hpos
    refine ⟨?_,hh.2⟩
    intro he
    have hij:=(residueEquiv n r p δ hp hr0 hrp hpm hfix hc).injective he
    exact hh.1 (congrArg ix hij)

/-- Local source geometry for the complete fixed-zero block, with both
possibly empty components retained as an exact disjoint sum. -/
theorem strict_split (n r p δ : ℕ) (hp : p=r+g*δ) (hr0 : 0<r)
    (hrp : r<p) (hpm : p<g*(n+2)) (hfix : (0:Fin g)=mate r 0)
    (hc : Nat.Coprime δ (n+2)) :
    (∀i j, (freeGraph (g*(n+2)) r p).Adj
      ((splitEquiv n r p δ hp hr0 hrp hpm hfix hc) i).val
      ((splitEquiv n r p δ hp hr0 hrp hpm hfix hc) j).val ↔
      SignedReflectionSplit.Adjacent n (zeroIndex n r δ hfix hc) i j) ∧
    (∀x y : FreeVertex (g*(n+2)) r p, SignedReflectionPaired.InBlock n r p 0 x →
      (freeGraph (g*(n+2)) r p).Adj x y → SignedReflectionPaired.InBlock n r p 0 y) :=
  ⟨original_adjacency_iff n r p δ hp hr0 hrp hpm hfix hc,
    SignedReflectionPaired.block_closed n r p δ hp hpm 0⟩

end SubmittedGenus.CapFourMass.SignedReflectionZeroFixed
