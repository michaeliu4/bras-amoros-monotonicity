import Results.Genus.RawGraph.PackedAcceptance.ReflectionFixedSourceWindow

/-! Exact fixed-path aligned pair letters. Only masks at interior nonpivot
positions use the old alphabet; endpoint/pivot masks remain separate fields. -/
namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionFixedSourceWindow
open SourceModel ReflectionCoset ReflectionFixedOrbit ReflectionComponentOrders
open ReflectionFixedPhase ReflectionThresholdWord
variable {g : ℕ} [NeZero g]

lemma aligned_pair_sum (n r δ : ℕ) (a : Fin g) (hfix : a=ReflectionPairedOrbit.mate r a)
    (hc : Nat.Coprime δ (n+2)) (k : ℕ) (i j : Fin (n+2))
    (hi : i.val=alignment (targetIndex n r δ a hfix hc)+2*k)
    (hj : j.val=alignment (targetIndex n r δ a hfix hc)+2*k+1) :
    residue n r δ a hfix hc i+residue n r δ a hfix hc j=(r:ZMod (g*(n+2))) := by
  change (order n a r (fixed_origin n r a hfix) (gapUnit n δ hc) i).val+
    (order n a r (fixed_origin n r a hfix) (gapUnit n δ hc) j).val=_
  rw [order_val,order_val,affineValue_pair_iff a r _ _ _ (target_value n a r (fixed_origin n r a hfix))]
  rw [phase_aligned_even n _ _ k i hi,phase_aligned_odd n _ _ k j hj]
  ring

lemma aligned_next (n r δ : ℕ) (a : Fin g) (hfix : a=ReflectionPairedOrbit.mate r a)
    (hc : Nat.Coprime δ (n+2)) (k : ℕ) (i w : Fin (n+2))
    (hi : i.val=alignment (targetIndex n r δ a hfix hc)+2*k)
    (hw : w.val=alignment (targetIndex n r δ a hfix hc)+2*(k+1)) :
    residue n r δ a hfix hc w=residue n r δ a hfix hc i+((g*δ:ℕ):ZMod (g*(n+2))) := by
  change (order n a r (fixed_origin n r a hfix) (gapUnit n δ hc) w).val=
    (order n a r (fixed_origin n r a hfix) (gapUnit n δ hc) i).val+_
  rw [order_val,order_val,phase_aligned_even n _ _ (k+1) w hw,phase_aligned_even n _ _ k i hi]
  have hcoef : (gapUnit n δ hc:ZMod (n+2))*
      (((normalizedTarget n (target n a r (fixed_origin n r a hfix)) (gapUnit n δ hc)).val/2+1+(k+1):ℕ):ZMod (n+2))=
      (gapUnit n δ hc:ZMod (n+2))*
      (((normalizedTarget n (target n a r (fixed_origin n r a hfix)) (gapUnit n δ hc)).val/2+1+k:ℕ):ZMod (n+2))+
      (δ:ZMod (n+2)) := by rw [ZMod.coe_unitOfCoprime];push_cast;ring
  rw [hcoef,affineValue_add,scaleHom_natCast]

/-- Source-exact old pair thresholds at any complete aligned three-vertex
window. Ordinary endpoint loops do not alter these edges, but pivots do. -/
theorem aligned_source_letter (n r p δ cap : ℕ) (hr : 0<r) (hδ : 0<δ)
    (hp : p=r+g*δ) (hpm : p<g*(n+2)) (a : Fin g)
    (hfix : a=ReflectionPairedOrbit.mate r a) (hc : Nat.Coprime δ (n+2))
    (k : ℕ) (i j w : Fin (n+2))
    (hi : i.val=alignment (targetIndex n r δ a hfix hc)+2*k)
    (hj : j.val=alignment (targetIndex n r δ a hfix hc)+2*k+1)
    (hw : w.val=alignment (targetIndex n r δ a hfix hc)+2*(k+1))
    (hi0 : residue n r δ a hfix hc i≠0) (hj0 : residue n r δ a hfix hc j≠0)
    (hw0 : residue n r δ a hfix hc w≠0)
    (hif : IsFree r p (point n r δ a hfix hc i hi0))
    (hjf : IsFree r p (point n r δ a hfix hc j hj0))
    (hwf : IsFree r p (point n r δ a hfix hc w hw0)) :
    let q:=letter (g*(n+2)) r (g*δ)
      (a.val+g*((startPhase n δ (targetIndex n r δ a hfix hc)+δ*k)%(n+2)))
    edgeBound r p cap (point n r δ a hfix hc i hi0) (point n r δ a hfix hc j hj0)=evenBound cap q ∧
    edgeBound r p cap (point n r δ a hfix hc j hj0) (point n r δ a hfix hc w hw0)=oddBound cap q ∧
    (¬endpoint n i→¬endpoint n j→∀v : Fin (cap+1),
      decide (Domain r p cap (point n r δ a hfix hc i hi0) v.val)=ReflectionThresholdWord.mask cap q v ∧
      decide (Domain r p cap (point n r δ a hfix hc j hj0) v.val)=ReflectionThresholdWord.mask cap q v) := by
  dsimp only
  let X:=residue n r δ a hfix hc i
  let Y:=residue n r δ a hfix hc j
  let Z:=residue n r δ a hfix hc w
  have hx : X.val=a.val+g*((startPhase n δ (targetIndex n r δ a hfix hc)+δ*k)%(n+2)) :=
    source_even n r δ a hfix hc k i hi
  have hxy : X.val+Y.val=r ∨ X.val+Y.val=g*(n+2)+r := by
    have h:= (targetPair_iff_zmod (by omega : r<g*(n+2))
      (point n r δ a hfix hc i hi0) (point n r δ a hfix hc j hj0)).mpr
      (by simpa only [physical_point,ZMod.natCast_zmod_val] using aligned_pair_sum n r δ a hfix hc k i j hi hj)
    simpa only [TargetPair,physical_point] using h
  have hz : Z.val=(X.val+g*δ)%(g*(n+2)) := by
    have h:=aligned_next n r δ a hfix hc k i w hi hw
    change Z=X+((g*δ:ℕ):ZMod (g*(n+2))) at h
    rw [h]
    conv_lhs => rw [←ZMod.natCast_zmod_val X]
    rw [←Nat.cast_add,ZMod.val_natCast]
  have hxpos : 0<X.val := by exact Nat.pos_of_ne_zero (fun h=>hi0 ((ZMod.val_eq_zero _).mp h))
  have hypos : 0<Y.val := by exact Nat.pos_of_ne_zero (fun h=>hj0 ((ZMod.val_eq_zero _).mp h))
  have hzpos : 0<Z.val := by exact Nat.pos_of_ne_zero (fun h=>hw0 ((ZMod.val_eq_zero _).mp h))
  have hd : 0<g*δ := Nat.mul_pos (NeZero.pos g) hδ
  have hb : X.val≠g*(n+2)-g*δ := by
    intro h
    have he : X.val+g*δ=g*(n+2) := by omega
    rw [hz,he,Nat.mod_self] at hzpos
    omega
  have ht:=paired_arithmetic (g*(n+2)) r (g*δ) X.val Y.val Z.val hr hd (by omega)
    hxpos (ZMod.val_lt X) hypos (ZMod.val_lt Y) hxy hz hb
  have hij : point n r δ a hfix hc i hi0≠point n r δ a hfix hc j hj0 := by
    intro h
    have h:=congrArg Fin.val (point_injective n r δ a hfix hc i j hi0 hj0 h)
    omega
  have hjw : point n r δ a hfix hc j hj0≠point n r δ a hfix hc w hw0 := by
    intro h
    have h:=congrArg Fin.val (point_injective n r δ a hfix hc j w hj0 hw0 h)
    omega
  have hEven:=edge_bound_of_sums (cap:=cap) (by omega : r<p) hpm
    (point n r δ a hfix hc i hi0) (point n r δ a hfix hc j hj0) hif hjf hij
    (decide (X.val<r)) (by simpa only [physical_point,decide_eq_true_eq] using ht.2.1)
  have hOdd:=edge_bound_of_sums_second (cap:=cap) (by omega : r<p) hpm
    (point n r δ a hfix hc j hj0) (point n r δ a hfix hc w hw0) hjf hwf hjw
    (decide (X.val<r ∨ g*(n+2)-g*δ<X.val))
    (by simpa only [physical_point,decide_eq_true_eq,hp,Nat.add_assoc] using ht.2.2)
  rw [←hx]
  have hMask (hei : ¬endpoint n i) (hej : ¬endpoint n j) (v : Fin (cap+1)) :
      decide (Domain r p cap (point n r δ a hfix hc i hi0) v.val)=
        ReflectionThresholdWord.mask cap (letter (g*(n+2)) r (g*δ) X.val) v ∧
      decide (Domain r p cap (point n r δ a hfix hc j hj0) v.val)=
        ReflectionThresholdWord.mask cap (letter (g*(n+2)) r (g*δ) X.val) v := by
    rw [interior_mask n r p δ cap hp hpm a hfix hc i hi0 hei hif v,
      interior_mask n r p δ cap hp hpm a hfix hc j hj0 hej hjf v]
    constructor
    · rfl
    · change ReflectionThresholdWord.mask cap (letter (g*(n+2)) r (g*δ) Y.val) v=
        ReflectionThresholdWord.mask cap (letter (g*(n+2)) r (g*δ) X.val) v
      unfold ReflectionThresholdWord.mask letter
      have he : Y.val<r ↔ X.val<r := ht.1
      by_cases hx : X.val<r
      · have hy:=he.mpr hx
        simp [hx,hy]
      · have hy : ¬Y.val<r := fun h=>hx (he.mp h)
        by_cases hxM : X.val<g*(n+2)-g*δ <;>
          by_cases hyM : Y.val<g*(n+2)-g*δ <;> simp [hx,hy,hxM,hyM]
  refine ⟨?_,?_,hMask⟩
  · by_cases h : X.val<r <;> by_cases hm : X.val<g*(n+2)-g*δ <;>
      simpa [evenBound,letter,h,hm] using hEven
  · by_cases h : X.val<r
    · simpa [oddBound,letter,h] using hOdd
    · by_cases hm : X.val<g*(n+2)-g*δ
      · have hn : ¬g*(n+2)-g*δ<X.val := by omega
        simpa [oddBound,letter,h,hm,hn] using hOdd
      · have hn : g*(n+2)-g*δ<X.val := by omega
        simpa [oddBound,letter,h,hm,hn] using hOdd

#print axioms aligned_source_letter
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionFixedSourceWindow
