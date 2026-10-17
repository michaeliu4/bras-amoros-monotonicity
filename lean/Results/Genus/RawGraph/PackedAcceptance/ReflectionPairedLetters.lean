import Results.Genus.RawGraph.PackedAcceptance.ReflectionThresholdWord

namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord
open SourceModel ReflectionPairedOrbit
open CapFourMass.SignedReflectionPaired

variable {g : ℕ} [NeZero g]

abbrev point (n r p δ : ℕ) (hp : p=r+g*δ)
    (hc : Nat.Coprime δ (n+2)) (a : Fin g) (ha : a≤mate r a) (ha0 : a≠0)
    (hpair : a≠mate r a) (j : Fin (2*(n+2))) :=
  vertex n r p δ hp a ha ha0 (canonicalOrder r a hpair δ hc j)

lemma edge_bound_of_sums {M r p cap : ℕ} (hrp : r<p) (hpm : p<M)
    (u v : Fin (M-1)) (hu : IsFree r p u) (hv : IsFree r p v) (hne : u≠v)
    (b : Bool) (hs : physical u+physical v=if b then r else M+r) :
    edgeBound r p cap u v=if b then cap else cap-1 := by
  change ¬IsPivot r p u at hu
  change ¬IsPivot r p v at hv
  cases b
  · simp only [Bool.false_eq_true,↓reduceIte] at hs ⊢
    have hsr : physical u+physical v≠r := by omega
    have hsp : physical u+physical v≠p := by omega
    simp only [edgeBound,hu,hv,hne,or_self,hsr,hsp,↓reduceIte]
    simp only [hs,or_true,true_or,↓reduceIte]
  · simp only [↓reduceIte] at hs ⊢
    simp [edgeBound,hu,hv,hne,hs]

lemma edge_bound_of_sums_second {M r p cap : ℕ} (hrp : r<p) (hpm : p<M)
    (u v : Fin (M-1)) (hu : IsFree r p u) (hv : IsFree r p v) (hne : u≠v)
    (b : Bool) (hs : physical u+physical v=if b then p else M+p) :
    edgeBound r p cap u v=if b then cap else cap-1 := by
  change ¬IsPivot r p u at hu
  change ¬IsPivot r p v at hv
  cases b
  · simp only [Bool.false_eq_true,↓reduceIte] at hs ⊢
    have hsr : physical u+physical v≠r := by omega
    have hsp : physical u+physical v≠p := by omega
    simp only [edgeBound,hu,hv,hne,or_self,hsr,hsp,↓reduceIte]
    simp only [hs,or_true,true_or,↓reduceIte]
  · simp only [↓reduceIte] at hs ⊢
    simp [edgeBound,hu,hv,hne,hs]

/-- Uniform actual-source masks and both thresholds for each pair. The `next`
index is modular, so the final odd edge is the original cycle closure. -/
theorem paired_source_letter (n r p δ cap : ℕ) (hr : 0<r) (hδ : 0<δ)
    (hp : p=r+g*δ) (hpm : p<g*(n+2)) (hc : Nat.Coprime δ (n+2))
    (a : Fin g) (ha : a≤mate r a) (ha0 : a≠0) (hpair : a≠mate r a)
    (k : Fin (n+2)) :
    let u := point n r p δ hp hc a ha ha0 hpair ((parityEquiv (n+2)).symm (false,k))
    let v := point n r p δ hp hc a ha ha0 hpair ((parityEquiv (n+2)).symm (true,k))
    let w := point n r p δ hp hc a ha ha0 hpair ((parityEquiv (n+2)).symm (false,next k))
    let q := letter (g*(n+2)) r (g*δ) (a.val+g*((δ*k.val)%(n+2)))
    (∀i : Fin (cap+1), decide (Domain r p cap u.val i.val)=mask cap q i ∧
      decide (Domain r p cap v.val i.val)=mask cap q i) ∧
    edgeBound r p cap u.val v.val=evenBound cap q ∧
    edgeBound r p cap v.val w.val=oddBound cap q := by
  dsimp only
  let E := canonicalOrder (L:=n+2) r a hpair δ hc
  let U := E ((parityEquiv (n+2)).symm (false,k))
  let V := E ((parityEquiv (n+2)).symm (true,k))
  let W := E ((parityEquiv (n+2)).symm (false,next k))
  have hu : U.val.val=a.val+g*((δ*k.val)%(n+2)) := canonicalOrder_even r a hpair δ hc k
  have hxy : U.val.val+V.val.val=r ∨ U.val.val+V.val.val=g*(n+2)+r := by
    have hs:=canonicalOrder_even_odd_sum r a hpair δ hc k
    have ht := (targetPair_iff_zmod (by omega : r<g*(n+2))
      (vertex n r p δ hp a ha ha0 U).val (vertex n r p δ hp a ha ha0 V).val).mpr
      (by simpa only [cast_physical_vertex] using hs)
    simpa only [TargetPair,physical_vertex] using ht
  have hz : W.val.val=(U.val.val+g*δ)%(g*(n+2)) := by
    have hs : W.val=U.val+((g*δ:ℕ):ZMod (g*(n+2))) := by
      dsimp only [W,U,E,canonicalOrder]
      rw [order_even,order_even,orbit_next]
    calc
      W.val.val=(U.val+((g*δ:ℕ):ZMod (g*(n+2)))).val := congrArg ZMod.val hs
      _=_ := by
        conv_lhs => rw [←ZMod.natCast_zmod_val U.val]
        rw [←Nat.cast_add,ZMod.val_natCast]
  have hb : U.val.val≠g*(n+2)-g*δ := by
    intro he
    have hw := paired_val_pos n r a ha ha0 W
    have hdlt : g*δ<g*(n+2) := by omega
    have he' : U.val.val+g*δ=g*(n+2) := by omega
    rw [hz,he',Nat.mod_self] at hw
    omega
  have hd : 0<g*δ := Nat.mul_pos (NeZero.pos g) hδ
  have hp' : r+g*δ<g*(n+2) := by omega
  have ht := paired_arithmetic (g*(n+2)) r (g*δ) U.val.val V.val.val W.val.val
    hr hd hp' (paired_val_pos n r a ha ha0 U) (ZMod.val_lt U.val)
    (paired_val_pos n r a ha ha0 V) (ZMod.val_lt V.val) hxy hz hb
  have hUV : (vertex n r p δ hp a ha ha0 U).val≠(vertex n r p δ hp a ha ha0 V).val := by
    intro he
    have h:=E.injective (vertex_injective n r p δ hp a ha ha0 (Subtype.ext he))
    have hv:=congrArg Fin.val h
    simp only [parityEquiv_symm_even,parityEquiv_symm_odd] at hv
    omega
  have hVW : (vertex n r p δ hp a ha ha0 V).val≠(vertex n r p δ hp a ha ha0 W).val := by
    intro he
    have h:=E.injective (vertex_injective n r p δ hp a ha ha0 (Subtype.ext he))
    have hv:=congrArg Fin.val h
    simp only [parityEquiv_symm_even,parityEquiv_symm_odd] at hv
    omega
  have hEven := edge_bound_of_sums (cap:=cap) (by omega : r<p) hpm
    (vertex n r p δ hp a ha ha0 U).val (vertex n r p δ hp a ha ha0 V).val
    (vertex n r p δ hp a ha ha0 U).property (vertex n r p δ hp a ha ha0 V).property
    hUV (decide (U.val.val<r)) (by simpa only [physical_vertex,decide_eq_true_eq] using ht.2.1)
  have hOdd := edge_bound_of_sums_second (cap:=cap) (by omega : r<p) hpm
    (vertex n r p δ hp a ha ha0 V).val (vertex n r p δ hp a ha ha0 W).val
    (vertex n r p δ hp a ha ha0 V).property (vertex n r p δ hp a ha ha0 W).property
    hVW (decide (U.val.val<r ∨ g*(n+2)-g*δ<U.val.val))
    (by simpa only [physical_vertex,decide_eq_true_eq,hp,Nat.add_assoc] using ht.2.2)
  change (∀i : Fin (cap+1), decide (Domain r p cap (vertex n r p δ hp a ha ha0 U).val i.val)=_ ∧
    decide (Domain r p cap (vertex n r p δ hp a ha ha0 V).val i.val)=_) ∧ _
  rw [←hu]
  by_cases hl : U.val.val<r
  · have hv : V.val.val<r := ht.1.mpr hl
    simp only [letter,hl,↓reduceIte]
    refine ⟨?_,?_,?_⟩
    · intro i
      simp [vertex_domain n r p δ cap hp a ha ha0 hpair U,
        vertex_domain n r p δ cap hp a ha ha0 hpair V,mask,hl,hv]
    · simpa only [evenBound,↓reduceIte,decide_eq_true_eq,hl] using hEven
    · simpa [oddBound,hl] using hOdd
  · have hv : ¬V.val.val<r := fun h=>hl (ht.1.mp h)
    by_cases hm : U.val.val<g*(n+2)-g*δ
    · have hn : ¬g*(n+2)-g*δ<U.val.val := by omega
      simp only [letter,hl,hm,↓reduceIte]
      refine ⟨?_,?_,?_⟩
      · intro i
        simp [vertex_domain n r p δ cap hp a ha ha0 hpair U,
          vertex_domain n r p δ cap hp a ha ha0 hpair V,mask,hl,hv]
      · simpa [evenBound,decide_eq_true_eq,hl] using hEven
      · simpa [oddBound,decide_eq_true_eq,hl,hn] using hOdd
    · have hn : g*(n+2)-g*δ<U.val.val := by omega
      simp only [letter,hl,hm,↓reduceIte]
      refine ⟨?_,?_,?_⟩
      · intro i
        simp [vertex_domain n r p δ cap hp a ha ha0 hpair U,
          vertex_domain n r p δ cap hp a ha ha0 hpair V,mask,hl,hv]
      · simpa [evenBound,decide_eq_true_eq,hl] using hEven
      · simpa [oddBound,decide_eq_true_eq,hl,hn] using hOdd

#print axioms paired_source_letter
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord
