import Results.Genus.RawGraph.PackedAcceptance.ReflectionPairedLetters
import Results.Genus.CapFourMass.SignedReflectionFreeBlock

namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionFreeThreshold
open SourceModel ReflectionPairedOrbit ReflectionThresholdWord
open CapFourMass.SignedReflectionFreeBlock
variable {g : ℕ} [NeZero g]

lemma vertex_no_loops (n r p δ : ℕ) (hp : p=r+g*δ)
    (a : Fin g) (hpair : a≠mate r a)
    (x : FreeResidue n r p a) :
    ¬StrongLoop r p (vertex n r p a x).val ∧
    ¬CarryLoop r p (vertex n r p a x).val := by
  have hn:=ReflectionThresholdWord.no_self_pair n r p δ hp a hpair x.val
  have hs (t : ℕ) (ht : 2*x.val.val.val=t ∨ 2*x.val.val.val=g*(n+2)+t) :
      x.val.val+x.val.val=(t:ZMod (g*(n+2))) := by
    rcases ht with ht|ht
    · have hh:=congrArg (fun q:ℕ=>(q:ZMod (g*(n+2)))) ht
      rw [Nat.cast_mul,Nat.cast_ofNat,ZMod.natCast_zmod_val,two_mul] at hh
      exact hh
    · have hh:=congrArg (fun q:ℕ=>(q:ZMod (g*(n+2)))) ht
      rw [Nat.cast_add,ZMod.natCast_self,zero_add,Nat.cast_mul,Nat.cast_ofNat,
        ZMod.natCast_zmod_val,two_mul] at hh
      exact hh
  simp only [StrongLoop,CarryLoop,physical_vertex]
  constructor
  · rintro (h|h)
    · exact hn (Or.inl (hs r (Or.inl h)))
    · exact hn (Or.inr (hs p (Or.inl h)))
  · rintro (h|h)
    · exact hn (Or.inl (hs r (Or.inr h)))
    · exact hn (Or.inr (hs p (Or.inr h)))

/-- The original source domain reduces uniformly to one threshold cut. -/
theorem vertex_domain (n r p δ cap : ℕ) (hp : p=r+g*δ)
    (a : Fin g) (hpair : a≠mate r a)
    (x : FreeResidue n r p a) (v : ℕ) :
    Domain r p cap (vertex n r p a x).val v ↔
      1≤v ∧ v≤(if x.val.val.val<r then cap else cap-1) := by
  have hl:=vertex_no_loops n r p δ hp a hpair x
  have hf:=(vertex n r p a x).property
  have hn : ¬IsPivot r p (vertex n r p a x).val := hf
  simp [Domain,IsFree,hn,lower,hl.1,hl.2,upper,physical_vertex]


/-- A legal free three-vertex window preserves both masks and both edge phases.
The return-to-zero boundary is excluded by the retained next vertex itself. -/
theorem source_letter (n r p δ cap : ℕ) (hr : 0<r) (hδ : 0<δ)
    (hp : p=r+g*δ) (hpm : p<g*(n+2)) (a : Fin g) (hpair : a≠mate r a)
    (U V W : FreeResidue n r p a)
    (hxy : U.val.val.val+V.val.val.val=r ∨ U.val.val.val+V.val.val.val=g*(n+2)+r)
    (hz : W.val.val.val=(U.val.val.val+g*δ)%(g*(n+2)))
    (hUV : (vertex n r p a U).val≠(vertex n r p a V).val)
    (hVW : (vertex n r p a V).val≠(vertex n r p a W).val) :
    let q:=letter (g*(n+2)) r (g*δ) U.val.val.val
    (∀i : Fin (cap+1),decide (Domain r p cap (vertex n r p a U).val i.val)=mask cap q i ∧
      decide (Domain r p cap (vertex n r p a V).val i.val)=mask cap q i) ∧
    edgeBound r p cap (vertex n r p a U).val (vertex n r p a V).val=evenBound cap q ∧
    edgeBound r p cap (vertex n r p a V).val (vertex n r p a W).val=oddBound cap q := by
  dsimp only
  have hb : U.val.val.val≠g*(n+2)-g*δ := by
    intro he
    have hw := val_pos n r p a W
    have hdlt : g*δ<g*(n+2) := by omega
    have he' : U.val.val.val+g*δ=g*(n+2) := by omega
    rw [hz,he',Nat.mod_self] at hw
    omega
  have hd : 0<g*δ := Nat.mul_pos (NeZero.pos g) hδ
  have hp' : r+g*δ<g*(n+2) := by omega
  have ht := paired_arithmetic (g*(n+2)) r (g*δ) U.val.val.val V.val.val.val W.val.val.val
    hr hd hp' (val_pos n r p a U) (ZMod.val_lt U.val.val)
    (val_pos n r p a V) (ZMod.val_lt V.val.val) hxy hz hb
  have hEven := edge_bound_of_sums (cap:=cap) (by omega : r<p) hpm
    (vertex n r p a U).val (vertex n r p a V).val
    (vertex n r p a U).property (vertex n r p a V).property
    hUV (decide (U.val.val.val<r)) (by simpa only [physical_vertex,decide_eq_true_eq] using ht.2.1)
  have hOdd := edge_bound_of_sums_second (cap:=cap) (by omega : r<p) hpm
    (vertex n r p a V).val (vertex n r p a W).val
    (vertex n r p a V).property (vertex n r p a W).property
    hVW (decide (U.val.val.val<r ∨ g*(n+2)-g*δ<U.val.val.val))
    (by simpa only [physical_vertex,decide_eq_true_eq,hp,Nat.add_assoc] using ht.2.2)
  change (∀i : Fin (cap+1), decide (Domain r p cap (vertex n r p a U).val i.val)=_ ∧
    decide (Domain r p cap (vertex n r p a V).val i.val)=_) ∧ _
  by_cases hl : U.val.val.val<r
  · have hv : V.val.val.val<r := ht.1.mpr hl
    simp only [letter,hl,↓reduceIte]
    refine ⟨?_,?_,?_⟩
    · intro i
      simp [vertex_domain n r p δ cap hp a hpair U,
        vertex_domain n r p δ cap hp a hpair V,mask,hl,hv]
    · simpa only [evenBound,↓reduceIte,decide_eq_true_eq,hl] using hEven
    · simpa [oddBound,hl] using hOdd
  · have hv : ¬V.val.val.val<r := fun h=>hl (ht.1.mp h)
    by_cases hm : U.val.val.val<g*(n+2)-g*δ
    · have hn : ¬g*(n+2)-g*δ<U.val.val.val := by omega
      simp only [letter,hl,hm,↓reduceIte]
      refine ⟨?_,?_,?_⟩
      · intro i
        simp [vertex_domain n r p δ cap hp a hpair U,
          vertex_domain n r p δ cap hp a hpair V,mask,hl,hv]
      · simpa [evenBound,decide_eq_true_eq,hl] using hEven
      · simpa [oddBound,decide_eq_true_eq,hl,hn] using hOdd
    · have hn : g*(n+2)-g*δ<U.val.val.val := by omega
      simp only [letter,hl,hm,↓reduceIte]
      refine ⟨?_,?_,?_⟩
      · intro i
        simp [vertex_domain n r p δ cap hp a hpair U,
          vertex_domain n r p δ cap hp a hpair V,mask,hl,hv]
      · simpa [evenBound,decide_eq_true_eq,hl] using hEven
      · simpa [oddBound,decide_eq_true_eq,hl,hn] using hOdd

#print axioms vertex_no_loops
#print axioms vertex_domain
#print axioms source_letter
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionFreeThreshold
