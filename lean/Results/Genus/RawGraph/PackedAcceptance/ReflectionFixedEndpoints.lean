import Results.Genus.RawGraph.PackedAcceptance.ReflectionFixedPhase

/-! In the full fixed-reflection path the only unary self-pairs are the two
original endpoints. This does not equate their strong and carried masks. -/
namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionFixedPhase
open ReflectionCoset ReflectionConsecutive ReflectionFixedOrbit

lemma self_pair_iff_endpoint_of_path {A : Type*} [AddCommGroup A]
    (n : ℕ) (f : Fin (n+2)→A) (hf : Function.Injective f) (r p : A) (hrp : r≠p)
    (hedge : ∀i j,i.val+1=j.val→f i+f j=r ∨ f i+f j=p)
    (hcover : ∀i j,i≠j→(f i+f j=r ∨ f i+f j=p)→i.val+1=j.val ∨ j.val+1=i.val)
    (hpartner : ∀i,(∃j,f i+f j=r) ∧ (∃j,f i+f j=p)) (i : Fin (n+2)) :
    (f i+f i=r ∨ f i+f i=p) ↔ i.val=0 ∨ i.val=n+1 := by
  have unique {x y z : Fin (n+2)} {t : A} (hy : f x+f y=t) (hz : f x+f z=t) : y=z :=
    hf (add_left_cancel (hy.trans hz.symm))
  constructor
  · intro hs
    by_contra hn
    have hi0 : 0 < (i : ℕ) := by omega
    have hil : i.val<n+1 := by have:=i.isLt;omega
    let j : Fin (n+2) := ⟨i.val-1,by omega⟩
    let k : Fin (n+2) := ⟨i.val+1,by omega⟩
    have hji : j.val+1=i.val := by dsimp [j];omega
    have hik : i.val+1=k.val := rfl
    have hji_ne : j≠i := by intro h;have:=congrArg Fin.val h;dsimp [j] at this;omega
    have hki_ne : k≠i := by intro h;have:=congrArg Fin.val h;dsimp [k] at this;omega
    have hjk_ne : j≠k := by intro h;have:=congrArg Fin.val h;dsimp [j,k] at this;omega
    have hj := hedge j i hji
    rw [add_comm] at hj
    have hk := hedge i k hik
    rcases hs with hs|hs
    · have hjp : f i+f j=p := hj.resolve_left (fun h=>hji_ne (unique h hs))
      have hkp : f i+f k=p := hk.resolve_left (fun h=>hki_ne (unique h hs))
      exact hjk_ne (unique hjp hkp)
    · have hjr : f i+f j=r := hj.resolve_right (fun h=>hji_ne (unique h hs))
      have hkr : f i+f k=r := hk.resolve_right (fun h=>hki_ne (unique h hs))
      exact hjk_ne (unique hjr hkr)
  · intro he
    by_contra hs
    obtain ⟨⟨j,hj⟩,⟨k,hk⟩⟩:=hpartner i
    have hij : i≠j := by intro h;subst j;exact hs (Or.inl hj)
    have hik : i≠k := by intro h;subst k;exact hs (Or.inr hk)
    have hji:=hcover i j hij (Or.inl hj)
    have hki:=hcover i k hik (Or.inr hk)
    have hjk : j=k := Fin.ext (by rcases he with he|he <;> have:=j.isLt <;> have:=k.isLt <;> omega)
    subst k
    exact hrp (hj.symm.trans hk)

lemma phase_consecutive_sum (n : ℕ) (t : ZMod (n+2)) (u : (ZMod (n+2))ˣ)
    (i j : Fin (n+2)) (hij : i.val+1=j.val) :
    phaseOrder n t u i+phaseOrder n t u j=
      if i.val%2=(normalizedTarget n t u).val%2 then t+(u:ZMod (n+2)) else t := by
  rw [phaseOrder_apply,phaseOrder_apply,←mul_add,consecutive_sum (n+1) _ i j hij]
  split_ifs
  · exact normalizedTarget_next n t u
  · exact normalizedTarget_value n t u

/-- Uniform endpoint characterization, including path size two. -/
theorem phase_self_pair_iff_endpoint (n : ℕ) (t : ZMod (n+2)) (u : (ZMod (n+2))ˣ)
    (i : Fin (n+2)) :
    (phaseOrder n t u i+phaseOrder n t u i=t ∨
      phaseOrder n t u i+phaseOrder n t u i=t+(u:ZMod (n+2))) ↔
      i.val=0 ∨ i.val=n+1 := by
  letI : Fact (1<n+2) := ⟨by omega⟩
  apply self_pair_iff_endpoint_of_path n (phaseOrder n t u) (phaseOrder n t u).injective
    t (t+(u:ZMod (n+2)))
  · intro h
    have hu : (u:ZMod (n+2))=0 := by linear_combination -h
    exact u.ne_zero hu
  · intro j k hjk
    rw [phase_consecutive_sum n t u j k hjk]
    split_ifs <;> simp
  · exact phaseOrder_adjacent n t u
  · intro j
    constructor
    · exact ⟨(phaseOrder n t u).symm (t-phaseOrder n t u j),by rw [Equiv.apply_symm_apply];ring⟩
    · exact ⟨(phaseOrder n t u).symm (t+(u:ZMod (n+2))-phaseOrder n t u j),by rw [Equiv.apply_symm_apply];ring⟩

variable {g : ℕ} [NeZero g]

/-- The only original reflection self-pairs are the full path endpoints.
Their integer strong/carried alternatives are deliberately not identified. -/
theorem source_self_pair_iff_endpoint (n : ℕ) (a : Fin g) (r p : ZMod (g*(n+2)))
    (hfix : (r-affineValue a (0:ZMod (n+2))).val%g=a.val) (u : (ZMod (n+2))ˣ)
    (hgap : scaleHom g (n+2) (u:ZMod (n+2))=p-r) (i : Fin (n+2)) :
    ((order n a r hfix u i).val+(order n a r hfix u i).val=r ∨
      (order n a r hfix u i).val+(order n a r hfix u i).val=p) ↔
      i.val=0 ∨ i.val=n+1 := by
  have ht:=target_value n a r hfix
  have hp : affineValue a (target n a r hfix+(u:ZMod (n+2)))=
      p-affineValue a (0:ZMod (n+2)) := by
    rw [affineValue_add,ht,hgap];ring
  rw [order_val,affineValue_pair_iff a r _ _ _ ht,affineValue_pair_iff a p _ _ _ hp]
  exact phase_self_pair_iff_endpoint n (target n a r hfix) u i

#print axioms phase_consecutive_sum
#print axioms phase_self_pair_iff_endpoint
#print axioms source_self_pair_iff_endpoint
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionFixedPhase
