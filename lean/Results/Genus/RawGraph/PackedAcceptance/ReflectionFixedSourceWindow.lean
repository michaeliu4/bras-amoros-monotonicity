import Results.Genus.RawGraph.PackedAcceptance.ReflectionFixedEndpoints
import Results.Genus.RawGraph.PackedAcceptance.ReflectionPairedLetters
import Results.Genus.RawGraph.PackedAcceptance.ReflectionChunkWord

/-! Original fixed-path source fields indexed by full-path positions. Windows
keep the original parity, endpoint loop tests, and pivot singleton masks. -/
namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionFixedSourceWindow
open SourceModel ReflectionCoset ReflectionFixedOrbit ReflectionComponentOrders
open ReflectionFixedPhase ReflectionThresholdWord

variable {g : ℕ} [NeZero g]

abbrev residue (n r δ : ℕ) (a : Fin g) (hfix : a=ReflectionPairedOrbit.mate r a)
    (hc : Nat.Coprime δ (n+2)) (i : Fin (n+2)) : ZMod (g*(n+2)) :=
  (order n a r (fixed_origin n r a hfix) (gapUnit n δ hc) i).val

def point (n r δ : ℕ) (a : Fin g) (hfix : a=ReflectionPairedOrbit.mate r a)
    (hc : Nat.Coprime δ (n+2)) (i : Fin (n+2)) (hi : residue n r δ a hfix hc i≠0) :
    Fin (g*(n+2)-1) :=
  ⟨(residue n r δ a hfix hc i).val-1,by
    have hv:=ZMod.val_lt (residue n r δ a hfix hc i)
    have hz : 0<(residue n r δ a hfix hc i).val := by
      by_contra hn
      have he : (residue n r δ a hfix hc i).val=0 := by omega
      exact hi ((ZMod.val_eq_zero _).mp he)
    omega⟩

lemma physical_point (n r δ : ℕ) (a : Fin g) (hfix : a=ReflectionPairedOrbit.mate r a)
    (hc : Nat.Coprime δ (n+2)) (i : Fin (n+2)) (hi : residue n r δ a hfix hc i≠0) :
    physical (point n r δ a hfix hc i hi)=(residue n r δ a hfix hc i).val := by
  have hz : 0<(residue n r δ a hfix hc i).val := by
    by_contra hn
    exact hi ((ZMod.val_eq_zero _).mp (by omega))
  change (residue n r δ a hfix hc i).val-1+1=_
  omega

lemma point_injective (n r δ : ℕ) (a : Fin g) (hfix : a=ReflectionPairedOrbit.mate r a)
    (hc : Nat.Coprime δ (n+2)) (i j : Fin (n+2))
    (hi : residue n r δ a hfix hc i≠0) (hj : residue n r δ a hfix hc j≠0)
    (he : point n r δ a hfix hc i hi=point n r δ a hfix hc j hj) : i=j := by
  have hv:=congrArg physical he
  rw [physical_point,physical_point] at hv
  apply (order n a r (fixed_origin n r a hfix) (gapUnit n δ hc)).injective
  apply Subtype.ext
  exact ZMod.val_injective _ hv

/-- A source-indexed endpoint predicate; it is not relative to a window. -/
def endpoint (n : ℕ) (i : Fin (n+2)) : Prop := i.val=0 ∨ i.val=n+1
instance (n : ℕ) (i : Fin (n+2)) : Decidable (endpoint n i) := inferInstanceAs (Decidable (_ ∨ _))

lemma no_loops_interior (n r p δ : ℕ) (hp : p=r+g*δ) (hpm : p<g*(n+2))
    (a : Fin g) (hfix : a=ReflectionPairedOrbit.mate r a) (hc : Nat.Coprime δ (n+2))
    (i : Fin (n+2)) (hi : residue n r δ a hfix hc i≠0) (he : ¬endpoint n i) :
    ¬StrongLoop r p (point n r δ a hfix hc i hi) ∧
    ¬CarryLoop r p (point n r δ a hfix hc i hi) := by
  have hs : ¬(residue n r δ a hfix hc i+residue n r δ a hfix hc i=(r:ZMod (g*(n+2))) ∨
      residue n r δ a hfix hc i+residue n r δ a hfix hc i=(p:ZMod (g*(n+2)))) := by
    intro h
    exact he ((source_self_pair_iff_endpoint n a r p (fixed_origin n r a hfix)
      (gapUnit n δ hc) (gap_value n r p δ hc hp) i).mp h)
  have hcast (t : ℕ) (ht : 2*(residue n r δ a hfix hc i).val=t ∨
      2*(residue n r δ a hfix hc i).val=g*(n+2)+t) :
      residue n r δ a hfix hc i+residue n r δ a hfix hc i=(t:ZMod (g*(n+2))) := by
    rcases ht with ht|ht
    · have h:=congrArg (fun x:ℕ=>(x:ZMod (g*(n+2)))) ht
      rw [Nat.cast_mul,Nat.cast_ofNat,ZMod.natCast_zmod_val,two_mul] at h
      exact h
    · have h:=congrArg (fun x:ℕ=>(x:ZMod (g*(n+2)))) ht
      rw [Nat.cast_add,ZMod.natCast_self,zero_add,Nat.cast_mul,Nat.cast_ofNat,
        ZMod.natCast_zmod_val,two_mul] at h
      exact h
  simp only [StrongLoop,CarryLoop,physical_point]
  constructor
  · rintro (h|h)
    · exact hs (Or.inl (hcast r (Or.inl h)))
    · exact hs (Or.inr (hcast p (Or.inl h)))
  · rintro (h|h)
    · exact hs (Or.inl (hcast r (Or.inr h)))
    · exact hs (Or.inr (hcast p (Or.inr h)))

/-- Full unary mask: pivot singleton first, then original endpoint loop lower
bounds, and finally the physical threshold upper bound. -/
def mask (M r p cap x : ℕ) (isEndpoint : Bool) (v : Fin (cap+1)) : Bool :=
  if x=r ∨ x=p then decide (v.val=cap)
  else decide ((if isEndpoint then
      max 1 (max (if 2*x=r ∨ 2*x=p then (cap+1)/2 else 1)
        (if 2*x=M+r ∨ 2*x=M+p then (cap-1+1)/2 else 1)) else 1)≤v.val ∧
      v.val≤(if x<r then cap else cap-1))

/-- Uniform source-field equality for every nonzero fixed-order position,
including either retained pivot in the zero coset. -/
theorem domain_mask (n r p δ cap : ℕ) (hp : p=r+g*δ) (hpm : p<g*(n+2))
    (a : Fin g) (hfix : a=ReflectionPairedOrbit.mate r a) (hc : Nat.Coprime δ (n+2))
    (i : Fin (n+2)) (hi : residue n r δ a hfix hc i≠0) (v : Fin (cap+1)) :
    decide (Domain r p cap (point n r δ a hfix hc i hi) v.val)=
      mask (g*(n+2)) r p cap (residue n r δ a hfix hc i).val (decide (endpoint n i)) v := by
  by_cases hpiv : IsPivot r p (point n r δ a hfix hc i hi)
  · have hx : (residue n r δ a hfix hc i).val=r ∨ (residue n r δ a hfix hc i).val=p := by
      simpa only [IsPivot,physical_point] using hpiv
    simp [Domain,IsFree,hpiv,mask,hx]
  · have hx : ¬((residue n r δ a hfix hc i).val=r ∨ (residue n r δ a hfix hc i).val=p) := by
      simpa only [IsPivot,physical_point] using hpiv
    by_cases he : endpoint n i
    · simp [Domain,IsFree,hpiv,lower,upper,StrongLoop,CarryLoop,physical_point,mask,hx,he]
    · have hl:=no_loops_interior n r p δ hp hpm a hfix hc i hi he
      simp [Domain,IsFree,hpiv,lower,upper,hl.1,hl.2,physical_point,mask,hx,he]

/-- Interior nonpivot domains are precisely the old three-letter mask. -/
theorem interior_mask (n r p δ cap : ℕ) (hp : p=r+g*δ) (hpm : p<g*(n+2))
    (a : Fin g) (hfix : a=ReflectionPairedOrbit.mate r a) (hc : Nat.Coprime δ (n+2))
    (i : Fin (n+2)) (hi : residue n r δ a hfix hc i≠0) (he : ¬endpoint n i)
    (hf : IsFree r p (point n r δ a hfix hc i hi)) (v : Fin (cap+1)) :
    decide (Domain r p cap (point n r δ a hfix hc i hi) v.val)=
      ReflectionThresholdWord.mask cap (letter (g*(n+2)) r (g*δ)
        (residue n r δ a hfix hc i).val) v := by
  have hl:=no_loops_interior n r p δ hp hpm a hfix hc i hi he
  have hn : ¬IsPivot r p (point n r δ a hfix hc i hi) := hf
  simp only [Domain,IsFree,hn,false_implies,true_implies,true_and,lower,hl.1,hl.2,
    ↓reduceIte,max_self,upper,physical_point]
  by_cases hx : (residue n r δ a hfix hc i).val<r
  · simp [ReflectionThresholdWord.mask,letter,hx]
  · by_cases hy : (residue n r δ a hfix hc i).val<g*(n+2)-g*δ
    · simp [ReflectionThresholdWord.mask,letter,hx,hy]
    · simp [ReflectionThresholdWord.mask,letter,hx,hy]

/-- The exact shifted-prefix alphabet consumed by future ordered slice
compression. Endpoint overrides and unpaired vertices are separate fields. -/
def pairWord (n r δ : ℕ) (a : Fin g) (hfix : a=ReflectionPairedOrbit.mate r a)
    (hc : Nat.Coprime δ (n+2)) (N : ℕ) : List Letter :=
  (List.range N).map (fun k=>letter (g*(n+2)) r (g*δ)
    (a.val+g*((startPhase n δ (targetIndex n r δ a hfix hc)+δ*k)%(n+2))))

theorem pairWord_reduced (n r δ : ℕ) (a : Fin g) (hfix : a=ReflectionPairedOrbit.mate r a)
    (hc : Nat.Coprime δ (n+2)) (N : ℕ) :
    pairWord n r δ a hfix hc N=
      (List.range N).map (fun k=>reducedLetter (n+2) δ (cut g a.val r)
        ((startPhase n δ (targetIndex n r δ a hfix hc)+δ*k)%(n+2))) := by
  apply List.map_congr_left
  intro k _
  exact affine_letter_reduced g (n+2) r δ a.val _ (NeZero.pos g) a.isLt

#print axioms domain_mask
#print axioms interior_mask
#print axioms pairWord_reduced
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionFixedSourceWindow
