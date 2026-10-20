import Results.Genus.CapFourMass.SignedReflectionPairedSource
import Results.Genus.RawGraph.PackedAcceptance.CompressedSignature

/-! Exact threshold letters for original nonzero paired cycles. Every letter
contains both vertex masks and both outgoing edges, including the closing edge.
No per-vertex signature certificate is assumed. -/
namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord
open SourceModel ReflectionPairedOrbit
open CapFourMass.SignedReflectionPaired

variable {g : ℕ} [NeZero g]

lemma no_self_pair (n r p δ : ℕ) (hp : p=r+g*δ)
    (a : Fin g) (hpair : a≠mate r a) (x : PairedCosets (L:=n+2) r a) :
    ¬(x.val+x.val=(r:ZMod (g*(n+2))) ∨
      x.val+x.val=(p:ZMod (g*(n+2)))) := by
  have hn : reduce g (n+2) (x.val+x.val)≠(r:ZMod g) := by
    rcases x.property with hx|hx
    · exact same_coset_sum_ne r a hpair x.val x.val hx hx
    · exact same_coset_sum_ne r (mate r a) (mate_ne r a hpair) x.val x.val hx hx
  rintro (h|h)
  · exact hn (by rw [h,map_natCast])
  · apply hn
    rw [h,map_natCast,hp,Nat.cast_add,Nat.cast_mul,ZMod.natCast_self,zero_mul,add_zero]

lemma vertex_no_loops (n r p δ : ℕ) (hp : p=r+g*δ)
    (a : Fin g) (ha : a≤mate r a) (ha0 : a≠0) (hpair : a≠mate r a)
    (x : PairedCosets (L:=n+2) r a) :
    ¬StrongLoop r p (vertex n r p δ hp a ha ha0 x).val ∧
    ¬CarryLoop r p (vertex n r p δ hp a ha ha0 x).val := by
  have hn:=no_self_pair n r p δ hp a hpair x
  have hs (t : ℕ) (ht : 2*x.val.val=t ∨ 2*x.val.val=g*(n+2)+t) :
      x.val+x.val=(t:ZMod (g*(n+2))) := by
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
    (a : Fin g) (ha : a≤mate r a) (ha0 : a≠0) (hpair : a≠mate r a)
    (x : PairedCosets (L:=n+2) r a) (v : ℕ) :
    Domain r p cap (vertex n r p δ hp a ha ha0 x).val v ↔
      1≤v ∧ v≤(if x.val.val<r then cap else cap-1) := by
  have hl:=vertex_no_loops n r p δ hp a ha ha0 hpair x
  have hf:=(vertex n r p δ hp a ha ha0 x).property
  have hn : ¬IsPivot r p (vertex n r p δ hp a ha ha0 x).val := hf
  simp [Domain,IsFree,hn,lower,hl.1,hl.2,upper,physical_vertex]

/-- There are exactly three paired transfer letters. -/
inductive Letter where
  | fullStrong
  | carryCarry
  | carryStrong
  deriving DecidableEq, Repr

def letter (M r d x : ℕ) : Letter :=
  if x<r then .fullStrong else if x<M-d then .carryCarry else .carryStrong

def mask (cap : ℕ) (q : Letter) (v : Fin (cap+1)) : Bool :=
  decide (1≤v.val ∧ v.val≤(if q=.fullStrong then cap else cap-1))

def evenBound (cap : ℕ) (q : Letter) : ℕ :=
  if q=.fullStrong then cap else cap-1

def oddBound (cap : ℕ) (q : Letter) : ℕ :=
  if q=.carryCarry then cap-1 else cap

/-- Exact representative arithmetic, including a wrap on the last edge. -/
lemma paired_arithmetic (M r d x y z : ℕ) (hr : 0<r) (hd : 0<d)
    (hp : r+d<M) (hx : 0<x) (hxm : x<M) (hy : 0<y) (hym : y<M)
    (hxy : x+y=r ∨ x+y=M+r) (hz : z=(x+d)%M)
    (hboundary : x≠M-d) :
    (y<r ↔ x<r) ∧
    (x+y=if x<r then r else M+r) ∧
    (y+z=if x<r ∨ M-d<x then r+d else M+r+d) := by
  have hm : 0<M := by omega
  by_cases hxr : x<r
  · have hxy' : x+y=r := by omega
    have hxd : x+d<M := by omega
    rw [hz,Nat.mod_eq_of_lt hxd]
    simp only [hxr,true_or,↓reduceIte,iff_true]
    omega
  · have hxy' : x+y=M+r := by omega
    by_cases hxd : x+d<M
    · rw [hz,Nat.mod_eq_of_lt hxd]
      have ht : ¬M-d<x := by omega
      simp only [hxr,ht,false_or,↓reduceIte,iff_false]
      omega
    · have ht : M-d<x := by omega
      have hmod : (x+d)%M=x+d-M := by
        rw [Nat.mod_eq_sub_mod (by omega : M≤x+d),Nat.mod_eq_of_lt (by omega : x+d-M<M)]
      rw [hz,hmod]
      simp only [hxr,ht,false_or,↓reduceIte,iff_false]
      omega

#print axioms vertex_domain
#print axioms paired_arithmetic
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord
