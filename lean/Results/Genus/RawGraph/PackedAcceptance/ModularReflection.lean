import Results.Genus.RawGraph.SourceModel
import Mathlib.Data.ZMod.Basic

/-! Source geometry for reusable full layouts. The two original ordinary/
carried target tests are exactly modular reflections; composing them is
translation by the original pivot gap. No layout family is assumed here. -/
namespace SubmittedGenus.RawGraph.PackedAcceptance
open SourceModel

lemma targetPair_iff_mod {m t : ℕ} (ht : t<m) (u v : Fin (m-1)) :
    TargetPair t u v ↔ (physical u+physical v)%m=t := by
  have hu := u.isLt
  have hv := v.isLt
  have hsum : physical u+physical v<2*m := by dsimp [physical]; omega
  unfold TargetPair
  constructor
  · rintro (h | h)
    · rw [h,Nat.mod_eq_of_lt ht]
    · rw [h,Nat.add_mod_left,Nat.mod_eq_of_lt ht]
  · intro h
    by_cases hs : physical u+physical v<m
    · exact Or.inl ((Nat.mod_eq_of_lt hs).symm.trans h)
    · right
      have hs' : physical u+physical v-m<m := by omega
      rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt hs'] at h
      omega

lemma targetPair_iff_zmod {m t : ℕ} (ht : t<m) (u v : Fin (m-1)) :
    TargetPair t u v ↔ (physical u:ZMod m)+(physical v:ZMod m)=(t:ZMod m) := by
  rw [targetPair_iff_mod ht]
  rw [←Nat.cast_add]
  constructor
  · intro h
    rw [←ZMod.natCast_mod (physical u+physical v) m,h]
  · intro h
    have hh := congrArg ZMod.val h
    simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt ht] using hh

def modularReflect {m : ℕ} (t x : ZMod m) : ZMod m := t-x

lemma modularReflect_involutive {m : ℕ} (t : ZMod m) :
    Function.Involutive (modularReflect t) := by
  intro x
  simp [modularReflect]

lemma modularReflect_comp {m : ℕ} (r p x : ZMod m) :
    modularReflect p (modularReflect r x)=x+(p-r) := by
  unfold modularReflect
  ring

/-- The source reflection partner is the original physical modular partner;
ordinary and carried edges have not been conflated with arbitrary pairs. -/
lemma targetPair_iff_modularReflect {m t : ℕ} (ht : t<m) (u v : Fin (m-1)) :
    TargetPair t u v ↔ (physical v:ZMod m)=modularReflect (t:ZMod m) (physical u) := by
  rw [targetPair_iff_zmod ht]
  simp only [modularReflect,eq_sub_iff_add_eq,add_comm]

/-- The pivot gap is the actual natural-number difference when r≤p. -/
lemma modularReflect_comp_gap {m r p : ℕ} (hrp : r≤p) (x : ZMod m) :
    modularReflect (p:ZMod m) (modularReflect (r:ZMod m) x)=x+((p-r:ℕ):ZMod m) := by
  rw [Nat.cast_sub hrp,modularReflect_comp]

/-- Two consecutive source reflections advance by the original pivot gap. -/
lemma targetPair_two_step {m r p : ℕ} (hr : r<m) (hp : p<m) (hrp : r≤p)
    (u v w : Fin (m-1)) (h₁ : TargetPair r u v) (h₂ : TargetPair p v w) :
    (physical w:ZMod m)=(physical u:ZMod m)+((p-r:ℕ):ZMod m) := by
  have hv := (targetPair_iff_modularReflect hr u v).mp h₁
  have hw := (targetPair_iff_modularReflect hp v w).mp h₂
  rw [hw,hv,modularReflect_comp_gap hrp]

/-- Iterating the two original reflections follows a translation orbit. -/
lemma modularReflect_pair_iterate {m : ℕ} (r p : ZMod m) (n : ℕ) (x : ZMod m) :
    ((fun y=>modularReflect p (modularReflect r y))^[n]) x=x+n*(p-r) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply,ih,modularReflect_comp]
    push_cast
    ring

/-- The complete two-reflection orbit closes after m/gcd(m,p-r) steps. -/
lemma modularReflect_pair_period {m r p : ℕ} (hm : m≠0) (hrp : r≤p) (x : ZMod m) :
    ((fun y=>modularReflect (p:ZMod m) (modularReflect (r:ZMod m) y))^[m/m.gcd (p-r)]) x=x := by
  rw [modularReflect_pair_iterate,←Nat.cast_sub hrp]
  have hz := addOrderOf_nsmul_eq_zero ((p-r:ℕ):ZMod m)
  rw [ZMod.addOrderOf_coe (p-r) hm,nsmul_eq_mul] at hz
  rw [hz,add_zero]

/-- No translation-orbit position is repeated before the proved period. -/
lemma modularTranslation_injective {m d : ℕ} (hm : m≠0) (x : ZMod m) :
    Function.Injective (fun k:Fin (m/m.gcd d)=>x+(k.val:ZMod m)*(d:ZMod m)) := by
  intro k l h
  apply Fin.ext
  have hh : k.val • (d:ZMod m)=l.val • (d:ZMod m) := by
    simpa only [nsmul_eq_mul] using add_left_cancel h
  exact nsmul_injOn_Iio_addOrderOf
    (by rw [ZMod.addOrderOf_coe d hm]; exact k.isLt)
    (by rw [ZMod.addOrderOf_coe d hm]; exact l.isLt) hh

#print axioms targetPair_iff_mod
#print axioms targetPair_iff_zmod
#print axioms modularReflect_comp
#print axioms targetPair_iff_modularReflect
#print axioms targetPair_two_step
#print axioms modularReflect_pair_iterate
#print axioms modularReflect_pair_period
#print axioms modularTranslation_injective
end SubmittedGenus.RawGraph.PackedAcceptance
