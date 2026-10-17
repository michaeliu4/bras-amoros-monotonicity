import Results.Genus.RawGraph.PackedAcceptance.CachedStepActionMod

/-! Semiring-independent cached components. The only outside-word factor is
an explicit monomial (the two pins of a zero-paired component). -/
namespace SubmittedGenus.RawGraph.PackedAcceptance.CachedComponentAction
open CachedStepAction

structure Component (cap : ℕ) where
  shift : ℕ
  word : List (CachedStep (cap+1))
  terminal : Terminal (cap+1)

def eval {cap : ℕ} {R : Type*} [CommSemiring R] (z : R) (c : Component cap) : R :=
  z^c.shift * CachedStepAction.value (powers z) c.word c.terminal

def residue {cap : ℕ} (bits m : ℕ) (c : Component cap) : ℕ :=
  (valueBitsMod bits m c.word c.terminal <<< (bits*c.shift))%m

lemma residue_cast {cap : ℕ} (bits m : ℕ) (c : Component cap) :
    (residue bits m c:ZMod m)=eval ((2:ZMod m)^bits) c := by
  simp [residue,eval,Nat.shiftLeft_eq,ZMod.natCast_mod,valueBitsMod_cast,pow_mul,mul_comm]

lemma residue_lt {cap : ℕ} (bits m : ℕ) (hm : 0<m) (c : Component cap) : residue bits m c<m :=
  Nat.mod_lt _ hm

def layoutEval {cap : ℕ} {R : Type*} [CommSemiring R] (z : R) (cs : List (Component cap)) : R :=
  (cs.map (eval z)).prod

/-- Each component and every product is reduced at the same supplied full
modulus. Cached geometry is independent of base and modulus. -/
def layoutResidue {cap : ℕ} (bits m : ℕ) : List (Component cap) → ℕ
  | [] => 1%m
  | c::cs => residue bits m c * layoutResidue bits m cs % m

lemma layoutResidue_cast {cap : ℕ} (bits m : ℕ) (cs : List (Component cap)) :
    (layoutResidue bits m cs:ZMod m)=layoutEval ((2:ZMod m)^bits) cs := by
  induction cs with
  | nil => simp [layoutResidue,layoutEval,ZMod.natCast_mod]
  | cons c cs ih => simp [layoutResidue,layoutEval,ZMod.natCast_mod,residue_cast,ih,layoutEval] at *

lemma layoutResidue_lt {cap : ℕ} (bits m : ℕ) (hm : 0<m) (cs : List (Component cap)) :
    layoutResidue bits m cs<m := by
  cases cs <;> exact Nat.mod_lt _ hm

lemma layoutResidue_eq_val {cap : ℕ} (bits m : ℕ) (hm : 0<m) (cs : List (Component cap)) :
    layoutResidue bits m cs=(layoutEval ((2:ZMod m)^bits) cs).val := by
  rw [←layoutResidue_cast,ZMod.val_natCast,Nat.mod_eq_of_lt (layoutResidue_lt bits m hm cs)]

#print axioms residue_cast
#print axioms layoutResidue_cast
#print axioms layoutResidue_eq_val
end SubmittedGenus.RawGraph.PackedAcceptance.CachedComponentAction
