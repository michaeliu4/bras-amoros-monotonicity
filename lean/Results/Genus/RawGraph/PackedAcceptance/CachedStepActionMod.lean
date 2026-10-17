import Results.Genus.RawGraph.PackedAcceptance.CachedStepAction

/-! Full-modulus natural bitshift action. Each row entry is reduced only
modulo the supplied original modulus; the source word and terminal are intact.
The generic cast proof uses no cancellation or extracted-origin assumption. -/
namespace SubmittedGenus.RawGraph.PackedAcceptance.CachedStepAction
open scoped BigOperators

def castVector {k : ℕ} (m : ℕ) (v : List.Vector ℕ k) : List.Vector (ZMod m) k :=
  List.Vector.ofFn (fun i=>(v.get i:ZMod m))

def actionBitsMod {k : ℕ} (bits m : ℕ) (s : CachedStep k) (v : List.Vector ℕ k) : List.Vector ℕ k :=
  List.Vector.ofFn (fun i=>if s.mask.get i then ((admittedSum s v i) <<< (bits*i.val))%m else 0)

lemma actionBitsMod_cast {k : ℕ} (bits m : ℕ) (s : CachedStep k) (v : List.Vector ℕ k) :
    castVector m (actionBitsMod bits m s v)=
      action (powers ((2:ZMod m)^bits)) s (castVector m v) := by
  apply List.Vector.ext
  intro i
  simp [castVector,actionBitsMod,action,powers,admittedSum,List.sum_ofFn,
    ZMod.natCast_mod,Nat.shiftLeft_eq,pow_mul,mul_comm]

def runBitsMod {k : ℕ} (bits m : ℕ) : List (CachedStep k) → List.Vector ℕ k → List.Vector ℕ k
  | [],v => v
  | s::w,v => actionBitsMod bits m s (runBitsMod bits m w v)

lemma runBitsMod_cast {k : ℕ} (bits m : ℕ) (w : List (CachedStep k)) (v : List.Vector ℕ k) :
    castVector m (runBitsMod bits m w v)=run (powers ((2:ZMod m)^bits)) w (castVector m v) := by
  induction w with
  | nil => rfl
  | cons s w ih => simp only [runBitsMod,run,actionBitsMod_cast,ih]

lemma finish_cast {k : ℕ} (bits m : ℕ) (t : Terminal k) (first : Fin k) :
    castVector m (finish (powers (2^bits:ℕ)) t first)=
      finish (powers ((2:ZMod m)^bits)) t first := by
  apply List.Vector.ext
  intro i
  simp [castVector,finish,powers]

lemma runBitsMod_finish_get {k : ℕ} (bits m : ℕ) (w : List (CachedStep k))
    (t : Terminal k) (first i : Fin k) :
    ((runBitsMod bits m w (finish (powers (2^bits:ℕ)) t first)).get i:ZMod m)=
      (run (powers ((2:ZMod m)^bits)) w (finish (powers ((2:ZMod m)^bits)) t first)).get i := by
  have h:=congrArg (fun v : List.Vector (ZMod m) k=>v.get i)
    (runBitsMod_cast bits m w (finish (powers (2^bits:ℕ)) t first))
  rw [finish_cast] at h
  simpa only [castVector,List.Vector.get_ofFn] using h

def valueBitsMod {cap : ℕ} (bits m : ℕ) (w : List (CachedStep (cap+1))) (t : Terminal (cap+1)) : ℕ :=
  let p:=powers (2^bits:ℕ)
  if t.cycle then (List.ofFn (fun first=>(runBitsMod bits m w (finish p t first)).get first)).sum%m
  else vectorSum (runBitsMod bits m w (finish p t 0))%m

lemma valueBitsMod_cast {cap : ℕ} (bits m : ℕ) (w : List (CachedStep (cap+1))) (t : Terminal (cap+1)) :
    (valueBitsMod bits m w t:ZMod m)=value (powers ((2:ZMod m)^bits)) w t := by
  unfold valueBitsMod value vectorSum
  split_ifs <;> simp only [List.sum_ofFn,ZMod.natCast_mod,Nat.cast_sum,runBitsMod_finish_get]

lemma valueBitsMod_lt {cap : ℕ} (bits m : ℕ) (hm : 0<m)
    (w : List (CachedStep (cap+1))) (t : Terminal (cap+1)) : valueBitsMod bits m w t<m := by
  unfold valueBitsMod
  split_ifs <;> exact Nat.mod_lt _ hm

/-- Canonical full-modulus original signature residue, with no digit extraction
or numerical acceptance folded into this source semantics theorem. -/
theorem valueBitsMod_eq_val {cap : ℕ} (bits m : ℕ) (hm : 0<m) (s : ComponentSignature cap)
    (w : List (CachedStep (cap+1))) (hw : w=(CompressedSignature.sourceSteps s).map cache) :
    valueBitsMod bits m w (cacheTerminal s)=(signatureScalar s ((2:ZMod m)^bits)).val := by
  have he : (valueBitsMod bits m w (cacheTerminal s):ZMod m)=signatureScalar s ((2:ZMod m)^bits) := by
    rw [valueBitsMod_cast]
    exact value_eq s _ w hw
  rw [←he,ZMod.val_natCast,Nat.mod_eq_of_lt (valueBitsMod_lt bits m hm w _)]

#print axioms actionBitsMod_cast
#print axioms runBitsMod_cast
#print axioms valueBitsMod_cast
#print axioms valueBitsMod_eq_val
end SubmittedGenus.RawGraph.PackedAcceptance.CachedStepAction
