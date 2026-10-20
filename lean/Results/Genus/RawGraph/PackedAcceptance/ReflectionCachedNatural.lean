import Results.Genus.RawGraph.PackedAcceptance.CachedComponentAction
import Results.Genus.RawGraph.PackedAcceptance.ReflectionCachedOriginal

/-! One cached original layout serves both generic semiring evaluation and
natural bitshift arithmetic. No source geometry is reconstructed by an action. -/
namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionCachedNatural
open CachedStepAction CachedComponentAction ReflectionCachedBranches
open CompressedSignature ReflectionThresholdWord ReflectionFixedPhase
open LayoutCompiler SourceModel ReflectionPairedOrbit ReflectionFullLayout Packing
open scoped BigOperators

variable {g : ℕ} [NeZero g]

def component (n r p d cap : ℕ) (hc : Nat.Coprime d (n+2)) (hp : p=r+g*d)
    (hp0 : 0<p) (hpm : p<g*(n+2)) (c : Fin (count (g:=g) r)) : Component cap :=
  if hfix:representative r c=mate r (representative r c) then
    if hz:representative r c=0 then
      let hf : (0:Fin g)=mate r 0 := by simpa only [hz] using hfix
      let s:=ReflectionFixedZeroPhysical.signature n r p d cap hc hp hp0 hpm hf
      ⟨0,ReflectionZeroCachedAction.word n d (cut g 0 r) (targetIndex n r d 0 hf hc) s,cacheTerminal s⟩
    else
      let s:=ReflectionFixedPhysicalLabels.signature n r p d cap (representative r c) hfix hc hz
      ⟨0,Fixed.word n r p d cap (representative r c) hfix hc hz,cacheTerminal s⟩
  else if hz:representative r c=0 then
    let hf : (0:Fin g)≠mate r 0 := by simpa only [hz] using hfix
    let s:=ReflectionZeroPaired.freeSignature n r p d cap hp hc hf
    ⟨2*cap,ZeroPaired.word (g:=g) n r d cap,cacheTerminal s⟩
  else
    let q:=cut g (representative r c).val r
    ⟨0,Paired.word n d cap q,cacheTerminal (normalizedSignature n d cap q)⟩

lemma component_eval {R : Type*} [CommSemiring R]
    (n r p d cap : ℕ) (hc : Nat.Coprime d (n+2)) (hp : p=r+g*d)
    (hp0 : 0<p) (hpm : p<g*(n+2)) (c : Fin (count (g:=g) r)) (z : R) :
    eval z (component n r p d cap hc hp hp0 hpm c)=
      ReflectionCachedBranches.componentValue n r p d cap hc hp hp0 hpm c z := by
  unfold component ReflectionCachedBranches.componentValue
  split_ifs <;> simp only [eval,zeroFixedValue,fixedValue,zeroPairedValue,pairedValue,pow_zero,one_mul]

def components (n r p d cap : ℕ) (hc : Nat.Coprime d (n+2)) (hp : p=r+g*d)
    (hp0 : 0<p) (hpm : p<g*(n+2)) : List (Component cap) :=
  List.ofFn (fun c:Fin (count (g:=g) r)=>component n r p d cap hc hp hp0 hpm c)

lemma components_eval {R : Type*} [CommSemiring R]
    (n r p d cap : ℕ) (hc : Nat.Coprime d (n+2)) (hp : p=r+g*d)
    (hp0 : 0<p) (hpm : p<g*(n+2)) (z : R) :
    layoutEval z (components n r p d cap hc hp hp0 hpm)=
      ∏c:Fin (count (g:=g) r),ReflectionCachedBranches.componentValue n r p d cap hc hp hp0 hpm c z := by
  simp only [layoutEval,components,List.map_ofFn,List.prod_ofFn,Function.comp_apply,component_eval]

def compile (M r p cap : ℕ) (hrp : r<p) (hpm : p<M) : List (Component cap) :=
  let C:=ReflectionOriginalLayout.coordinates M r p hrp hpm
  letI : NeZero C.g:=⟨ne_of_gt C.g_pos⟩
  components C.n r p C.δ cap C.coprime C.gap C.pivot_pos C.pivot_lt

lemma compile_eval {R : Type*} [CommSemiring R] (M r p cap : ℕ)
    (hrp : r<p) (hpm : p<M) (z : R) :
    layoutEval z (compile M r p cap hrp hpm)=ReflectionCachedOriginal.value M r p cap hrp hpm z := by
  let C:=ReflectionOriginalLayout.coordinates M r p hrp hpm
  letI : NeZero C.g:=⟨ne_of_gt C.g_pos⟩
  change layoutEval z (components C.n r p C.δ cap C.coprime C.gap C.pivot_pos C.pivot_lt)=_
  exact components_eval _ _ _ _ _ _ _ _ _ z

/-- Execute an already-built layout at any power-of-two base and any supplied
modulus. The transport is exact even for a nonunit base. -/
def naturalValue (M r p cap bits m : ℕ) (hrp : r<p) (hpm : p<M) : ℕ :=
  CachedComponentAction.layoutResidue bits m (compile M r p cap hrp hpm)

lemma naturalValue_cast (M r p cap bits m : ℕ) (hrp : r<p) (hpm : p<M) :
    (naturalValue M r p cap bits m hrp hpm:ZMod m)=
      ReflectionCachedOriginal.value M r p cap hrp hpm ((2:ZMod m)^bits) := by
  rw [naturalValue,layoutResidue_cast,compile_eval]

def residue (M r p cap H : ℕ) (hrp : r<p) (hpm : p<M) : ℕ :=
  naturalValue M r p cap (H+2) (modulus H) hrp hpm

lemma residue_cast (M r p cap H : ℕ) (hrp : r<p) (hpm : p<M) :
    (residue M r p cap H hrp hpm:ZMod (modulus H))=
      ReflectionCachedOriginal.value M r p cap hrp hpm (digitBase H:ZMod (modulus H)) := by
  rw [residue,naturalValue_cast]
  simp only [digitBase,Nat.cast_pow,Nat.cast_ofNat]

lemma residue_eq_original (M r p cap H : ℕ) (hrp : r<p) (hpm : p<M) :
    residue M r p cap H hrp hpm=ReflectionCachedOriginal.residue M r p cap H hrp hpm := by
  have hm : 0<modulus H := by unfold modulus digitBase;positivity
  unfold residue naturalValue ReflectionCachedOriginal.residue
  rw [layoutResidue_eq_val _ _ hm,compile_eval]
  simp only [digitBase,Nat.cast_pow,Nat.cast_ofNat]

theorem residue_eq_eval {M r p cap : ℕ} (hp : Parameters M r p cap) (H : ℕ) :
    residue M r p cap H hp.2.1 hp.2.2.1=
      (rawPolynomial M r p cap).eval (digitBase H)%modulus H := by
  rw [residue_eq_original,ReflectionCachedOriginal.residue_eq_eval hp H]

/-- Provider contract for exact pruned sums and explicit finite chunks. -/
theorem provider_eq_scalar {M r p cap : ℕ} (hp : Parameters M r p cap) (H : ℕ) :
    (residue M r p cap H hp.2.1 hp.2.2.1:ZMod (modulus H))=
      scalarLayout (ReflectionOriginalLayout.layout M r p hp.2.1 hp.2.2.1)
        r p cap (digitBase H:ZMod (modulus H)) := by
  rw [residue_cast]
  exact (ReflectionCachedOriginal.value_eq_scalar M r p cap hp.1 hp.2.1 hp.2.2.1 _).symm

def Accepts (M r p cap H : ℕ) (hrp : r<p) (hpm : p<M) (coeffs : Fin (H+1)→ℕ) : Prop :=
  residue M r p cap H hrp hpm=pack (digitBase H) coeffs ∧ ∀i,coeffs i<digitBase H
instance (M r p cap H : ℕ) (hrp : r<p) (hpm : p<M) (coeffs : Fin (H+1)→ℕ) :
    Decidable (Accepts M r p cap H hrp hpm coeffs) := by unfold Accepts;infer_instance

theorem accepted_coeff {M r p cap H : ℕ} (hp : Parameters M r p cap)
    (coeffs : Fin (H+1)→ℕ) (accepted : Accepts M r p cap H hp.2.1 hp.2.2.1 coeffs)
    (k : Fin (H+1)) : (rawPolynomial M r p cap).coeff k.val=coeffs k := by
  apply ReflectionCachedOriginal.accepted_coeff hp coeffs
  refine ⟨?_,accepted.2⟩
  rw [←residue_eq_original]
  exact accepted.1

#print axioms component_eval
#print axioms compile_eval
#print axioms naturalValue_cast
#print axioms residue_eq_eval
#print axioms provider_eq_scalar
#print axioms accepted_coeff
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionCachedNatural
