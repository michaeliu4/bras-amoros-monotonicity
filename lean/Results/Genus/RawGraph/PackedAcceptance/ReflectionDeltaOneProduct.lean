import Results.Genus.RawGraph.PackedAcceptance.ReflectionDeltaOneSignature

namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord
open CompressedSignature
open scoped Matrix

/-- The ordinary strong factor. -/
def fullStep (cap : ℕ) : Step (cap+1) := ⟨mask cap .fullStrong,cap⟩
/-- The ordinary carry factor. The terminal factor is kept separate. -/
def carryStep (cap : ℕ) : Step (cap+1) := ⟨mask cap .carryCarry,cap-1⟩

lemma ofFn_cut {A : Type*} (n q : ℕ) (hq : q≤n) (x y : A) :
    List.ofFn (fun j : Fin n=>if j.val<q then x else y)=
      List.replicate q x ++ List.replicate (n-q) y := by
  obtain ⟨b,rfl⟩:=Nat.exists_eq_add_of_le hq
  rw [List.ofFn_add]
  change ((List.ofFn fun j : Fin q=>if j.val<q then x else y) ++
    List.ofFn fun j : Fin b=>if q+j.val<q then x else y)=_
  simp only [Nat.add_sub_cancel_left]
  have h1 : (fun j : Fin q=>if j.val<q then x else y)=(fun _=>x) := by
    funext j
    simp only [j.isLt,↓reduceIte]
  have h2 : (fun j : Fin b=>if q+j.val<q then x else y)=(fun _=>y) := by
    funext j
    simp only [show ¬q+j.val<q by omega,↓reduceIte]
  rw [h1,h2,List.ofFn_const,List.ofFn_const]

/-- No list or per-vertex scan is needed to certify the two ordinary runs. -/
theorem deltaOneSignature_sourceSteps (n cap q : ℕ) (hq : q≤n+1) :
    sourceSteps (deltaOneSignature n cap q)=
      List.replicate (2*q) (fullStep cap) ++
      List.replicate (2*(n+2)-1-2*q) (carryStep cap) := by
  have he : 2*q≤2*(n+2)-1 := by omega
  rw [←ofFn_cut (2*(n+2)-1) (2*q) he (fullStep cap) (carryStep cap)]
  unfold sourceSteps deltaOneSignature
  congr 1
  funext j
  dsimp only
  by_cases h : j.val<2*q <;> simp only [Fin.val_castSucc,h,↓reduceIte,fullStep,carryStep]

/-- Exact order-preserving matrix powers for the canonical signature. -/
theorem deltaOneSignature_matrix_product {R : Type*} [CommSemiring R]
    (n cap q : ℕ) (hq : q≤n+1) (z : R) :
    ((sourceSteps (deltaOneSignature n cap q)).map (stepMatrix z)).prod=
      stepMatrix z (fullStep cap)^(2*q) *
      stepMatrix z (carryStep cap)^(2*(n+2)-1-2*q) := by
  rw [deltaOneSignature_sourceSteps n cap q hq]
  simp [List.prod_append]

/-- The final carry mask/weight and actual-first strong closure stay in the
accepted terminal evaluator, and therefore are applied exactly once. -/
theorem deltaOneSignature_matrix_value {R : Type*} [CommSemiring R]
    (n cap q : ℕ) (hq : q≤n+1) (z : R) :
    matrixValue (deltaOneSignature n cap q) z
      (stepMatrix z (fullStep cap)^(2*q) *
        stepMatrix z (carryStep cap)^(2*(n+2)-1-2*q))=
      signatureScalar (deltaOneSignature n cap q) z := by
  rw [←deltaOneSignature_matrix_product n cap q hq z,matrixValue_eq_signature]

lemma deltaOneSignature_terminal {R : Type*} [CommSemiring R]
    (n cap q : ℕ) (hq : q≤n+1) (z : R) (first last : Fin (cap+1)) :
    terminal (deltaOneSignature n cap q) z first last=
      (if mask cap .carryCarry last then z^last.val else 0) *
      (if cap≤last.val+first.val then 1 else 0) := by
  have hn : 2*(n+2)-1<2*(n+2)-1+1 := by omega
  have ht : ¬2*(n+2)-1<2*q := by omega
  simp [terminal,signatureVertices,deltaOneSignature,hn,ht]

lemma source_cut_le (g n r a : ℕ) (hg : 0<g) (hp : r+g<g*(n+2)) :
    cut g a r≤n+1 := by
  apply cut_le g a r (n+1) hg
  have he : g*(n+1)+g=g*(n+2) := by ring
  omega

/-- Direct matrix-power evaluation of the original canonical source signature. -/
theorem canonicalSignature_matrix_value {g : ℕ} [NeZero g]
    {R : Type*} [CommSemiring R] (n r p cap : ℕ) (hr : 0<r)
    (hp : p=r+g*1) (hpm : p<g*(n+2)) (hc : Nat.Coprime 1 (n+2))
    (a : Fin g) (ha : a≤ReflectionPairedOrbit.mate r a) (ha0 : a≠0)
    (hpair : a≠ReflectionPairedOrbit.mate r a) (z : R) :
    matrixValue (canonicalSignature n r p 1 cap hp hc a ha ha0 hpair) z
      (stepMatrix z (fullStep cap)^(2*cut g a.val r) *
        stepMatrix z (carryStep cap)^(2*(n+2)-1-2*cut g a.val r))=
      signatureScalar (canonicalSignature n r p 1 cap hp hc a ha ha0 hpair) z := by
  rw [canonicalSignature_delta_one n r p cap hr hp hpm hc a ha ha0 hpair]
  exact deltaOneSignature_matrix_value n cap (cut g a.val r)
    (source_cut_le g n r a.val (NeZero.pos g) (by simpa only [hp,Nat.mul_one] using hpm)) z

#print axioms canonicalSignature_matrix_value
#print axioms deltaOneSignature_sourceSteps
#print axioms deltaOneSignature_matrix_value
#print axioms deltaOneSignature_terminal
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord
