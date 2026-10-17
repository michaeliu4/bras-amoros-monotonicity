import Results.Genus.RawGraph.PackedAcceptance.ReflectionZeroPairedPairWord
import Results.Genus.RawGraph.PackedAcceptance.ReflectionZeroPairedPhysicalSignature

namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionZeroPaired
open SourceModel LayoutCompiler ReflectionPairedOrbit ReflectionFullLayout ReflectionThresholdWord CompressedSignature
open scoped BigOperators Matrix
variable {g : ℕ} [NeZero g]

def letterMatrix {R : Type*} [CommSemiring R] (cap : ℕ) (z : R) (q : Letter) :
    Matrix (Fin (cap+1)) (Fin (cap+1)) R :=
  stepMatrix z ⟨mask cap q,evenBound cap q⟩ * stepMatrix z ⟨mask cap q,oddBound cap q⟩

theorem free_word_product {R : Type*} [CommSemiring R]
    (n r p δ cap : ℕ) (hr : 0<r) (hδ : 0<δ)
    (hp : p=r+g*δ) (hpm : p<g*(n+2)) (hc : Nat.Coprime δ (n+2))
    (hpair : (0:Fin g)≠mate r 0) (z : R) :
    ((sourceSteps (freeSignature n r p δ cap hp hc hpair)).map (stepMatrix z)).prod=
      (List.ofFn (fun j:Fin n=>letterMatrix cap z
        (letter (g*(n+2)) r (g*δ) (g*((δ*(j.val+1))%(n+2)))))).prod := by
  rw [free_sourceSteps n r p δ cap hr hδ hp hpm hc hpair]
  simp only [List.map_flatten,List.prod_flatten,List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext j
  simp [letterSteps,letterMatrix]

theorem free_matrix_value {R : Type*} [CommSemiring R]
    (n r p δ cap : ℕ) (hr : 0<r) (hδ : 0<δ)
    (hp : p=r+g*δ) (hpm : p<g*(n+2)) (hc : Nat.Coprime δ (n+2))
    (hpair : (0:Fin g)≠mate r 0) (z : R) :
    matrixValue (freeSignature n r p δ cap hp hc hpair) z
      ((List.ofFn (fun j:Fin n=>letterMatrix cap z
        (letter (g*(n+2)) r (g*δ) (g*((δ*(j.val+1))%(n+2)))))).prod)=
      signatureScalar (freeSignature n r p δ cap hp hc hpair) z := by
  rw [←free_word_product n r p δ cap hr hδ hp hpm hc hpair]
  exact matrixValue_eq_signature _ z

/-- Every free zero-paired product has the same open terminal evaluator.
The boundary mask is kept even when there are no interior pairs. -/
theorem free_matrix_value_explicit {R : Type*} [CommSemiring R]
    (n r p δ cap : ℕ) (hδ : 0<δ)
    (hp : p=r+g*δ) (hpm : p<g*(n+2)) (hc : Nat.Coprime δ (n+2))
    (hpair : (0:Fin g)≠mate r 0) (z : R)
    (A : Matrix (Fin (cap+1)) (Fin (cap+1)) R) :
    matrixValue (freeSignature n r p δ cap hp hc hpair) z A=
      ∑first,∑last,A first last*(if mask cap .carryCarry last then z^last.val else 0) := by
  have ht (first last : Fin (cap+1)) :
      terminal (freeSignature n r p δ cap hp hc hpair) z first last=
      (if mask cap .carryCarry last then z^last.val else 0) := by
    have hm:=congrFun (free_terminal_mask n r p δ cap hδ hp hpm hc hpair) last
    simp only [freeSignature] at hm
    simp only [terminal,signatureVertices,freeSignature,Nat.lt_succ_self,dif_pos,
      Bool.false_eq_true,if_false,mul_one]
    exact congrArg (fun b:Bool=>if b then z^last.val else 0) hm
  simp only [matrixValue,Matrix.mulVec,dotProduct,ht]

#print axioms free_word_product
#print axioms free_matrix_value
#print axioms free_matrix_value_explicit
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionZeroPaired
