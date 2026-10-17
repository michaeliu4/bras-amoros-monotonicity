import Results.Genus.RawGraph.PackedAcceptance.ScalarTransfer

namespace SubmittedGenus.RawGraph.PackedAcceptance
open LayoutCompiler SourceModel
open scoped BigOperators

/-- An ordered source signature retains every vertex mask, ordinary edge
threshold and the actual closing edge. Reversal is not identified here. -/
structure ComponentSignature (a : ℕ) where
  edges : ℕ
  mask : Fin (edges+1)→Fin (a+1)→Bool
  bound : Fin edges→ℕ
  cycle : Bool
  close : ℕ

def physicalSignature {m : ℕ} (L : Layout m) (r p a : ℕ) (c : Fin L.count) :
    ComponentSignature a where
  edges := L.edges c
  mask j v := decide (Domain r p a (L.label ⟨c,j⟩) v.val)
  bound j := edgeBound r p a (L.label ⟨c,j.castSucc⟩) (L.label ⟨c,j.succ⟩)
  cycle := L.cycle c
  close := edgeBound r p a (L.label ⟨c,Fin.last (L.edges c)⟩) (L.label ⟨c,0⟩)

section
variable {R : Type*} [CommSemiring R]

def signatureVertices {a : ℕ} (s : ComponentSignature a) (z : R)
    (j : ℕ) (v : Fin (a+1)) : R :=
  if h:j<s.edges+1 then if s.mask ⟨j,h⟩ v then z^v.val else 0 else 0

def signatureEdges {a : ℕ} (s : ComponentSignature a)
    (j : ℕ) (u v : Fin (a+1)) : R :=
  if h:j<s.edges then if s.bound ⟨j,h⟩≤u.val+v.val then 1 else 0 else 1

def signatureScalar {a : ℕ} (s : ComponentSignature a) (z : R) : R :=
  if s.cycle then Transfer.cycleRun s.edges (signatureVertices s z) (signatureEdges s)
    (fun last first=>if s.close≤last.val+first.val then 1 else 0)
  else Transfer.pathRun s.edges (signatureVertices s z) (signatureEdges s)

/-- Exact component semantics factors through the ordered signature. This
is the correctness layer for source-exact component caches. -/
lemma scalarComponent_eq_signature {m : ℕ} (L : Layout m) (r p a : ℕ)
    (c : Fin L.count) (z : R) :
    scalarComponent L r p a z c=signatureScalar (physicalSignature L r p a c) z := by
  have hv : scalarVertices L r p a z c=signatureVertices (physicalSignature L r p a c) z := by
    funext j v
    simp only [scalarVertices,signatureVertices,physicalSignature,vertexScalar]
    split_ifs <;> simp_all
  have he : scalarEdges (R:=R) L r p a c=signatureEdges (physicalSignature L r p a c) := by
    funext j u v
    simp only [scalarEdges,signatureEdges,physicalSignature,edgeScalar]
    rfl
  unfold scalarComponent signatureScalar
  rw [hv,he]
  rfl

/-- Equal ordered signatures permit reuse across different multiplicities
and pivots in every coefficient or residue semiring. -/
theorem scalarComponent_eq_of_signature {m₁ m₂ a : ℕ}
    (L₁ : Layout m₁) (L₂ : Layout m₂) (r₁ p₁ r₂ p₂ : ℕ)
    (c₁ : Fin L₁.count) (c₂ : Fin L₂.count)
    (h : physicalSignature L₁ r₁ p₁ a c₁=physicalSignature L₂ r₂ p₂ a c₂) (z : R) :
    scalarComponent L₁ r₁ p₁ a z c₁=scalarComponent L₂ r₂ p₂ a z c₂ := by
  rw [scalarComponent_eq_signature,scalarComponent_eq_signature,h]

/-- A checked signature assignment may replace every component by a shared
cache entry without changing the complete original source evaluation. -/
theorem eval_raw_eq_signature_product {m r p a : ℕ} (L : Layout m)
    (hp : Parameters m r p a) (hc : Covers L r p a)
    {I : Type*} (cache : I→ComponentSignature a) (key : Fin L.count→I)
    (h : ∀c,physicalSignature L r p a c=cache (key c)) (z : R) :
    Polynomial.eval₂ (Nat.castRingHom R) z (rawPolynomial m r p a)=
      ∏c,signatureScalar (cache (key c)) z := by
  rw [eval_raw_eq_scalar L hp hc z]
  unfold scalarLayout
  apply Finset.prod_congr rfl
  intro c _
  rw [scalarComponent_eq_signature,h c]
end

#print axioms scalarComponent_eq_signature
#print axioms scalarComponent_eq_of_signature
#print axioms eval_raw_eq_signature_product
end SubmittedGenus.RawGraph.PackedAcceptance
