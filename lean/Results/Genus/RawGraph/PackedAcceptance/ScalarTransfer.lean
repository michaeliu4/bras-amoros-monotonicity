import Results.Genus.RawGraph.Layout
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs

namespace SubmittedGenus.RawGraph.PackedAcceptance
open LayoutCompiler SourceModel
open scoped BigOperators

/-- Transfer is natural under semiring homomorphisms, including evaluation
into a finite residue ring used by the packed checker. -/
lemma map_run {A R S : Type*} [Fintype A] [CommSemiring R] [CommSemiring S]
    (f : R→+*S) (n : ℕ) (w : ℕ→A→R) (edge : ℕ→A→A→R)
    (finish : A→R) (first : A) :
    f (Transfer.run n w edge finish first)=
      Transfer.run n (fun j a=>f (w j a)) (fun j a b=>f (edge j a b))
        (fun a=>f (finish a)) first := by
  induction n generalizing w edge first with
  | zero => simp [Transfer.run]
  | succ n ih =>
    simp [Transfer.run,ih,Transfer.shift]
    rfl

lemma map_pathRun {A R S : Type*} [Fintype A] [CommSemiring R] [CommSemiring S]
    (f : R→+*S) (n : ℕ) (w : ℕ→A→R) (edge : ℕ→A→A→R) :
    f (Transfer.pathRun n w edge)=
      Transfer.pathRun n (fun j a=>f (w j a)) (fun j a b=>f (edge j a b)) := by
  simp [Transfer.pathRun,map_run]

lemma map_cycleRun {A R S : Type*} [Fintype A] [CommSemiring R] [CommSemiring S]
    (f : R→+*S) (n : ℕ) (w : ℕ→A→R) (edge : ℕ→A→A→R) (close : A→A→R) :
    f (Transfer.cycleRun n w edge close)=
      Transfer.cycleRun n (fun j a=>f (w j a)) (fun j a b=>f (edge j a b))
        (fun a b=>f (close a b)) := by
  simp [Transfer.cycleRun,map_run]

section Scalar
variable {R : Type*} [CommSemiring R]

def vertexScalar {m : ℕ} (r p a : ℕ) (z : R) (i : Fin (m-1))
    (value : Fin (a+1)) : R :=
  if Domain r p a i value.val then z^value.val else 0

def edgeScalar {m : ℕ} (r p a : ℕ) (i j : Fin (m-1))
    (left right : Fin (a+1)) : R :=
  if edgeBound r p a i j≤left.val+right.val then 1 else 0

def scalarVertices {m : ℕ} (L : Layout m) (r p a : ℕ) (z : R)
    (c : Fin L.count) (j : ℕ) (value : Fin (a+1)) : R :=
  if h : j<L.edges c+1 then vertexScalar r p a z (L.label ⟨c,⟨j,h⟩⟩) value else 0

def scalarEdges {m : ℕ} (L : Layout m) (r p a : ℕ)
    (c : Fin L.count) (j : ℕ) (left right : Fin (a+1)) : R :=
  if h : j<L.edges c then edgeScalar r p a
    (L.label ⟨c,(⟨j,h⟩:Fin (L.edges c)).castSucc⟩)
    (L.label ⟨c,(⟨j,h⟩:Fin (L.edges c)).succ⟩) left right else 1

def scalarClose {m : ℕ} (L : Layout m) (r p a : ℕ)
    (c : Fin L.count) (last first : Fin (a+1)) : R :=
  edgeScalar r p a (L.label ⟨c,Fin.last (L.edges c)⟩) (L.label ⟨c,0⟩) last first

def scalarComponent {m : ℕ} (L : Layout m) (r p a : ℕ) (z : R) (c : Fin L.count) : R :=
  if L.cycle c=true then Transfer.cycleRun (L.edges c)
    (scalarVertices L r p a z c) (scalarEdges L r p a c) (scalarClose L r p a c)
  else Transfer.pathRun (L.edges c) (scalarVertices L r p a z c) (scalarEdges L r p a c)

def scalarLayout {m : ℕ} (L : Layout m) (r p a : ℕ) (z : R) : R :=
  ∏ c,scalarComponent L r p a z c

lemma eval_component {m : ℕ} (L : Layout m) (r p a : ℕ) (z : R) (c : Fin L.count) :
    Polynomial.eval₂ (Nat.castRingHom R) z (componentRun L r p a c)=
      scalarComponent L r p a z c := by
  let f := Polynomial.eval₂RingHom (Nat.castRingHom R) z
  have hv : (fun j v=>f (transferVertices L r p a c j v))=scalarVertices L r p a z c := by
    funext j v
    simp only [transferVertices,scalarVertices]
    split_ifs <;> simp [f,vertexWeight,vertexScalar,apply_ite]
    split_ifs <;> simp_all
  have he : (fun j u v=>f (transferEdges L r p a c j u v))=scalarEdges (R:=R) L r p a c := by
    funext j u v
    simp only [transferEdges,scalarEdges]
    split_ifs <;> simp [f,edgeWeight,edgeScalar]
  have hc : (fun u v=>f (transferClose L r p a c u v))=scalarClose (R:=R) L r p a c := by
    funext u v
    simp [f,transferClose,scalarClose,edgeWeight,edgeScalar]
  change f (componentRun L r p a c)=_
  unfold componentRun scalarComponent
  split_ifs
  · rw [map_cycleRun,hv,he,hc]
  · rw [map_pathRun,hv,he]

/-- An accepted physical layout evaluates the original raw polynomial in
any commutative semiring, with all loops and closing cycle states retained. -/
theorem eval_raw_eq_scalar {m r p a : ℕ} (L : Layout m)
    (hp : Parameters m r p a) (hc : Covers L r p a) (z : R) :
    Polynomial.eval₂ (Nat.castRingHom R) z (rawPolynomial m r p a)=
      scalarLayout L r p a z := by
  rw [rawPolynomial_eq_components L hp hc]
  change (Polynomial.eval₂RingHom (Nat.castRingHom R) z) (∏ c,componentRun L r p a c)=_
  rw [map_prod]
  exact Finset.prod_congr rfl (fun c _=>eval_component L r p a z c)
end Scalar

#print axioms map_run
#print axioms eval_raw_eq_scalar
end SubmittedGenus.RawGraph.PackedAcceptance
