import Results.Genus.RawGraph.PackedAcceptance.Digits
import Results.Genus.RawGraph.PackedAcceptance.TransferTable

namespace SubmittedGenus.RawGraph.PackedAcceptance
open LayoutCompiler Packing

/-- Original submitted digit width, not a floating-point precision parameter. -/
def digitBase (H : ℕ) : ℕ := 2^(H+2)
def modulus (H : ℕ) : ℕ := digitBase H^(H+1)

/-- Every arithmetic operation of the checker takes place in the exact
finite residue ring, so high digits can be discarded throughout transfer. -/
def layoutResidue {m : ℕ} (L : Layout m) (r p a H : ℕ) : ℕ :=
  (scalarLayout L r p a (digitBase H : ZMod (modulus H))).val

lemma layoutResidue_eq_eval {m r p a : ℕ} (L : Layout m)
    (hp : Parameters m r p a) (hc : Covers L r p a) (H : ℕ) :
    layoutResidue L r p a H=(rawPolynomial m r p a).eval (digitBase H)%modulus H := by
  unfold layoutResidue
  rw [←eval_raw_eq_scalar L hp hc,Polynomial.eval₂_at_natCast]
  exact ZMod.val_natCast _ _

/-- Finite acceptance checks the exact residue and every proposed digit.
No hash, native evaluator or producer assertion is a proof premise. -/
def LayoutAccepts {m : ℕ} (L : Layout m) (r p a H : ℕ) (coeffs : Fin (H+1)→ℕ) : Prop :=
  layoutResidue L r p a H=pack (digitBase H) coeffs ∧
    ∀i,coeffs i<digitBase H

instance {m : ℕ} (L : Layout m) (r p a H : ℕ) (coeffs : Fin (H+1)→ℕ) :
    Decidable (LayoutAccepts L r p a H coeffs) := by
  unfold LayoutAccepts
  infer_instance

/-- Soundness for the actual original cap-four or cap-five graph source.
All retained coefficients follow from one accepted packed residue. -/
theorem accepted_layout_coeff {m r p a H : ℕ} (L : Layout m)
    (hp : Parameters m r p a) (hc : Covers L r p a)
    (coeffs : Fin (H+1)→ℕ) (accepted : LayoutAccepts L r p a H coeffs) (k : Fin (H+1)) :
    (rawPolynomial m r p a).coeff k.val=coeffs k := by
  have hb : 0<digitBase H := by unfold digitBase; positivity
  have hbound (i : Fin (H+1)) : (rawPolynomial m r p a).coeff i.val<digitBase H := by
    apply (fixed_coeff_le_compositions m r p a i.val).trans_lt
    exact Nat.pow_lt_pow_right (by decide) (by have := i.isLt; omega)
  have he := accepted.1
  rw [layoutResidue_eq_eval L hp hc] at he
  have hh := accepted_residue_coeff (rawPolynomial m r p a) hb hbound he k
  exact hh.trans (digit_pack hb coeffs accepted.2 k)

#print axioms layoutResidue_eq_eval
#print axioms accepted_layout_coeff
end SubmittedGenus.RawGraph.PackedAcceptance
