import Results.Genus.RawGraph.PackedAcceptance.ReflectionCosetAffine
import Results.Genus.RawGraph.PackedAcceptance.ReflectionCoprime

/-! Explicit path orders on the translation cosets fixed by the original
reflection. The additive coset embedding retains the original residue labels. -/
namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionFixedOrbit
open ReflectionCoset ReflectionConsecutive

/-- A full residue path for targets t and t+u, where u is a unit. -/
def normalizedTarget (n : ℕ) (t : ZMod (n+2)) (u : (ZMod (n+2))ˣ) : Fin (n+2) :=
  ⟨(((u⁻¹:(ZMod (n+2))ˣ):ZMod (n+2))*t).val,ZMod.val_lt _⟩

abbrev phaseOrder (n : ℕ) (t : ZMod (n+2)) (u : (ZMod (n+2))ˣ) : Fin (n+2) ≃ ZMod (n+2) :=
  (ReflectionConsecutive.order (n+1) (normalizedTarget n t u).val).trans (ReflectionCoprime.scale u)

lemma phaseOrder_apply (n : ℕ) (t : ZMod (n+2)) (u : (ZMod (n+2))ˣ) (j : Fin (n+2)) :
    phaseOrder n t u j=(u:ZMod (n+2))*asResidue (n+1)
      (ReflectionConsecutive.order (n+1) (normalizedTarget n t u).val j) := rfl

lemma normalizedTarget_value (n : ℕ) (t : ZMod (n+2)) (u : (ZMod (n+2))ˣ) :
    (u:ZMod (n+2))*((normalizedTarget n t u).val:ZMod (n+2))=t := by
  change (u:ZMod (n+2))*
    (((((u⁻¹:(ZMod (n+2))ˣ):ZMod (n+2))*t).val:ℕ):ZMod (n+2))=t
  rw [ZMod.natCast_zmod_val]
  simp [←mul_assoc]

lemma normalizedTarget_next (n : ℕ) (t : ZMod (n+2)) (u : (ZMod (n+2))ˣ) :
    (u:ZMod (n+2))*(((normalizedTarget n t u).val+1:ℕ):ZMod (n+2))=t+(u:ZMod (n+2)) := by
  rw [Nat.cast_add,Nat.cast_one,mul_add,mul_one,normalizedTarget_value]

lemma phaseOrder_zero (n : ℕ) (t : ZMod (n+2)) (u : (ZMod (n+2))ˣ) :
    phaseOrder n t u (normalizedTarget n t u)=0 := by
  rw [phaseOrder_apply]
  exact (congrArg (fun z:Fin (n+2)=>(u:ZMod (n+2))*asResidue (n+1) z)
    (ReflectionConsecutive.order_zero (n+1) (normalizedTarget n t u))).trans (mul_zero _)

lemma phaseOrder_adjacent (n : ℕ) (t : ZMod (n+2)) (u : (ZMod (n+2))ˣ)
    (i j : Fin (n+2)) (hne : i≠j)
    (h : phaseOrder n t u i+phaseOrder n t u j=t ∨
      phaseOrder n t u i+phaseOrder n t u j=t+(u:ZMod (n+2))) :
    i.val+1=j.val ∨ j.val+1=i.val := by
  apply ReflectionConsecutive.adjacent_of_pair (n+1) (normalizedTarget n t u).val (by omega) i j hne
  simp only [phaseOrder_apply] at h
  rcases h with h|h
  · left
    apply u.isUnit.mul_left_cancel
    rw [mul_add,normalizedTarget_value]
    exact h
  · right
    apply u.isUnit.mul_left_cancel
    rw [mul_add,normalizedTarget_next]
    exact h

variable {g : ℕ} [NeZero g]

/-- The reduced reflection target is computed from the original reflected
coset origin by the proved quotient/remainder inverse. -/
def target (n : ℕ) (a : Fin g) (r : ZMod (g*(n+2)))
    (hfix : (r-affineValue a (0:ZMod (n+2))).val%g=a.val) : ZMod (n+2) :=
  (affineEquiv a).symm ⟨r-affineValue a 0,hfix⟩

lemma target_value (n : ℕ) (a : Fin g) (r : ZMod (g*(n+2)))
    (hfix : (r-affineValue a (0:ZMod (n+2))).val%g=a.val) :
    affineValue a (target n a r hfix)=r-affineValue a (0:ZMod (n+2)) := by
  have he := congrArg Subtype.val ((affineEquiv (L:=n+2) a).apply_symm_apply
    ⟨r-affineValue a 0,hfix⟩)
  exact (affineEquiv_val a (target n a r hfix)).symm.trans he

/-- A complete explicit order of all original residues in one fixed coset. -/
abbrev order (n : ℕ) (a : Fin g) (r : ZMod (g*(n+2)))
    (hfix : (r-affineValue a (0:ZMod (n+2))).val%g=a.val) (u : (ZMod (n+2))ˣ) :
    Fin (n+2) ≃ Coset g (n+2) a :=
  (phaseOrder n (target n a r hfix) u).trans (affineEquiv a)

lemma order_val (n : ℕ) (a : Fin g) (r : ZMod (g*(n+2)))
    (hfix : (r-affineValue a (0:ZMod (n+2))).val%g=a.val) (u : (ZMod (n+2))ˣ) (i : Fin (n+2)) :
    (order n a r hfix u i).val=affineValue a (phaseOrder n (target n a r hfix) u i) :=
  affineEquiv_val a _

/-- Every original reflection edge within this coset is a consecutive pair
in its full path; all reflection self-pairs remain unary source constraints. -/
lemma adjacent_of_pair (n : ℕ) (a : Fin g) (r p : ZMod (g*(n+2)))
    (hfix : (r-affineValue a (0:ZMod (n+2))).val%g=a.val) (u : (ZMod (n+2))ˣ)
    (hgap : scaleHom g (n+2) (u:ZMod (n+2))=p-r)
    (i j : Fin (n+2)) (hne : i≠j)
    (h : (order n a r hfix u i).val+(order n a r hfix u j).val=r ∨
      (order n a r hfix u i).val+(order n a r hfix u j).val=p) :
    i.val+1=j.val ∨ j.val+1=i.val := by
  apply phaseOrder_adjacent n (target n a r hfix) u i j hne
  simp only [order_val] at h
  have ht := target_value n a r hfix
  have hp : affineValue a (target n a r hfix+(u:ZMod (n+2)))=p-affineValue a (0:ZMod (n+2)) := by
    rw [affineValue_add,ht,hgap]
    ring
  rcases h with h|h
  · left
    exact (affineValue_pair_iff a r (target n a r hfix) _ _ ht).mp h
  · right
    exact (affineValue_pair_iff a p (target n a r hfix+(u:ZMod (n+2))) _ _ hp).mp h

#print axioms phaseOrder_zero
#print axioms phaseOrder_adjacent
#print axioms target_value
#print axioms adjacent_of_pair
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionFixedOrbit
