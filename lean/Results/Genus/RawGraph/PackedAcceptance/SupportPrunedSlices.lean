import Results.Genus.RawGraph.PackedAcceptance.RangeSlices

/-! A source-proved arithmetic pruning gate. Every omitted scalar summand
has no source coefficient at or below the retained genus cutoff. -/
namespace SubmittedGenus.RawGraph.PackedAcceptance
open scoped BigOperators
open LayoutCompiler Packing

lemma scalarLayout_zero_of_support {m r p a H : ℕ} (L : Layout m)
    (hp : Parameters m r p a) (hc : Covers L r p a)
    (hs : 2*H<(a-1)*m+p+1) :
    scalarLayout L r p a (digitBase H:ZMod (modulus H))=0 := by
  apply (ZMod.val_eq_zero _).mp
  change layoutResidue L r p a H=0
  rw [layoutResidue_eq_eval L hp hc H]
  unfold modulus
  rw [eval_mod_eq_prefix]
  have hz : (fun i : Fin (H+1)=>(rawPolynomial m r p a).coeff i.val)=(fun _=>0) := by
    funext i
    apply rawPolynomial_coeff_zero_of_support
    have hi:=i.isLt
    omega
  rw [hz,pack_eq_sum]
  simp

def prunedMultiplicityResidue (M P a H : ℕ) (layouts : (t : Triple M P)→Layout t.m)
    (mi : Fin (M-2)) : ZMod (modulus H) :=
  ∑pi : Fin (min P (mi.val+2)-1),
    if 2*H<(a-1)*(mi.val+3)+(pi.val+2)+1 then 0 else
      ∑ri : Fin (pi.val+1),
        scalarLayout (layouts ⟨mi,pi,ri⟩) (ri.val+1) (pi.val+2) a (digitBase H:ZMod (modulus H))

lemma multiplicityResidue_eq_pruned (M P a H : ℕ) (layouts : (t : Triple M P)→Layout t.m)
    (ha : a=4 ∨ a=5) (hc : ∀t,Covers (layouts t) t.r t.p a)
    (mi : Fin (M-2)) :
    multiplicityResidue M P a H layouts mi=prunedMultiplicityResidue M P a H layouts mi := by
  unfold multiplicityResidue prunedMultiplicityResidue
  apply Finset.sum_congr rfl
  intro pi _
  split_ifs with h
  · apply Finset.sum_eq_zero
    intro ri _
    apply scalarLayout_zero_of_support (layouts ⟨mi,pi,ri⟩) (Triple.parameters _ ha) (hc _)
    exact h
  · rfl

theorem accepted_range_of_pruned_slices (M P a H : ℕ)
    (layouts : (t : Triple M P)→Layout t.m) (ha : a=4 ∨ a=5)
    (hc : ∀t,Covers (layouts t) t.r t.p a)
    (values : Fin (M-2)→ZMod (modulus H))
    (hs : ∀mi,prunedMultiplicityResidue M P a H layouts mi=values mi)
    (coeffs : Fin (H+1)→ℕ)
    (h : (∑mi,values mi).val=pack (digitBase H) coeffs ∧ ∀i,coeffs i<digitBase H) :
    RangeAccepts M P a H layouts coeffs := by
  apply accepted_range_of_slices M P a H layouts values _ coeffs h
  intro mi
  exact (multiplicityResidue_eq_pruned M P a H layouts ha hc mi).trans (hs mi)

#print axioms scalarLayout_zero_of_support
#print axioms multiplicityResidue_eq_pruned
#print axioms accepted_range_of_pruned_slices
end SubmittedGenus.RawGraph.PackedAcceptance
