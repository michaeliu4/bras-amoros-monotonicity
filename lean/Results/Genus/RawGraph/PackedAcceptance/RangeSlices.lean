import Results.Genus.RawGraph.PackedAcceptance.Aggregation

/-! Multiplicity-sliced complete range acceptance. Each scalar shard is
checked separately; a small finite sum joins exactly the original range. -/
namespace SubmittedGenus.RawGraph.PackedAcceptance
open scoped BigOperators
open LayoutCompiler Packing

def multiplicityResidue (M P a H : ℕ) (layouts : (t : Triple M P)→Layout t.m)
    (mi : Fin (M-2)) : ZMod (modulus H) :=
  ∑pi : Fin (min P (mi.val+2)-1),∑ri : Fin (pi.val+1),
    scalarLayout (layouts ⟨mi,pi,ri⟩) (ri.val+1) (pi.val+2) a (digitBase H:ZMod (modulus H))

lemma rangeResidue_eq_multiplicity_sum (M P a H : ℕ)
    (layouts : (t : Triple M P)→Layout t.m) :
    rangeResidue M P a H layouts=(∑mi,multiplicityResidue M P a H layouts mi).val := by
  unfold rangeResidue multiplicityResidue
  congr 1
  simp only [Triple,Fintype.sum_sigma,Triple.r,Triple.p]

theorem rangeResidue_eq_accepted_slices (M P a H : ℕ)
    (layouts : (t : Triple M P)→Layout t.m) (values : Fin (M-2)→ZMod (modulus H))
    (hs : ∀mi,multiplicityResidue M P a H layouts mi=values mi) :
    rangeResidue M P a H layouts=(∑mi,values mi).val := by
  rw [rangeResidue_eq_multiplicity_sum]
  congr 1
  exact Finset.sum_congr rfl (fun mi _=>hs mi)

theorem accepted_range_of_slices (M P a H : ℕ)
    (layouts : (t : Triple M P)→Layout t.m) (values : Fin (M-2)→ZMod (modulus H))
    (hs : ∀mi,multiplicityResidue M P a H layouts mi=values mi)
    (coeffs : Fin (H+1)→ℕ)
    (h : (∑mi,values mi).val=pack (digitBase H) coeffs ∧ ∀i,coeffs i<digitBase H) :
    RangeAccepts M P a H layouts coeffs :=
  ⟨(rangeResidue_eq_accepted_slices M P a H layouts values hs).trans h.1,h.2⟩

#print axioms rangeResidue_eq_multiplicity_sum
#print axioms rangeResidue_eq_accepted_slices
#print axioms accepted_range_of_slices
end SubmittedGenus.RawGraph.PackedAcceptance
