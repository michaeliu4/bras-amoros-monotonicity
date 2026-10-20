import Results.Genus.RawGraph.PackedAcceptance.SupportPrunedSlices

/-! Abstract source-exact scalar providers and finite chunk assembly.
Optimized branch evaluators supply only their original scalar equality.
Chunk cover/partition and concrete numeric equalities remain explicit premises. -/
namespace SubmittedGenus.RawGraph.PackedAcceptance
open LayoutCompiler Packing
open scoped BigOperators

def sourceValuePrunedMultiplicity (M P a H : ℕ)
    (value : Triple M P→ZMod (modulus H)) (mi : Fin (M-2)) : ZMod (modulus H) :=
  ∑pi : Fin (min P (mi.val+2)-1),
    if 2*H<(a-1)*(mi.val+3)+(pi.val+2)+1 then 0 else
      ∑ri : Fin (pi.val+1),value ⟨mi,pi,ri⟩

lemma sourceValuePrunedMultiplicity_eq (M P a H : ℕ)
    (layouts : (t : Triple M P)→Layout t.m) (value : Triple M P→ZMod (modulus H))
    (hv : ∀t,value t=scalarLayout (layouts t) t.r t.p a (digitBase H:ZMod (modulus H)))
    (mi : Fin (M-2)) : sourceValuePrunedMultiplicity M P a H value mi=
      prunedMultiplicityResidue M P a H layouts mi := by
  simp only [sourceValuePrunedMultiplicity,prunedMultiplicityResidue,hv,Triple.r,Triple.p]

theorem accepted_range_of_source_value_pruned_chunks (M P a H : ℕ)
    (layouts : (t : Triple M P)→Layout t.m) (ha : a=4 ∨ a=5)
    (hc : ∀t,Covers (layouts t) t.r t.p a)
    (value : Triple M P→ZMod (modulus H))
    (hv : ∀t,value t=scalarLayout (layouts t) t.r t.p a (digitBase H:ZMod (modulus H)))
    (chunkCount : Fin (M-2)→ℕ)
    (chunks : (mi : Fin (M-2))→Fin (chunkCount mi)→ZMod (modulus H))
    (hs : ∀mi,sourceValuePrunedMultiplicity M P a H value mi=∑j,chunks mi j)
    (coeffs : Fin (H+1)→ℕ)
    (h : (∑mi,∑j,chunks mi j).val=pack (digitBase H) coeffs ∧ ∀i,coeffs i<digitBase H) :
    RangeAccepts M P a H layouts coeffs := by
  apply accepted_range_of_pruned_slices M P a H layouts ha hc (fun mi=>∑j,chunks mi j) _ coeffs h
  intro mi
  exact (sourceValuePrunedMultiplicity_eq M P a H layouts value hv mi).symm.trans (hs mi)

#print axioms sourceValuePrunedMultiplicity_eq
#print axioms accepted_range_of_source_value_pruned_chunks
end SubmittedGenus.RawGraph.PackedAcceptance
