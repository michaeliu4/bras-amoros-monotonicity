import Results.Genus.FiniteComparison.Tables
import Results.Genus.FiniteComparison.Envelope
import Results.Genus.FiniteArithmetic.NExtension837.Acceptance
import Results.Genus.FiniteArithmetic.Reservoir.CapacityLookup837

namespace SubmittedGenus.FiniteComparison
open FiniteArithmetic FiniteArithmetic.Reservoir

def tableResidual (g : ℕ) : ℤ :=
  (upperFour g:ℤ)-nLookup837 g-nLookup837 (g-3)-nLookup837 (g-4)+
    (upperFour (g-1):ℤ)-nLookup837 (g-1)+(upperFive g:ℤ)

def ComparisonRange (start count : ℕ) : Prop := ∀ i : Fin count,
  0≤tableResidual (start+i.val) ∧
    tableResidual (start+i.val)≤(capacityLookup837 (start+i.val):ℤ)
instance (s n : ℕ) : Decidable (ComparisonRange s n) :=
  inferInstanceAs (Decidable (∀ i : Fin n,_))

lemma tableResidual_eq_source (g : ℕ) (hg : g<837) :
    tableResidual g=residualUpper g (upperFour g) (upperFour (g-1)) (upperFive g) := by
  unfold tableResidual residualUpper
  rw [nLookup837_card_correct g hg,nLookup837_card_correct (g-3) (by omega),
    nLookup837_card_correct (g-4) (by omega),nLookup837_card_correct (g-1) (by omega)]

lemma comparisonRange_apply {s k g : ℕ} (h : ComparisonRange s k)
    (hlo : s≤g) (hhi : g<s+k) :
    0≤tableResidual g ∧ tableResidual g≤(capacityLookup837 g:ℤ) := by
  have he : s+(g-s)=g := by omega
  simpa only [he] using h ⟨g-s,by omega⟩

#print axioms tableResidual_eq_source
end SubmittedGenus.FiniteComparison
