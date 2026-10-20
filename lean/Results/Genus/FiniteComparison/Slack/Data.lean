import Results.Genus.FiniteComparison.Acceptance
namespace SubmittedGenus.FiniteComparison.Slack
open FiniteArithmetic.Reservoir

def delta (g : ℕ) : ℤ := (capacityLookup837 g:ℤ)-tableResidual g
def minimumCapacityNumerator : ℤ := 628703649216298849714026665348117889703045087949284018645808327741153897312560618089227488876051856788383886443483296122067120
def minimumCapacityDenominator : ℕ := 3495479555312401446242963164222906107654733186592129604073814779424482821534022818445917524798530959338139917042785917069524726

/-- Exact integer cross-products avoid all numerical rounding. -/
def Row (g : ℕ) : Prop :=
  1≤delta g ∧
  15028705*(Nat.fastFib g:ℤ)≤33489287*delta g ∧
  minimumCapacityNumerator*(capacityLookup837 g:ℤ)≤(minimumCapacityDenominator:ℤ)*delta g ∧
  (g≠1 → g≠2 → 2≤delta g)
instance (g : ℕ) : Decidable (Row g) := inferInstanceAs (Decidable (_∧_∧_∧_))
def CheckedRange (start count : ℕ) : Prop := ∀ i:Fin count,Row (start+i.val)
instance (s n : ℕ) : Decidable (CheckedRange s n) := inferInstanceAs (Decidable (∀ i:Fin n,_))
theorem checkedRange_apply {s k g:ℕ} (h:CheckedRange s k) (hlo:s≤g) (hhi:g<s+k) : Row g := by
  have he : s+(g-s)=g := by omega
  simpa only [he] using h ⟨g-s,by omega⟩

/-- This is slack for the original literal envelope and original capacity;
it makes no claim that the raw graph tables have been source-accepted. -/
theorem delta_eq_source (g:ℕ) (hg:g<837) :
    delta g=(originalCapacity g:ℤ)-residualUpper g (upperFour g) (upperFour (g-1)) (upperFive g) := by
  unfold delta
  rw [capacityLookup837_correct g hg,tableResidual_eq_source g hg]
end SubmittedGenus.FiniteComparison.Slack
