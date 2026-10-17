import Results.Genus.Injection.RawEnvelope

/-! Signed integer residual comparison. Natural subtraction is justified by
actual disjoint source exclusions before it is converted to integer arithmetic. -/
noncomputable section
namespace SubmittedGenus.FiniteComparison
open OriginalPopulations OriginalSources FiniteArithmetic
attribute [local instance] Classical.propDecidable

lemma exclusions_le_raw (g : ℕ) :
    Fintype.card (NWords g)+Fintype.card (NWords (g-3))+Fintype.card (NWords (g-4)) ≤ rawFourCount g := by
  have hd : Disjoint (@RawNoOnePred g) (@RawFinalOnePred g) :=
    fun f hn hf w hw => raw_exclusions_disjoint g w (hn w hw) (hf w hw)
  have hc := Fintype.card_subtype_le (fun w : RawFourAt g => RawNoOnePred w ∨ RawFinalOnePred w)
  rw [Fintype.card_subtype_or_disjoint _ _ hd] at hc
  have hn : Fintype.card {w : RawFourAt g // RawNoOnePred w} = Fintype.card (RawNoOneAt g) :=
    Fintype.card_congr (Equiv.refl _)
  have hf : Fintype.card {w : RawFourAt g // RawFinalOnePred w} = Fintype.card (RawFinalOneAt g) :=
    Fintype.card_congr (Equiv.refl _)
  rw [hn,hf,rawNoOne_card,rawFinalOne_card] at hc
  change _ ≤ rawFourCount g at hc
  omega

/-- Exact original residual expression, with subtraction in the integers. -/
def residualUpper (g Ug Uprev Vg : ℕ) : ℤ :=
  (Ug:ℤ)-Fintype.card (NWords g)-Fintype.card (NWords (g-3))-
    Fintype.card (NWords (g-4))+(Uprev:ℤ)-Fintype.card (NWords (g-1))+(Vg:ℤ)

lemma exceptional_le_integer_envelope (g Ug Uprev Vg : ℕ)
    (hU : rawFourCount g ≤ Ug) (hUp : rawFourCount (g-1) ≤ Uprev)
    (hV : CapFiveMass.count g ≤ Vg) :
    (Fintype.card (SourceClass g .E):ℤ) ≤ residualUpper g Ug Uprev Vg := by
  have he := raw_envelope_upper g Ug Uprev Vg hU hUp hV
  have h1 := exclusions_le_raw g
  have h2 := exclusions_le_raw (g-1)
  unfold residualUpper
  omega

/-- Concrete comparison acceptance is a separate premise, never inferred
from hashes or from the existence of the supplied coefficient tables. -/
theorem finite_capacity_of_integer_comparison (g Ug Uprev Vg L : ℕ)
    (hU : rawFourCount g ≤ Ug) (hUp : rawFourCount (g-1) ≤ Uprev)
    (hV : CapFiveMass.count g ≤ Vg)
    (hcheck : residualUpper g Ug Uprev Vg ≤ (L:ℤ)) :
    Fintype.card (SourceClass g .E) ≤ L := by
  have h := exceptional_le_integer_envelope g Ug Uprev Vg hU hUp hV
  omega

#print axioms finite_capacity_of_integer_comparison
end SubmittedGenus.FiniteComparison
