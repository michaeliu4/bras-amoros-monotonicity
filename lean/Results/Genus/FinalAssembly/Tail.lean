import Results.Genus.FiniteArithmetic.Reservoir.CapacityBounds
import Results.Genus.Injection.MassExtraction
import Results.Genus.CapFiveMass.MassBound
import Results.Genus.TailComparison

/-! Exact submitted 836/837 assembly interface. The genuine cap-four mass and
finite exceptional-versus-capacity comparisons are explicit remaining premises.
No theorem in this file claims those certificates have been accepted. -/
namespace SubmittedGenus.FinalAssembly
open OriginalSources OriginalPopulations OriginalReservoir
open FiniteArithmetic.Reservoir TailComparison
noncomputable section

/-- All source and capacity bridges in the submitted analytic tail are closed;
only the actual genuine cap-four mass theorem remains as an input here. -/
theorem exceptional_lt_capacity_from_837
    (hs4 : Summable (fun n => (countFour n:ℝ)*z4^n))
    (hm4 : massFour z4<2024) (g : ℕ) (hg : 837≤g) :
    Fintype.card (SourceClass g .E)<originalCapacity g := by
  have hs5 : Summable (fun n => (CapFiveMass.count n:ℝ)*z5^n) :=
    CapFiveMass.mass_five.1
  have hm5 : CapFiveMass.mass z5<113 := CapFiveMass.mass_five.2
  have he := exceptional_mass_extraction g z4_pos (by norm_num [z4])
    z5_pos (by norm_num [z5]) hs4 hs5
  have he' : (Fintype.card (SourceClass g .E):ℝ)<2024/z4^g+113/z5^g :=
    he.trans_lt (add_lt_add (div_lt_div_of_pos_right hm4 (pow_pos z4_pos g))
      (div_lt_div_of_pos_right hm5 (pow_pos z5_pos g)))
  apply mass_tail_counts hg he'
  simpa only [FiniteArithmetic.Analytic.rho] using original_capacity_improved g (by omega)

/-- The genuine numerical-semigroup counting function is strictly increasing
from837 once the one remaining mass certificate is supplied. -/
theorem strict_growth_from_837_of_cap_four_mass
    (hs4 : Summable (fun n => (countFour n:ℝ)*z4^n))
    (hm4 : massFour z4<2024) (g : ℕ) (hg : 837≤g) :
    NumericalSemigroup.count g<NumericalSemigroup.count (g+1) := by
  have he := exceptional_lt_capacity_from_837 hs4 hm4 g hg
  have hf := original_fundamental_reservoir g (by omega)
  change NumericalSemigroup.count g+originalCapacity g ≤
    NumericalSemigroup.count (g+1)+Fintype.card (SourceClass g .E) at hf
  omega

/-- The exact two remaining certificate interfaces, with the submitted split
at836/837. Finite comparisons and cap-four mass are NOT asserted by this lemma. -/
theorem weak_growth_of_original_certificates
    (hs4 : Summable (fun n => (countFour n:ℝ)*z4^n))
    (hm4 : massFour z4<2024)
    (hfinite : ∀g,1≤g → g≤836 →
      Fintype.card (SourceClass g .E)≤originalCapacity g) :
    ∀g,NumericalSemigroup.count g≤NumericalSemigroup.count (g+1) := by
  intro g
  by_cases hz : g=0
  · subst g
    simp
  by_cases hg : g≤836
  · have he := hfinite g (by omega) hg
    have hf := original_fundamental_reservoir g (by omega)
    change NumericalSemigroup.count g+originalCapacity g ≤
      NumericalSemigroup.count (g+1)+Fintype.card (SourceClass g .E) at hf
    omega
  · exact (strict_growth_from_837_of_cap_four_mass hs4 hm4 g (by omega)).le

#print axioms weak_growth_of_original_certificates
end
end SubmittedGenus.FinalAssembly
