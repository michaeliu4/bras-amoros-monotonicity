import Results.Genus.FiniteArithmetic.Reservoir.FiniteAcceptance
import Results.Genus.Injection.ReservoirSources.Assembly

namespace SubmittedGenus.FiniteArithmetic.Reservoir
open OriginalReservoir OriginalMaps OriginalSources Analytic SubmittedGenus.TailComparison
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The submitted exact integer L, with binary rounding and separate
nonbinary clipping already tied to genuine unused targets. -/
def originalCapacity (g : ℕ) : ℕ :=
  max ((12*Nat.fib g+24)/25) (Nat.fib g-originalDemand g)+nonbinaryLowerBound g

/-- Original constant capacity bound, after all finite and infinite
nonbinary obligations have been discharged. -/
theorem original_capacity_constant (g : ℕ) (hg : 305≤g) :
    2841*Nat.fib g ≤ 1000*originalCapacity g := by
  have hn := original_nonbinary_all g hg
  have hd := originalDemand_sharp g (by omega)
  have hm := le_max_right ((12*Nat.fib g+24)/25) (Nat.fib g-originalDemand g)
  unfold originalCapacity
  omega

/-- Original refined capacity estimate, retaining the actual W decay term. -/
theorem original_capacity_improved (g : ℕ) (hg : 305≤g) :
    1-50*rStar^2/(rho*rStar)^g+927/500 ≤
      (originalCapacity g:ℝ)/(Nat.fib g:ℝ) := by
  have hnN := original_nonbinary_all g hg
  have hdN := originalDemand_sharp g (by omega)
  have hm := le_max_right ((12*Nat.fib g+24)/25) (Nat.fib g-originalDemand g)
  have hlN : Nat.fib g+nonbinaryLowerBound g ≤ originalCapacity g+originalDemand g := by
    unfold originalCapacity
    omega
  have hl : (Nat.fib g:ℝ)+(nonbinaryLowerBound g:ℝ) ≤
      (originalCapacity g:ℝ)+(originalDemand g:ℝ) := by exact_mod_cast hlN
  have hn : (927:ℝ)*(Nat.fib g:ℝ) ≤ 500*(nonbinaryLowerBound g:ℝ) := by exact_mod_cast hnN
  have hw := original_W_decay g (by omega)
  have he : realCoeff capacityW g=(originalDemand g:ℝ) := by
    unfold realCoeff
    rw [←originalDemand_cast]
    norm_cast
  rw [he] at hw
  have hf : 0<(Nat.fib g:ℝ) := by exact_mod_cast Nat.fib_pos.mpr (by omega : 0<g)
  have hw' := (div_lt_iff₀ hf).mp hw
  apply (le_div_iff₀ hf).mpr
  nlinarith

/-- Both original quantitative estimates apply to one actual unused-low
reservoir, not merely to a formal coefficient expression. -/
theorem original_unused_low_capacity (g : ℕ) (hg : 305≤g) :
    ∃ fresh : DISources g ↪ BinaryEndTwo g,
      ∃ hreserved : ∀ di b,fresh di≠BReserved g b,
        originalCapacity g ≤ Fintype.card (UnusedLow g fresh hreserved) ∧
        2841*Nat.fib g ≤ 1000*Fintype.card (UnusedLow g fresh hreserved) ∧
        1-50*rStar^2/(rho*rStar)^g+927/500 ≤
          (Fintype.card (UnusedLow g fresh hreserved):ℝ)/(Nat.fib g:ℝ) := by
  obtain ⟨fresh,hreserved,h⟩ := original_low_supply g (by omega)
  change originalCapacity g ≤ Fintype.card (UnusedLow g fresh hreserved) at h
  refine ⟨fresh,hreserved,h,?_,?_⟩
  · exact (original_capacity_constant g hg).trans (Nat.mul_le_mul_left 1000 h)
  · apply (original_capacity_improved g hg).trans
    exact div_le_div_of_nonneg_right (by exact_mod_cast h) (by positivity)

/-- The original constant capacity inserted into the genuine-semigroup
fundamental counting inequality, with the exceptional population retained. -/
theorem original_fundamental_constant (g : ℕ) (hg : 305≤g) :
    1000*NumericalSemigroup.count g+2841*Nat.fib g ≤
      1000*(NumericalSemigroup.count (g+1)+Fintype.card (SourceClass g .E)) := by
  have h := original_fundamental_reservoir g (by omega)
  change NumericalSemigroup.count g+originalCapacity g ≤
    NumericalSemigroup.count (g+1)+Fintype.card (SourceClass g .E) at h
  have hc := original_capacity_constant g hg
  omega

#print axioms original_capacity_constant
#print axioms original_capacity_improved
#print axioms original_unused_low_capacity
#print axioms original_fundamental_constant
end
end SubmittedGenus.FiniteArithmetic.Reservoir
