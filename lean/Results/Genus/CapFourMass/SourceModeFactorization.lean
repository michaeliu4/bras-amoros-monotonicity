import Results.Genus.CapFourMass.SourceModeFactors

/-! Exact finite regrouping of the actual source: core contractions precede
absolute values, and complete mode assignments are split by physical component. -/
namespace SubmittedGenus.CapFourMass.SourceCoreFactorization
open FixedPivot CarryLocalization
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

section Source
variable {r N d : ℕ} (hr : 0<r) (hd : 0<d) (hN : d<N) (hbig : 2*d<N)

/-- The two deleted pivots are the only weights outside the complete finite
core/mode contraction. -/
theorem sourceCoefficient_eq_core_mode_sum (b : CarryRepresentative N d hN→Bool) :
    sourceCoefficient r N d hN b=radius^8*
      ∑ x : CoreFree r (r+d)→State,freeCoreTerm radius x*sourceCarryFactor N d hN b*
        (∏ q : Fin d,sourcePortFactor hd hN (extendCore hr (show r<r+d by omega) x) b q) := by
  rw [sourceCoefficient_eq_port_product hd hN]
  rw [stableCore_sum_restrict hr (show r<r+d by omega) radius]
  rw [mul_left_comm]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr ?_ ?_
  · ext x
    simp
  · intro x _
    ring

/-- Each source coefficient is a product of its completed actual-component
core sums. The identity holds for every complete signed mode assignment. -/
theorem sourceCoefficient_components (b : CarryRepresentative N d hN→Bool) :
    sourceCoefficient r N d hN b=radius^8*
      ∏ c : SourceComponent r N d,∑ x : CoreAt hN c→State,
        componentModeTerm hr hd hN hbig c x (modeAssignmentEquiv hr hN hbig b c) := by
  rw [sourceCoefficient_eq_core_mode_sum hr hd hN]
  congr 1
  exact (ModeFubini.transported_coefficient (coreAssignmentEquiv hN)
    (modeAssignmentEquiv hr hN hbig) (componentModeTerm hr hd hN hbig)
    (fun x b => freeCoreTerm radius x*sourceCarryFactor N d hN b*
      (∏ q : Fin d,sourcePortFactor hd hN (extendCore hr (show r<r+d by omega) x) b q))
    (source_mode_term_factor hr hd hN hbig) b).trans
      (ModeFubini.coefficient_factor _ _)

/-- The complete absolute source-mode partition factors after, never before,
each component's full core contraction. All-negative modes are retained. -/
theorem sourceAbsolute_components :
    sourceAbsolute r N d hN=radius^8*
      ∏ c : SourceComponent r N d,∑ b : ModeFiber hr hN hbig c→Bool,
        |∑ x : CoreAt hN c→State,componentModeTerm hr hd hN hbig c x b| := by
  unfold sourceAbsolute
  simp_rw [sourceCoefficient_eq_core_mode_sum hr hd hN]
  exact ModeFubini.transported_pivot_absolute_factor (coreAssignmentEquiv hN)
    (modeAssignmentEquiv hr hN hbig) (componentModeTerm hr hd hN hbig)
    (fun x b => freeCoreTerm radius x*sourceCarryFactor N d hN b*
      (∏ q : Fin d,sourcePortFactor hd hN (extendCore hr (show r<r+d by omega) x) b q))
    (source_mode_term_factor hr hd hN hbig) radius

end Source
end
end SubmittedGenus.CapFourMass.SourceCoreFactorization
