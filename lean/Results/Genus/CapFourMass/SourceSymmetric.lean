import Results.Genus.CapFourMass.SourceMixed
import Results.Genus.CapFourMass.SpectralBlocks

/-! Exact symmetric convention for every complete carry assignment, with the
fixed strong-core contraction performed before taking its absolute value. -/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFourMass
open FixedPivot

def choiceMode (b : Bool) : Mode := if b then 1 else 0

def symmetricSourceCoefficient (r N d : ℕ) (hN : d<N)
    (choice : CarryRepresentative N d hN → Bool) : ℝ :=
  ∑ x : Fin (r+d) → Fin 5,
    Polynomial.eval₂ (Nat.castRingHom ℝ) radius (stableCoreTerm r (r+d) x)*
    ∏ c : CarryRepresentative N d hN,
      (modeRoot (choiceMode (choice c)))^(carryTailSize N d hN c-1)*
        (sourceHalf (fun v => if canonicalStartAllowed x c v then 1 else 0) ⬝ᵥ modeVector (choiceMode (choice c)))*
        (modeVector (choiceMode (choice c)) ⬝ᵥ sourceHalf (fun v => if canonicalFinishAllowed x c v then 1 else 0))

/-- The positive diagonal change of basis and the eigenvector rescaling
commute with the entire core contraction for each complete assignment. -/
theorem sourceCoefficient_eq_symmetric (r N d : ℕ) (hN : d<N)
    (choice : CarryRepresentative N d hN → Bool) :
    sourceCoefficient r N d hN choice=symmetricSourceCoefficient r N d hN choice := by
  unfold sourceCoefficient sourceModeCoefficient symmetricSourceCoefficient
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  apply Finset.prod_congr rfl
  intro c _
  cases hc : choice c
  · simpa only [hc,choiceMode,Bool.false_eq_true,ite_false,modeRoot,modeVector,Matrix.cons_val_zero,
      canonicalModeAmplitude] using rational_positive_amplitude (carryTailSize N d hN c-1)
        (fun v => if canonicalStartAllowed x c v then 1 else 0)
        (fun v => if canonicalFinishAllowed x c v then 1 else 0)
  · simpa only [hc,choiceMode,ite_true,modeRoot,modeVector,Matrix.cons_val_one,Matrix.cons_val_zero,
      canonicalModeAmplitude] using rational_negative_amplitude (carryTailSize N d hN c-1)
        (fun v => if canonicalStartAllowed x c v then 1 else 0)
        (fun v => if canonicalFinishAllowed x c v then 1 else 0)

/-- Absolute values are taken after the finite source contraction, so this is
an equality of the original convention, rather than an enlarged spinwise sum. -/
theorem sourceAbsolute_eq_symmetric (r N d : ℕ) (hN : d<N) :
    sourceAbsolute r N d hN=
      ∑ choice : CarryRepresentative N d hN → Bool,|symmetricSourceCoefficient r N d hN choice| := by
  unfold sourceAbsolute
  exact Finset.sum_congr rfl (fun choice _ => congrArg abs (sourceCoefficient_eq_symmetric r N d hN choice))

theorem sourceMixed_eq_symmetric (r N d : ℕ) (hN : d<N) :
    sourceMixed r N d hN=
      ∑ choice : CarryRepresentative N d hN → Bool,
        if choice=(fun _ => false) then 0 else |symmetricSourceCoefficient r N d hN choice| := by
  unfold sourceMixed
  apply Finset.sum_congr rfl
  intro choice _
  rw [sourceCoefficient_eq_symmetric]

end SubmittedGenus.CapFourMass
