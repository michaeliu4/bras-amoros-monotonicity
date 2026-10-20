import Results.Genus.CapFourMass.TaggedModeEvaluation
import Results.Genus.CapFourMass.CarryRunExponents

/-! Exact signed contraction of each retained canonical carry run. Surviving
core ports absorb one eigenvalue and divide by their already-paid half-weight;
a deleted pivot gives a free endpoint and a fixed class gives its loop endpoint. -/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFourMass.CarryLocalization
open FixedPivot
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Unit coordinate boundary divided by its physical half-weight. -/
def corePortBoundary (v : State) : State→ℝ := fun i => if i=v then (halfWeight v)⁻¹ else 0
lemma corePortBoundary_dot (v : State) (q : State→ℝ) :
    corePortBoundary v ⬝ᵥ q=q v/halfWeight v := by
  simp [corePortBoundary,dotProduct,div_eq_mul_inv,mul_comm]
lemma dot_corePortBoundary (v : State) (q : State→ℝ) :
    q ⬝ᵥ corePortBoundary v=q v/halfWeight v := by rw [dotProduct_comm,corePortBoundary_dot]

section Run
variable (N d : ℕ) (hN : d<N) (a : CarryRepresentative N d hN)

def retainedLeft (v : State) : State→ℝ :=
  if a.val.val+1=d then freeBoundary else corePortBoundary v

def retainedRight (v : State) : State→ℝ :=
  if a.val=portPartner N d hN a.val then loopBoundary else corePortBoundary v

def initialPortMode (j : Mode) (v : State) : ℝ :=
  if a.val.val+1=d then freeBoundary ⬝ᵥ modeVector j
  else modeRoot j*modeVector j v/halfWeight v

def terminalPortMode (j : Mode) (v : State) : ℝ :=
  if a.val=portPartner N d hN a.val then 1
  else modeRoot j*modeVector j v/halfWeight v

/-- This is the canonical tail eigenfactor and its original signed port factors. -/
def retainedSourceMode (j : Mode) (left right : State) : ℝ :=
  modeRoot j^(carryTailSize N d hN a-1)*
    (if a.val=portPartner N d hN a.val then loopBoundary ⬝ᵥ modeVector j else 1)*
    initialPortMode N d hN a j left*terminalPortMode N d hN a j right

lemma retained_boundary_factor (hbig : 2*d<N) (j : Mode) (left right : State) :
    ((retainedLeft N d hN a left) ⬝ᵥ modeVector j)*
      modeRoot j^(freeCarrySize N d hN a-1)*
      (modeVector j ⬝ᵥ retainedRight N d hN a right)=
      retainedSourceMode N d hN a j left right := by
  rw [freeCarry_mode_power N d hN hbig a]
  by_cases hf : a.val=portPartner N d hN a.val
  · rw [survivingPorts_fixed N d hN a hf]
    by_cases hp : a.val.val+1=d
    · simp only [retainedLeft,retainedRight,retainedSourceMode,initialPortMode,terminalPortMode,
        if_pos hp,if_pos hf,pow_zero,mul_one]
      rw [dotProduct_comm (modeVector j) loopBoundary]
      ring
    · simp only [retainedLeft,retainedRight,retainedSourceMode,initialPortMode,terminalPortMode,
        if_neg hp,if_pos hf,pow_one,mul_one,corePortBoundary_dot]
      rw [dotProduct_comm (modeVector j) loopBoundary]
      ring
  · rw [survivingPorts_paired N d hN a hf]
    by_cases hp : a.val.val+1=d
    · simp only [retainedLeft,retainedRight,retainedSourceMode,initialPortMode,terminalPortMode,
        if_pos hp,if_neg hf,pow_one,mul_one,dot_corePortBoundary]
      ring
    · simp only [retainedLeft,retainedRight,retainedSourceMode,initialPortMode,terminalPortMode,
        if_neg hp,if_neg hf,mul_one,corePortBoundary_dot,dot_corePortBoundary]
      ring

/-- Every positive-edge retained run contracts to its original canonical signed
factor. This theorem does not reinterpret a zero power as a mode projector. -/
theorem retained_positive_mode (hbig : 2*d<N) (j : Mode) (left right : State)
    (hn : 1 ≤ freeCarrySize N d hN a-1) :
    retainedLeft N d hN a left ⬝ᵥ
      (((modeRoot j • modeProjector j)^(freeCarrySize N d hN a-1))*ᵥ
        retainedRight N d hN a right)=retainedSourceMode N d hN a j left right := by
  rw [mode_power_path _ _ hn]
  exact retained_boundary_factor N d hN a hbig j left right

end Run
end SubmittedGenus.CapFourMass.CarryLocalization
