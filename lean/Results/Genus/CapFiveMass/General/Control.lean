import Results.Genus.CapFiveMass.MassBound

/-! Exact analytic hypotheses of the submitted general multiple-five lemma.
The fourth norm inequalities are written as equivalent fourth-trace bounds.
The radius is positive, as in the surrounding weighted-mass argument. -/

noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFiveMass.General

structure Control where
  z : ℝ
  a : ℝ
  b : ℝ
  z_pos : 0 < z
  a_pos : 0 < a
  a_lt_b : a < b
  b_lt_one : b < 1
  b_le_mass : b ≤ alphabetMass 5 z
  strong_trace : fourthTrace 5 z ≤ a ^ 4
  carry_trace : fourthTrace 4 z ≤ b ^ 4
  strong_endpoint : strongEndpoint z ≤ a
  carry_endpoint : carryEndpoint z ≤ b

lemma Control.b_pos (H : Control) : 0 < H.b := H.a_pos.trans H.a_lt_b
lemma Control.a_lt_one (H : Control) : H.a < 1 := H.a_lt_b.trans H.b_lt_one

def strongTransfer (H : Control) : MatrixBounds.Controlled (ι := State) where
  matrix := thresholdMatrix 5 H.z
  bound := H.a
  bound_nonneg := H.a_pos.le
  symmetric := threshold_symmetric 5 H.z
  trace_le := by
    rw [threshold_trace_fourth H.z_pos.le, ambient_trace_five]
    exact H.strong_trace

def carryTransfer (H : Control) : MatrixBounds.Controlled (ι := State) where
  matrix := thresholdMatrix 4 H.z
  bound := H.b
  bound_nonneg := H.b_pos.le
  symmetric := threshold_symmetric 4 H.z
  trace_le := by
    rw [threshold_trace_fourth H.z_pos.le, ambient_trace_four]
    exact H.carry_trace

def strongTransferSix (H : Control) := extendControlled (strongTransfer H)
def carryTransferSix (H : Control) := extendControlled (carryTransfer H)

def endpointBound (H : Control) : EndpointKind → ℝ
  | .free => alphabetMass 5 H.z
  | .strongLoop => H.a
  | .carryLoop => H.b

lemma endpoint_energy_le (H : Control) (kind : EndpointKind) :
    MatrixBounds.vectorEnergy (endpointVector kind H.z) ≤ endpointBound H kind := by
  rw [endpoint_energy kind H.z_pos.le]
  cases kind
  · rfl
  · exact H.strong_endpoint
  · exact H.carry_endpoint

lemma endpointBound_nonneg (H : Control) (kind : EndpointKind) : 0 ≤ endpointBound H kind :=
  (MatrixBounds.vectorEnergy_nonneg _).trans (endpoint_energy_le H kind)

lemma endpointSix_energy_le (H : Control) (kind : EndpointKind) :
    MatrixBounds.vectorEnergy (endpointVectorSix kind H.z) ≤ endpointBound H kind := by
  rw [endpointVectorSix, zeroExtendVector_energy]
  exact endpoint_energy_le H kind

/-- Exact supplied constants satisfy the same general hypotheses. -/
def submittedControl : Control where
  z := radius
  a := strongBound
  b := carryBound
  z_pos := radius_bounds.1
  a_pos := norm_bound_order.1
  a_lt_b := norm_bound_order.2.1
  b_lt_one := norm_bound_order.2.2
  b_le_mass := alphabet_five_ge_carry
  strong_trace := fourthTrace_five_lt.le
  carry_trace := fourthTrace_four_lt.le
  strong_endpoint := strong_endpoint_le
  carry_endpoint := carry_endpoint_le

end SubmittedGenus.CapFiveMass.General
