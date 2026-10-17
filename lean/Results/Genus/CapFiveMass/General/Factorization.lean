import Results.Genus.CapFiveMass.General.Evaluation
import Results.Genus.CapFiveMass.General.Geometric

noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFiveMass.General
open RawGraph RawGraph.SourceModel RawGraph.Topology RawGraph.Transfer LocalSource MatrixSource ActualComponent RawGraph.LayoutCompiler

lemma rawPartition_eq_pivot_component_product (H : Control) (q : PivotParameters) :
    rawPartition q H.z = H.z ^ 10 * allComponentMass H q.m q.r q.p := by
  rw [rawPartition_eq_eval, rawPolynomial_eq_pivots_free q.valid]
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetProd]
  simp_rw [fullComponentPolynomial_eq q.valid, ← componentMass_eq_eval H]
  rfl

/-- Actual source and analytic factors have now been linked. Only the two
purely combinatorial free/strong incidence inequalities remain as inputs. -/

lemma rawPartition_le_of_incidence_bounds (H : Control) (q : PivotParameters)
    (hu : totalEndpointCount q.m q.r q.p .free ≤ 2)
    (hstrong : q.r + q.p ≤ 2 * totalStrongCount q.m q.r q.p +
      totalEndpointCount q.m q.r q.p .strongLoop + 4) :
    rawPartition q H.z ≤ geometricTerm H (parameterEquiv q) := by
  have hparam := pivotTriple_reconstruct q.valid
  have hcount := total_incidence_count q.m q.r q.p
  rw [freeVertex_card q.valid] at hcount
  let i := (parameterEquiv q).1
  let j := (parameterEquiv q).2.1
  let l := (parameterEquiv q).2.2
  have hri : q.r = 1 + i := hparam.1
  have hpj : q.p = 2 + i + j := hparam.2.1
  have hml : q.m = 3 + i + j + l := hparam.2.2
  have htotal : totalEndpointCount q.m q.r q.p .free +
      (2 * totalStrongCount q.m q.r q.p + totalEndpointCount q.m q.r q.p .strongLoop) +
      (2 * totalCarryCount q.m q.r q.p + totalEndpointCount q.m q.r q.p .carryLoop) =
      2 * (i + j + l) := by omega
  have hs : 2 * i + j ≤ 2 * totalStrongCount q.m q.r q.p +
      totalEndpointCount q.m q.r q.p .strongLoop + 1 := by omega
  have hx : mixedRoot H ^ 2 = H.a * H.b :=
    Real.sq_sqrt (mul_nonneg H.a_pos.le (H.a_pos.trans H.a_lt_b).le)
  have h := incidence_compression H.a_pos H.a_lt_b.le H.b_le_mass
    (mixedRoot_pos H) hx (totalEndpointCount q.m q.r q.p .free)
    (2 * totalStrongCount q.m q.r q.p + totalEndpointCount q.m q.r q.p .strongLoop)
    (2 * totalCarryCount q.m q.r q.p + totalEndpointCount q.m q.r q.p .carryLoop)
    i j l hu hs htotal (allComponentMass_sq_le H q.valid)
  rw [rawPartition_eq_pivot_component_product H]
  calc
    H.z ^ 10 * allComponentMass H q.m q.r q.p ≤ H.z ^ 10 *
        (alphabetMass 5 H.z / mixedRoot H * H.a ^ i * mixedRoot H ^ j * H.b ^ l) :=
      mul_le_mul_of_nonneg_left h (pow_nonneg H.z_pos.le _)
    _ = geometricTerm H (parameterEquiv q) := by unfold geometricTerm; dsimp [i, j, l]; ring

end SubmittedGenus.CapFiveMass.General
