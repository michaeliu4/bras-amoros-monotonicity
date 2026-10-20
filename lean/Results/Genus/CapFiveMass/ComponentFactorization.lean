import Results.Genus.CapFiveMass.ComponentEvaluation
import Results.Genus.CapFiveMass.SourceSummation
import Results.Genus.CapFiveMass.Compression
import Results.Genus.RawGraph.ActualLayout

noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFiveMass
open RawGraph RawGraph.SourceModel RawGraph.Topology RawGraph.LayoutCompiler
open ActualComponent

set_option maxHeartbeats 2000000 in
/-- The actual-layout source polynomial and the actual mass component have
identical unary domains, consecutive constraints, closing edge and weights. -/
lemma fullComponentPolynomial_eq {m r p : ℕ} (hp : Parameters m r p 5)
    (c : Component m r p) :
    fullComponentPolynomial hp (Sum.inr c) = componentPolynomial c := by
  classical
  unfold fullComponentPolynomial componentPolynomial
  simp only [fullEdges, fullCycle, fullVertexEquiv_free]
  apply Finset.sum_congr rfl
  intro x _
  change (∏ j, vertexWeight r p 5 (vertex c j) (x j)) *
      (∏ j : Fin (edgeCount c), edgeWeight r p 5 (vertex c j.castSucc) (vertex c j.succ)
        (x j.castSucc) (x j.succ)) *
      (if (freeComponentOrder m r p c).cycle = true then edgeWeight r p 5
        (vertex c (Fin.last _)) (vertex c 0) (x (Fin.last _)) (x 0) else 1) = _
  unfold vertexWeight edgeWeight
  rw [RawGraph.Factorization.prod_gated_powers, RawGraph.Factorization.prod_gate]
  simp only [Finset.prod_const_one]
  unfold Allowed
  split_ifs <;> simp_all

/-- Exact full original raw source factorization at the submitted radius.
The two fixed fives contribute radius^10, and every other physical vertex
occurs in exactly one actual component. -/
lemma rawPartition_eq_pivot_component_product (q : PivotParameters) :
    rawPartition q radius = radius ^ 10 * allComponentMass q.m q.r q.p := by
  rw [rawPartition_eq_eval, rawPolynomial_eq_pivots_free q.valid]
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetProd]
  simp_rw [fullComponentPolynomial_eq q.valid, ← componentMass_eq_eval]
  rfl

/-- Actual source and analytic factors have now been linked. Only the two
purely combinatorial free/strong incidence inequalities remain as inputs. -/
lemma rawPartition_le_of_incidence_bounds (q : PivotParameters)
    (hu : totalEndpointCount q.m q.r q.p .free ≤ 2)
    (hstrong : q.r + q.p ≤ 2 * totalStrongCount q.m q.r q.p +
      totalEndpointCount q.m q.r q.p .strongLoop + 4) :
    rawPartition q radius ≤ geometricTerm (parameterEquiv q) := by
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
  have hx : mixedRoot ^ 2 = strongBound * carryBound :=
    Real.sq_sqrt (mul_nonneg norm_bound_order.1.le (norm_bound_order.1.trans norm_bound_order.2.1).le)
  have h := incidence_compression norm_bound_order.1 norm_bound_order.2.1.le alphabet_five_ge_carry
    mixedRoot_pos hx (totalEndpointCount q.m q.r q.p .free)
    (2 * totalStrongCount q.m q.r q.p + totalEndpointCount q.m q.r q.p .strongLoop)
    (2 * totalCarryCount q.m q.r q.p + totalEndpointCount q.m q.r q.p .carryLoop)
    i j l hu hs htotal (allComponentMass_sq_le q.valid)
  rw [rawPartition_eq_pivot_component_product]
  calc
    radius ^ 10 * allComponentMass q.m q.r q.p ≤ radius ^ 10 *
        (alphabetMass 5 radius / mixedRoot * strongBound ^ i * mixedRoot ^ j * carryBound ^ l) :=
      mul_le_mul_of_nonneg_left h (pow_nonneg radius_bounds.1.le _)
    _ = geometricTerm (parameterEquiv q) := by unfold geometricTerm; dsimp [i, j, l]; ring

end SubmittedGenus.CapFiveMass
