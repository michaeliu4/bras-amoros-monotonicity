import Results.Genus.CapFourMass.PathCodeBounds
import Results.Genus.CapFourMass.EndpointProduct
import Results.Genus.CapFourMass.RestrictedCounts

/-! The original all-parameter cap-four raw-graph envelope, derived from the
actual source partition and its computed maximal strong/carry runs. -/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFourMass.ActualComponent
open RawGraph RawGraph.Topology CapFiveMass.MatrixBounds

/-- An actual component's edge cost, with E counted as a strong edge and its
single restricted replacement recorded separately. -/
def edgeCost {m r p : ℕ} (c : Component m r p) : ℝ :=
  strongBound^(strongLength (sourceWord c))*
    sigma^(restrictedLength (sourceWord c))*lam^(carryLength (sourceWord c))

lemma edgeCost_nonneg {m r p : ℕ} (c : Component m r p) : 0≤edgeCost c :=
  mul_nonneg (mul_nonneg (pow_nonneg strongBound_pos.le _)
    (pow_nonneg sigma_bounds.1.le _)) (pow_nonneg lam_pos.le _)

/-- Source-exact path/cycle compilation discharges the run-layout premise of
the analytic estimates for every physical component. -/
theorem componentMass_le_edgeCost {m r p : ℕ} (hp : Parameters m r p 4)
    (c : Component m r p) : componentMass c≤endpointFactor c*edgeCost c := by
  cases hc : (freeComponentOrder m r p c).cycle with
  | false =>
    obtain ⟨q,hm,hs,hc',he⟩:=actual_path_code_counts hp c hc
    rw [hm]
    have hh:=q.path_le (domainHalf c 0) (domainHalf c (Fin.last _))
    rw [hs,hc',he] at hh
    simpa only [endpointFactor,edgeCost,sourceWord,hc,Bool.false_eq_true,if_false] using hh
  | true =>
    obtain ⟨bs,hbs,hm,hs,hc',he⟩:=actual_cycle_coupled_counts hp c hc
    have hb : ((bs.map CoupledRun.matrix).prod).trace ≤
        (bs.map (fun b => b.dominated.bound)).prod := by
      cases bs with
      | nil => contradiction
      | cons b bs => simpa only [List.map_cons,List.prod_cons] using coupled_cycle_le b bs
    rw [coupled_bounds_product,hs,hc',he] at hb
    rw [hm]
    simpa only [endpointFactor,edgeCost,sourceWord,hc,if_true,one_mul] using hb

lemma edgeCost_product (m r p : ℕ) :
    (∏ c : Component m r p,edgeCost c)=
      strongBound^(totalStrongLength m r p)*sigma^(totalRestrictedLength m r p)*
        lam^(totalCarryLength m r p) := by
  simp only [edgeCost,Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,
    totalStrongLength,totalRestrictedLength,totalCarryLength]

/-- Full source components are multiplied only after their exact physical
vertex partition and endpoint accounting have been proved. -/
theorem component_product_le {m r p : ℕ} (hp : Parameters m r p 4) :
    (∏ c : Component m r p,componentMass c) ≤
      alphabetMass*(strongBound^(totalStrongLength m r p)*
        sigma^(totalRestrictedLength m r p)*lam^(totalCarryLength m r p)) := by
  calc
    _ ≤ ∏ c : Component m r p,endpointFactor c*edgeCost c :=
      Finset.prod_le_prod (fun c _ => componentMass_nonneg c)
        (fun c _ => componentMass_le_edgeCost hp c)
    _ = (∏ c : Component m r p,endpointFactor c)*
        (strongBound^(totalStrongLength m r p)*sigma^(totalRestrictedLength m r p)*
          lam^(totalCarryLength m r p)) := by
      rw [Finset.prod_mul_distrib,edgeCost_product]
    _ ≤ _ := mul_le_mul_of_nonneg_right (actual_endpoint_product_le hp)
      (mul_nonneg (mul_nonneg (pow_nonneg strongBound_pos.le _)
        (pow_nonneg sigma_bounds.1.le _)) (pow_nonneg lam_pos.le _))

lemma total_edges_le_free_vertices {m r p : ℕ} (hp : Parameters m r p 4) :
    totalStrongLength m r p+totalCarryLength m r p≤m-3 := by
  have hh:=CapFiveMass.ActualComponent.total_incidence_count m r p
  rw [freeVertex_card hp] at hh
  rw [total_strong_eq,total_carry_eq]
  omega

/-- The paper's exact exponents, including the p=2r deleted-loop corner. -/
def sourceEnvelope (m r p : ℕ) : ℝ :=
  radius^8*alphabetMass*lambdaBound^(m-3)*
    eta^((r-1)/2+(p-1)/2-(if p=2*r then 0 else 1))*sigma^((p-1)/2-r)

/-- Original cap-four raw-graph envelope for every admissible parameter triple.
This theorem concerns the signed, nonnegative source partition itself; the
separate absolute complete-mode partition requires its own source comparison. -/
theorem raw_eval_le_sourceEnvelope {m r p : ℕ} (hp : Parameters m r p 4) :
    Polynomial.eval₂ (Nat.castRingHom ℝ) radius (rawPolynomial m r p 4)≤
      sourceEnvelope m r p := by
  rw [raw_eval_eq_component_product hp]
  have hcost:=edge_budget_bound (totalStrongLength m r p) (totalRestrictedLength m r p)
    (totalCarryLength m r p) (m-3) (total_edges_le_free_vertices hp)
  have hh:=(component_product_le hp).trans
    (mul_le_mul_of_nonneg_left hcost (le_of_lt (lt_trans zero_lt_one alphabetMass_gt_one)))
  have h:=mul_le_mul_of_nonneg_left hh (pow_nonneg radius_pos.le 8)
  rw [total_strong_formula hp,total_restricted_formula hp] at h
  simpa only [sourceEnvelope,mul_assoc] using h

end SubmittedGenus.CapFourMass.ActualComponent
