import Results.Genus.CapFourMass.ActualEnvelope
import Results.Genus.CapFourMass.ModeEndpointBudget

/-! Typed absolute-run bounds and their actual global endpoint/edge envelope.
The source-to-local-complete-mode identity is deliberately a separate input. -/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFourMass.ActualComponent
open RawGraph RawGraph.Topology CapFiveMass.MatrixBounds

lemma PathCode.path_abs_le (q : PathCode) (x y : State→ℝ) :
    |x ⬝ᵥ (q.matrix *ᵥ y)|≤
      Real.sqrt (vectorEnergy x)*Real.sqrt (vectorEnergy y)*
        (strongBound^q.strongCount*sigma^q.restrictedCount*lam^q.carryCount) := by
  apply abs_le.mpr
  refine ⟨?_,q.path_le x y⟩
  have hh:=q.path_le (-x) y
  have he : vectorEnergy (-x)=vectorEnergy x := by simp [vectorEnergy]
  rw [neg_dotProduct,he] at hh
  linarith

/-- Pure paths retain their complete scalar contraction; carried paths sum
absolute complete run assignments using the projected blocks. -/
def PathCode.absolute (q : PathCode) (x y : State→ℝ) : ℝ :=
  match q with
  | .pure s => |x ⬝ᵥ ((optionalStrongMatrix s)*ᵥ y)|
  | .carried pre n _ bs post => framedPathAbsolute pre post n bs x y

lemma PathCode.absolute_le (q : PathCode) (x y : State→ℝ) :
    q.absolute x y≤Real.sqrt (vectorEnergy x)*Real.sqrt (vectorEnergy y)*
      (strongBound^q.strongCount*sigma^q.restrictedCount*lam^q.carryCount) := by
  cases q with
  | pure s => exact PathCode.path_abs_le (.pure s) x y
  | carried pre n hn bs post =>
    have hh:=optional_frame_absolute_le pre post n bs x y
    rw [optional_frame_bounds_product] at hh
    simpa only [PathCode.absolute,PathCode.strongCount,PathCode.restrictedCount,PathCode.carryCount,
      optionalStrongCount_eq_frame,optionalRestrictedCount_eq_frame,
      Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hh

lemma path_absolute_le_edgeCost {m r p : ℕ} (c : Component m r p)
    (hc : (freeComponentOrder m r p c).cycle=false) (q : PathCode)
    (hS : q.strongCount=strongLength (sourceWord c))
    (hC : q.carryCount=carryLength (sourceWord c))
    (hE : q.restrictedCount=restrictedLength (sourceWord c))
    (x y : State→ℝ)
    (hx : vectorEnergy x≤alphabetMass^(if CapFiveMass.ActualComponent.leftKind c=.free then 1 else 0))
    (hy : vectorEnergy y≤alphabetMass^(if CapFiveMass.ActualComponent.rightKind c=.free then 1 else 0)) :
    q.absolute x y≤modeEndpointBudget c*edgeCost c := by
  have hh:=q.absolute_le x y
  rw [hS,hC,hE] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right
    (path_endpoint_le_modeBudget c hc x y hx hy) (edgeCost_nonneg c))

lemma cycle_absolute_le_edgeCost {m r p : ℕ} (c : Component m r p)
    (hc : (freeComponentOrder m r p c).cycle=true) (bs : List CoupledRun) (hne : bs≠[])
    (hS : (bs.map (fun b => b.strong.strongCount)).sum=strongLength (sourceWord c))
    (hC : (bs.map CoupledRun.carryLength).sum=carryLength (sourceWord c))
    (hE : (bs.map (fun b => b.strong.restrictedCount)).sum=restrictedLength (sourceWord c)) :
    coupledCycleAbsolute bs≤modeEndpointBudget c*edgeCost c := by
  have hh : coupledCycleAbsolute bs≤(bs.map (fun b : CoupledRun => b.dominated.bound)).prod := by
    cases bs with
    | nil => contradiction
    | cons b bs => exact coupledCycleAbsolute_le b bs
  rw [coupled_bounds_product,hS,hC,hE] at hh
  simpa only [modeEndpointBudget,CapFiveMass.ActualComponent.endpointCount,hc,if_true,
    pow_zero,Real.sqrt_one,one_mul,edgeCost] using hh

/-- The exceptional zero-edge carry-loop uses its free/loop mode convention,
which is bounded by one free endpoint incidence rather than two loop masks. -/
lemma isolated_loop_le_edgeCost {m r p : ℕ} (c : Component m r p)
    (hS : strongLength (sourceWord c)=0) (hC : carryLength (sourceWord c)=0)
    (hE : restrictedLength (sourceWord c)=0)
    (hfree : 1≤CapFiveMass.ActualComponent.endpointCount c .free) :
    carryAbsolute 0 freeBoundary loopBoundary≤modeEndpointBudget c*edgeCost c := by
  have hh : Real.sqrt alphabetMass≤modeEndpointBudget c := by
    apply Real.sqrt_le_sqrt
    simpa only [pow_one] using pow_le_pow_right₀ alphabetMass_gt_one.le hfree
  simpa only [edgeCost,hS,hC,hE,pow_zero,mul_one,one_mul] using isolated_carry_loop_absolute_le.trans hh

/-- Any source-identified local absolute mode sums satisfying the preceding
three typed branches obey the original full envelope. No signed cancellation
is used to manufacture the local source comparison. -/
theorem absolute_product_le_sourceEnvelope {m r p : ℕ} (hp : Parameters m r p 4)
    (A : Component m r p→ℝ) (hA : ∀ c,0≤A c)
    (hloc : ∀ c,A c≤modeEndpointBudget c*edgeCost c) :
    radius^8*(∏ c,A c)≤sourceEnvelope m r p := by
  have hp1 : (∏ c,A c)≤alphabetMass*
      (strongBound^(totalStrongLength m r p)*sigma^(totalRestrictedLength m r p)*
        lam^(totalCarryLength m r p)) := by
    calc
      _ ≤ ∏ c,modeEndpointBudget c*edgeCost c := Finset.prod_le_prod (fun c _ => hA c) (fun c _ => hloc c)
      _ = (∏ c,modeEndpointBudget c)*
          (strongBound^(totalStrongLength m r p)*sigma^(totalRestrictedLength m r p)*
            lam^(totalCarryLength m r p)) := by rw [Finset.prod_mul_distrib,edgeCost_product]
      _ ≤ _ := mul_le_mul_of_nonneg_right (modeEndpointBudget_product_le hp)
        (mul_nonneg (mul_nonneg (pow_nonneg strongBound_pos.le _) (pow_nonneg sigma_bounds.1.le _))
          (pow_nonneg lam_pos.le _))
  have hcost:=edge_budget_bound (totalStrongLength m r p) (totalRestrictedLength m r p)
    (totalCarryLength m r p) (m-3) (total_edges_le_free_vertices hp)
  have h:=mul_le_mul_of_nonneg_left (hp1.trans (mul_le_mul_of_nonneg_left hcost
    (le_of_lt (lt_trans zero_lt_one alphabetMass_gt_one)))) (pow_nonneg radius_pos.le 8)
  rw [total_strong_formula hp,total_restricted_formula hp] at h
  simpa only [sourceEnvelope,mul_assoc] using h

end SubmittedGenus.CapFourMass.ActualComponent
