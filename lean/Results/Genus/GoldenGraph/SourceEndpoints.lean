import Results.Genus.GoldenGraph.SourceEdges
import Results.Genus.GoldenGraph.EndpointCounts
import Results.Genus.GoldenSpectral.Endpoints

/-! The actual golden-q endpoint vectors and their global boundary budget. -/
namespace SubmittedGenus.GoldenGraph.Source
open RawGraph RawGraph.SourceModel RawGraph.Topology RawGraph.Transfer
open CapFourMass.ActualComponent GoldenSpectral CapFiveMass.MatrixSource CapFiveMass.MatrixBounds
open scoped BigOperators Matrix
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

lemma domainHalf_energy_free {m r p : ℕ} (c : Component m r p) (j : Fin (edgeCount c+1)) :
    vectorEnergy (domainHalf c j)≤alphabetMass := by
  apply Finset.sum_le_sum
  intro v _
  rw [domainHalf_sq]
  split_ifs
  · rfl
  · exact pow_nonneg radius_pos.le _

lemma domainHalf_energy_loop {m r p : ℕ} (c : Component m r p) (j : Fin (edgeCount c+1))
    (hl : StrongLoop r p (vertex c j) ∨ CarryLoop r p (vertex c j)) :
    vectorEnergy (domainHalf c j)≤loopMass := by
  have hbound : vectorEnergy (domainHalf c j)≤
      ∑ v : State,if 2≤v.val+1 then radius^(v.val+1) else 0 := by
    apply Finset.sum_le_sum
    intro v _
    rw [domainHalf_sq]
    by_cases hv : Domain r p 4 (vertex c j) (v.val+1)
    · rw [if_pos hv]
      have hh:=((domain_iff_unary _ _).mp hv).2 (vertex_free c j)
      have htwo : 2≤v.val+1 := by
        rcases hl with hs | hc
        · have:=hh.2.2.1 hs; omega
        · have:=hh.2.2.2 hc; omega
      rw [if_pos htwo]
    · rw [if_neg hv]
      split_ifs
      · exact pow_nonneg radius_pos.le _
      · rfl
  have hs : (∑ v : State,if 2≤v.val+1 then radius^(v.val+1) else 0)=loopMass := by
    norm_num [Fin.sum_univ_succ,loopMass]
    ring
  exact hbound.trans_eq hs

def endpointMass (k : CapFiveMass.EndpointKind) : ℝ := if k=.free then alphabetMass else loopMass

lemma loopMass_nonneg : 0≤loopMass := by unfold loopMass; have hr:=radius_pos; positivity
lemma endpointMass_nonneg (k : CapFiveMass.EndpointKind) : 0≤endpointMass k := by
  unfold endpointMass
  split_ifs
  · exact alphabetMass_gt_one.le.trans' (by norm_num)
  · exact loopMass_nonneg

lemma domainHalf_energy_loopKind {m r p : ℕ} (c : Component m r p) (j : Fin (edgeCount c+1)) :
    vectorEnergy (domainHalf c j)≤
      endpointMass (CapFiveMass.ActualComponent.loopKind (r:=r) (p:=p) (vertex c j)) := by
  unfold CapFiveMass.ActualComponent.loopKind
  split_ifs with hs hc
  · exact domainHalf_energy_loop c j (Or.inl hs)
  · exact domainHalf_energy_loop c j (Or.inr hc)
  · exact domainHalf_energy_free c j

lemma first_half_energy {m r p : ℕ} (c : Component m r p) :
    vectorEnergy (halfWeights c 0)≤endpointMass (CapFiveMass.ActualComponent.leftKind c) := by
  have he : halfWeights c 0=domainHalf c 0 := funext (fun v => Source.halfWeights_fin c 0 v)
  rw [he]
  exact domainHalf_energy_loopKind c 0

lemma last_half_energy {m r p : ℕ} (c : Component m r p) :
    vectorEnergy (halfWeights c (edgeCount c))≤endpointMass (CapFiveMass.ActualComponent.rightKind c) := by
  have he : halfWeights c (edgeCount c)=domainHalf c (Fin.last _) :=
    funext (fun v => Source.halfWeights_fin c (Fin.last _) v)
  rw [he]
  unfold CapFiveMass.ActualComponent.rightKind
  split_ifs
  · exact domainHalf_energy_free c (Fin.last _)
  · exact domainHalf_energy_loopKind c (Fin.last _)

/-- Two endpoint incidences are retained even when the path has zero edges. -/
def componentBoundaryMass {m r p : ℕ} (c : Component m r p) : ℝ :=
  if (freeComponentOrder m r p c).cycle=true then 1 else
    Real.sqrt (endpointMass (CapFiveMass.ActualComponent.leftKind c))*
      Real.sqrt (endpointMass (CapFiveMass.ActualComponent.rightKind c))

lemma componentBoundaryMass_nonneg {m r p : ℕ} (c : Component m r p) :
    0≤componentBoundaryMass c := by unfold componentBoundaryMass; split_ifs <;> positivity

lemma componentBoundaryMass_sq {m r p : ℕ} (c : Component m r p) :
    componentBoundaryMass c^2=
      alphabetMass^CapFiveMass.ActualComponent.endpointCount c .free *
      loopMass^(CapFiveMass.ActualComponent.endpointCount c .strongLoop+
        CapFiveMass.ActualComponent.endpointCount c .carryLoop) := by
  by_cases hc : (freeComponentOrder m r p c).cycle=true
  · simp [componentBoundaryMass,CapFiveMass.ActualComponent.endpointCount,hc]
  · rw [componentBoundaryMass,if_neg hc,mul_pow,
      Real.sq_sqrt (endpointMass_nonneg _),Real.sq_sqrt (endpointMass_nonneg _)]
    simp only [CapFiveMass.ActualComponent.endpointCount,hc]
    cases hL : CapFiveMass.ActualComponent.leftKind c <;>
      cases hR : CapFiveMass.ActualComponent.rightKind c <;> simp [endpointMass] <;> ring

def sourceBoundaryMass (m r p : ℕ) : ℝ := ∏ c : Component m r p,componentBoundaryMass c

lemma sourceBoundaryMass_nonneg (m r p : ℕ) : 0≤sourceBoundaryMass m r p :=
  Finset.prod_nonneg (fun c _ => componentBoundaryMass_nonneg c)

lemma sourceBoundaryMass_sq (m r p : ℕ) :
    sourceBoundaryMass m r p^2=
      alphabetMass^CapFiveMass.ActualComponent.totalEndpointCount m r p .free *
      loopMass^(CapFiveMass.ActualComponent.totalEndpointCount m r p .strongLoop+
        CapFiveMass.ActualComponent.totalEndpointCount m r p .carryLoop) := by
  unfold sourceBoundaryMass
  rw [← Finset.prod_pow]
  simp_rw [componentBoundaryMass_sq]
  rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,Finset.prod_pow_eq_pow_sum,
    Finset.sum_add_distrib]
  rfl

/-- Original boundary budget: the complete product of actual endpoint norms
is at most s₄(q), with no factor per component or per cycle. -/
theorem sourceBoundaryMass_le {m r p : ℕ} (hp : Parameters m r p 4) :
    sourceBoundaryMass m r p≤alphabetMass := by
  have hf:=CapFiveMass.MissingGeometry.free_endpoint_count_le_two hp
  have ha : alphabetMass^CapFiveMass.ActualComponent.totalEndpointCount m r p .free≤alphabetMass^2 :=
    pow_le_pow_right₀ alphabetMass_gt_one.le hf
  have hl : loopMass^(CapFiveMass.ActualComponent.totalEndpointCount m r p .strongLoop+
      CapFiveMass.ActualComponent.totalEndpointCount m r p .carryLoop)≤1 :=
    pow_le_one₀ loopMass_nonneg loopMass_lt_one.le
  have hs:=mul_le_mul ha hl (pow_nonneg loopMass_nonneg _) (sq_nonneg alphabetMass)
  rw [← sourceBoundaryMass_sq,mul_one] at hs
  have hn:=sourceBoundaryMass_nonneg m r p
  have hp' : 0≤alphabetMass := by linarith [alphabetMass_gt_one]
  nlinarith

end
end SubmittedGenus.GoldenGraph.Source
