import Results.Genus.GoldenGraph.CompleteJunctionCounts
import Results.Genus.GoldenGraph.EndpointCounts

/-! Source-exact paid-run lower bound in the submitted d−16 argument. -/
namespace SubmittedGenus.GoldenGraph
open RawGraph RawGraph.SourceModel RawGraph.Topology CapFourMass.ActualComponent
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

/-- A cut furnished by the actual source's strong/carry transition. -/
def cycleCut {m r p : ℕ} (hp : Parameters m r p 4) (c : Component m r p)
    (hc : (freeComponentOrder m r p c).cycle=true) : ℕ :=
  Classical.choose (actual_cycle_run_cut hp c hc)

lemma cycleCut_last {m r p : ℕ} (hp : Parameters m r p 4) (c : Component m r p)
    (hc : (freeComponentOrder m r p c).cycle=true) :
    (((closedWord c).rotate (cycleCut hp c hc)).map strongColor).getLast?=some false :=
  (Classical.choose_spec (actual_cycle_run_cut hp c hc)).2.1

lemma cycleCut_compatible {m r p : ℕ} (hp : Parameters m r p 4) (c : Component m r p)
    (hc : (freeComponentOrder m r p c).cycle=true) :
    ((closedWord c).rotate (cycleCut hp c hc)).IsChain CompatibleKinds :=
  (Classical.choose_spec (actual_cycle_run_cut hp c hc)).2.2.1

lemma carry_last_boundary_zero (l : List EdgeKind) (h : (l.map strongColor).getLast?=some false) :
    boundaryJunction l l=0 := by
  have hn : l≠[] := by intro he; simp [he] at h
  have hc : strongColor (l.getLast hn)=false := by
    apply Option.some.inj
    simpa only [List.getLast?_eq_some_getLast (map_nonempty _ _ hn),List.getLast_map] using h
  have hk : l.getLast hn=.carry := by
    cases he : l.getLast hn <;> simp_all [strongColor]
  simp only [boundaryJunction,List.getLastD_eq_getLast?,List.getLast?_eq_some_getLast hn,
    Option.getD_some,hk,strongPair_carry_left]

/-- The actual word is retained on paths and rotated at a genuine transition
on cycles. This changes neither physical edges nor their multiplicities. -/
def sourceRunWord {m r p : ℕ} (hp : Parameters m r p 4) (c : Component m r p) : List EdgeKind :=
  if hc : (freeComponentOrder m r p c).cycle=true then (closedWord c).rotate (cycleCut hp c hc)
  else pathWord c

lemma sourceRunWord_compatible {m r p : ℕ} (hp : Parameters m r p 4) (c : Component m r p) :
    (sourceRunWord hp c).IsChain CompatibleKinds := by
  unfold sourceRunWord
  split_ifs with hc
  · exact cycleCut_compatible hp c hc
  · exact pathWord_compatible hp c

lemma sourceRunWord_strong {m r p : ℕ} (hp : Parameters m r p 4) (c : Component m r p) :
    strongLength (sourceRunWord hp c)=strongLength (sourceWord c) := by
  unfold sourceRunWord sourceWord
  split_ifs with hc
  · exact (rotated_exponents _ _).1
  · rfl

lemma sourceRunWord_junctions {m r p : ℕ} (hp : Parameters m r p 4) (c : Component m r p) :
    wordJunctions (sourceRunWord hp c)=sourceJunctions c := by
  unfold sourceRunWord sourceJunctions
  split_ifs with hc
  · have hz:=carry_last_boundary_zero _ (cycleCut_last hp c hc)
    have hr:=cyclicWordJunctions_rotate (closedWord c) (cycleCut hp c hc)
    simpa only [cyclicWordJunctions,hz,Nat.add_zero] using hr
  · rfl

def sourceStrongRunCount {m r p : ℕ} (hp : Parameters m r p 4) : ℕ :=
  ∑ c : Component m r p,strongRunCount (sourceRunWord hp c)

def componentPaidRuns {m r p : ℕ} (hp : Parameters m r p 4) (c : Component m r p) : ℕ :=
  if (freeComponentOrder m r p c).cycle=true then strongRunCount (sourceRunWord hp c)
  else strongRunCount (sourceRunWord hp c)-2

def componentUnpaidRuns {m r p : ℕ} (hp : Parameters m r p 4) (c : Component m r p) : ℕ :=
  if (freeComponentOrder m r p c).cycle=true then 0
  else min (strongRunCount (sourceRunWord hp c)) 2

def sourcePaidRunCount {m r p : ℕ} (hp : Parameters m r p 4) : ℕ :=
  ∑ c : Component m r p,componentPaidRuns hp c

def sourceUnpaidRunCount {m r p : ℕ} (hp : Parameters m r p 4) : ℕ :=
  ∑ c : Component m r p,componentUnpaidRuns hp c

/-- Exact ordinary edge/run/junction identity on the actual graph. -/
theorem source_strong_run_junction_identity {m r p : ℕ} (hp : Parameters m r p 4) :
    totalStrongLength m r p=sourceStrongRunCount hp+
      ∑ c : Component m r p,sourceJunctions c := by
  unfold totalStrongLength sourceStrongRunCount
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c _
  rw [← sourceRunWord_strong hp c,strong_runs_junction_identity _ (sourceRunWord_compatible hp c),
    sourceRunWord_junctions]

lemma source_paid_unpaid_partition {m r p : ℕ} (hp : Parameters m r p 4) :
    sourceStrongRunCount hp=sourcePaidRunCount hp+sourceUnpaidRunCount hp := by
  unfold sourceStrongRunCount sourcePaidRunCount sourceUnpaidRunCount
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c _
  unfold componentPaidRuns componentUnpaidRuns
  split_ifs <;> omega

/-- Only the at-most-two endpoint strong runs of each actual path are unpaid. -/
theorem source_unpaid_run_count_le_six {m r p : ℕ} (hp : Parameters m r p 4) :
    sourceUnpaidRunCount hp≤6 := by
  apply le_trans (b:=sourceEndpointCount m r p) _ (source_endpoint_count_le_six hp)
  unfold sourceUnpaidRunCount sourceEndpointCount
  apply Finset.sum_le_sum
  intro c _
  unfold componentUnpaidRuns
  split_ifs <;> omega

/-- The original d−16 paid-run budget, now for the actual raw source's maximal
runs. No residue-layout or edge-count certificate is assumed. -/
theorem source_paid_run_count_lower {m r p : ℕ} (hp : Parameters m r p 4) :
    p-r≤2*sourcePaidRunCount hp+16 := by
  have he:=strong_edge_lower hp
  have hj:=source_junction_sum_le m r p
  have hu:=source_unpaid_run_count_le_six hp
  have hi:=source_strong_run_junction_identity hp
  rw [source_paid_unpaid_partition] at hi
  have hr:=hp.1
  omega

end
end SubmittedGenus.GoldenGraph
