import Results.Genus.GoldenGraph.Junctions

/-! Original endpoint budget from the actual missing incidences and self-pairs. -/
namespace SubmittedGenus.GoldenGraph
open RawGraph RawGraph.SourceModel RawGraph.Topology CapFourMass.ActualComponent
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

lemma actual_loop_count_le_four (m r p : ℕ) :
    (CapFiveMass.MissingGeometry.loops m r p).card≤4 := by
  let targets : Finset ℕ := {r,p,m+r,m+p}
  have hm : Set.MapsTo (fun i : FreeVertex m r p => 2*physical i.val)
      (CapFiveMass.MissingGeometry.loops m r p) targets := by
    intro i hi
    have hh := (Finset.mem_filter.mp hi).2
    simp only [CapFiveMass.MissingGeometry.Loop,StrongLoop,CarryLoop] at hh
    change 2*physical i.val ∈ targets
    simp only [targets,Finset.mem_insert,Finset.mem_singleton]
    omega
  have hinj : Set.InjOn (fun i : FreeVertex m r p => 2*physical i.val)
      (CapFiveMass.MissingGeometry.loops m r p) := by
    intro i _ j _ he
    apply Subtype.ext
    apply Fin.ext
    change 2*physical i.val=2*physical j.val at he
    unfold physical at he
    omega
  have hh := Finset.card_le_card_of_injOn _ hm hinj
  have h1 := Finset.card_insert_le r ({p,m+r,m+p} : Finset ℕ)
  have h2 := Finset.card_insert_le p ({m+r,m+p} : Finset ℕ)
  have h3 := Finset.card_insert_le (m+r) ({m+p} : Finset ℕ)
  simp only [Finset.card_singleton] at h3
  change (CapFiveMass.MissingGeometry.loops m r p).card≤({r,p,m+r,m+p} : Finset ℕ).card at hh
  omega

def sourcePathCount (m r p : ℕ) : ℕ :=
  ∑ c : Component m r p,if (freeComponentOrder m r p c).cycle=true then 0 else 1

def sourceEndpointCount (m r p : ℕ) : ℕ :=
  ∑ c : Component m r p,if (freeComponentOrder m r p c).cycle=true then 0 else 2

lemma sourceEndpointCount_eq (m r p : ℕ) : sourceEndpointCount m r p=
    CapFiveMass.ActualComponent.totalEndpointCount m r p .free+
    CapFiveMass.ActualComponent.totalEndpointCount m r p .strongLoop+
    CapFiveMass.ActualComponent.totalEndpointCount m r p .carryLoop := by
  unfold sourceEndpointCount CapFiveMass.ActualComponent.totalEndpointCount
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun c _ => (CapFiveMass.ActualComponent.endpoint_counts_sum c).symm)

lemma sourceEndpointCount_eq_twice_paths (m r p : ℕ) :
    sourceEndpointCount m r p=2*sourcePathCount m r p := by
  unfold sourceEndpointCount sourcePathCount
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  split_ifs <;> rfl

/-- At most six endpoint incidences: two genuinely missing incidences and at
most four self-pairs. Isolated vertices still contribute both endpoint slots. -/
theorem source_endpoint_count_le_six {m r p : ℕ} (hp : Parameters m r p 4) :
    sourceEndpointCount m r p≤6 := by
  rw [sourceEndpointCount_eq]
  have hf:=CapFiveMass.MissingGeometry.free_endpoint_count_le_two hp
  have hl:=actual_loop_count_le_four m r p
  rw [CapFiveMass.MissingGeometry.loops_card_eq hp] at hl
  omega

theorem source_path_count_le_three {m r p : ℕ} (hp : Parameters m r p 4) :
    sourcePathCount m r p≤3 := by
  have h:=source_endpoint_count_le_six hp
  rw [sourceEndpointCount_eq_twice_paths] at h
  omega

end
end SubmittedGenus.GoldenGraph
