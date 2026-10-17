import Results.Genus.CapFiveMass.OrdinaryCount
import Results.Genus.CapFiveMass.StrongGeometry

noncomputable section
open scoped BigOperators
namespace SubmittedGenus.CapFiveMass
namespace MissingGeometry
open RawGraph RawGraph.SourceModel RawGraph.Topology RawGraph.Incidence ActualComponent


lemma loops_card_eq {m r p a : ℕ} (hp : Parameters m r p a) :
    (loops m r p).card = totalEndpointCount m r p .strongLoop + totalEndpointCount m r p .carryLoop := by
  classical
  rw [total_strong_loops, total_carry_loops hp]
  simp only [loops, Finset.card_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hd := loops_disjoint hp i.val
  unfold Loop
  by_cases hs : StrongLoop r p i.val <;> by_cases hc : CarryLoop r p i.val <;> simp_all

/-- The endpoint exponent u is exactly the actual number of missing target
incidences. This equality includes isolated vertices and all self-pairs. -/
lemma free_endpoint_count_eq {m r p a : ℕ} (hp : Parameters m r p a) :
    totalEndpointCount m r p .free = (missingIncidences m r p).card := by
  have hs := source_incidence_partition hp
  rw [ordinaryPairs_card, loops_card_eq hp] at hs
  have hc := total_incidence_count m r p
  dsimp only [V] at hs
  omega

lemma free_endpoint_count_le_two {m r p a : ℕ} (hp : Parameters m r p a) :
    totalEndpointCount m r p .free ≤ 2 := by
  rw [free_endpoint_count_eq hp]
  exact missingIncidences_card_le_two hp

end MissingGeometry
end SubmittedGenus.CapFiveMass
