import Results.Genus.CapFiveMass.MissingGeometry
import Results.Genus.RawGraph.ComponentLocalization

noncomputable section
open scoped BigOperators
namespace SubmittedGenus.CapFiveMass
namespace MissingGeometry
open RawGraph RawGraph.SourceModel RawGraph.Topology RawGraph.Incidence ActualComponent

lemma ordinaryPairs_card (m r p : ℕ) :
    (ordinaryPairs m r p).card = 2 * (totalStrongCount m r p + totalCarryCount m r p) := by
  classical
  have h := relation_component_card (freeGraph m r p) (freeGraph_noThird m r p)
    (freeGraph_noTriangle m r p) (freeGraph m r p).Adj (fun _ _ h => h)
  change (ordinaryPairs m r p).card = ∑ c : Component m r p,
    (Finset.univ.filter (fun ij : Fin (edgeCount c + 1) × Fin (edgeCount c + 1) =>
      (freeGraph m r p).Adj ((freeComponentOrder m r p c).label ij.1).val
        ((freeComponentOrder m r p c).label ij.2).val)).card at h
  have hlocal (c : Component m r p) :
      (Finset.univ.filter (fun ij : Fin (edgeCount c + 1) × Fin (edgeCount c + 1) =>
        (freeGraph m r p).Adj ((freeComponentOrder m r p c).label ij.1).val
          ((freeComponentOrder m r p c).label ij.2).val)).card =
        2 * (strongCount c + carryCount c) := by
    have hc := (freeComponentOrder m r p c).relation_edge_card c.toSimpleGraph.Adj
      (fun _ _ h => h.symm) (fun _ _ h => h)
    have hedge (j : Fin (edgeCount c)) : c.toSimpleGraph.Adj
        ((freeComponentOrder m r p c).label j.castSucc)
        ((freeComponentOrder m r p c).label j.succ) := consecutive_adj c j
    have hclose : ((freeComponentOrder m r p c).cycle = true ∧
        c.toSimpleGraph.Adj ((freeComponentOrder m r p c).label 0)
          ((freeComponentOrder m r p c).label (Fin.last _))) ↔
        (freeComponentOrder m r p c).cycle = true := by
      refine ⟨And.left, fun hh => ⟨hh, ?_⟩⟩
      exact (closing_adj c hh).symm
    simp only [hedge, Finset.filter_true_of_mem (fun _ _ => True.intro), Finset.card_univ,
      Fintype.card_fin, hclose] at hc
    rw [edge_counts_sum]
    exact hc
  rw [h]
  simp_rw [hlocal]
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, totalStrongCount, totalCarryCount]


end MissingGeometry
end SubmittedGenus.CapFiveMass
