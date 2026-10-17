import Results.Genus.CapFourMass.CompilerCounts

/-! Source-exact internal strong-junction accounting for the original d−16
paid-run bound. The local graph fact is from the submitted strong-run geometry. -/
namespace SubmittedGenus.GoldenGraph
open RawGraph RawGraph.SourceModel RawGraph.Topology CapFourMass.ActualComponent
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

/-- A physical free vertex with two distinct retained ordinary strong edges. -/
def IsStrongJunction {m r p : ℕ} (i : FreeVertex m r p) : Prop :=
  ∃ j k : Fin (m-1),StrongRuns.StrongStep r p i.val j ∧
    StrongRuns.StrongStep r p i.val k ∧ j≠k

abbrev JunctionVertex (m r p : ℕ) := {i : FreeVertex m r p // IsStrongJunction i}

lemma strong_junction_low {m r p : ℕ} (i : JunctionVertex m r p) : physical i.val.val<r := by
  obtain ⟨j,k,hj,hk,hne⟩:=i.property
  exact StrongRuns.internal_strong_lt_r hj hk hne

def junctionIndex {m r p : ℕ} (i : JunctionVertex m r p) : Fin (r-1) :=
  ⟨i.val.val.val,by have hh:=strong_junction_low i; unfold physical at hh; omega⟩

lemma junctionIndex_injective (m r p : ℕ) : Function.Injective (@junctionIndex m r p) := by
  intro i j he
  apply Subtype.ext
  apply Subtype.ext
  apply Fin.ext
  exact congrArg (fun x : Fin (r-1) => x.val) he

/-- The entire actual graph, including every component and multiplicity, has
at most r−1 internal strong-run vertices. -/
theorem strong_junction_count_le (m r p : ℕ) : Fintype.card (JunctionVertex m r p)≤r-1 := by
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective _ (junctionIndex_injective m r p)

/-- The lower edge count needed by the original paid-run exponent, derived
from the already identified actual strong source edges. -/
theorem strong_edge_lower {m r p : ℕ} (hp : Parameters m r p 4) :
    r+p≤2*totalStrongLength m r p+6 := by
  have hr:=hp.1
  have hrp:=hp.2.1
  rw [total_strong_formula hp]
  split_ifs <;> omega

/-- Once the maximal-run compiler supplies its exact edge/junction identity,
the original lower run count follows without any new geometric hypothesis. -/
theorem run_count_from_junctions {m r p runs : ℕ} (hp : Parameters m r p 4)
    (hcount : totalStrongLength m r p=runs+Fintype.card (JunctionVertex m r p)) :
    p-r≤2*runs+4 := by
  have he:=strong_edge_lower hp
  have hj:=strong_junction_count_le m r p
  have hr:=hp.1
  rw [hcount] at he
  omega

/-- The final manuscript exponent is unchanged: at most six endpoint runs
are unpaid, and the exact strong-run count gives 2·paid+16≥p−r. -/
theorem paid_count_from_junctions {m r p paid unpaid : ℕ} (hp : Parameters m r p 4)
    (hcount : totalStrongLength m r p=paid+unpaid+Fintype.card (JunctionVertex m r p))
    (hu : unpaid≤6) : p-r≤2*paid+16 := by
  have hh:=run_count_from_junctions hp hcount
  omega

end
end SubmittedGenus.GoldenGraph
