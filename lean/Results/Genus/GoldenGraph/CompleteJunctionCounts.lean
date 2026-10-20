import Results.Genus.GoldenGraph.CycleJunctions

/-! Exhaustive physical junction accounting for paths and cycles. -/
namespace SubmittedGenus.GoldenGraph
open RawGraph RawGraph.SourceModel RawGraph.Topology CapFourMass.ActualComponent
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

lemma cyclicWordJunctions_concat (l : List EdgeKind) (k : EdgeKind) (hn : l≠[]) :
    cyclicWordJunctions (l++[k])=wordJunctions l+
      strongPair (l.getLastD .carry) k+strongPair k (l.headD .carry) := by
  unfold cyclicWordJunctions
  rw [wordJunctions_append]
  unfold boundaryJunction
  rw [List.getLastD_concat]
  cases l with
  | nil => contradiction
  | cons a l => simp [wordJunctions,Nat.add_assoc]

lemma extraJunction_card {m r p : ℕ} (c : Component m r p) :
    Fintype.card (ExtraJunction c)=
      if (freeComponentOrder m r p c).cycle=true then
        strongPair ((pathWord c).getLastD .carry) (closingKind c)+
        strongPair (closingKind c) ((pathWord c).headD .carry) else 0 := by
  rw [Fintype.card_subtype,Finset.card_filter]
  simp only [Fintype.sum_bool]
  by_cases hc : (freeComponentOrder m r p c).cycle=true
  · simp [hc,strongPair]
  · simp [hc]

def sourceJunctions {m r p : ℕ} (c : Component m r p) : ℕ :=
  if (freeComponentOrder m r p c).cycle=true then cyclicWordJunctions (closedWord c)
  else wordJunctions (pathWord c)

/-- All internal and closing junctions are represented once. -/
lemma sourceJunctions_card {m r p : ℕ} (c : Component m r p) :
    sourceJunctions c=Fintype.card (AllJunction c) := by
  rw [Fintype.card_sum,extraJunction_card,← path_word_junction_count]
  unfold sourceJunctions
  by_cases hc : (freeComponentOrder m r p c).cycle=true
  · rw [if_pos hc,if_pos hc]
    have hn : 3≤edgeCount c := (freeComponentOrder m r p c).cycle_min hc
    have hnon : pathWord c≠[] := by intro he; have:=congrArg List.length he; simp at this; omega
    rw [closedWord,cyclicWordJunctions_concat _ _ hnon]
    simp only [closingKind,Nat.add_assoc]
  · simp [hc]

def allJunctionMap (m r p : ℕ) :
    (Σ c : Component m r p,AllJunction c)→JunctionVertex m r p :=
  fun x => allJunctionVertex x.1 x.2

lemma allJunctionMap_injective (m r p : ℕ) : Function.Injective (allJunctionMap m r p) := by
  rintro ⟨c,i⟩ ⟨d,j⟩ he
  have hv:=congrArg Subtype.val he
  change (allJunctionVertex c i).val=(allJunctionVertex d j).val at hv
  rw [allJunctionVertex_val,allJunctionVertex_val] at hv
  have hs:=(freeOrderedVertexEquiv m r p).injective hv
  have hc : c=d := congrArg Sigma.fst hs
  subst d
  have hp : allJunctionPosition c i=allJunctionPosition c j :=
    eq_of_heq ((Sigma.mk.inj_iff.mp hs).2)
  exact congrArg (Sigma.mk c) ((allJunctionPosition_injective c) hp)

/-- Every source strong junction, including both closing cycle corners, is
charged injectively to one of the original r−1 low physical coordinates. -/
theorem source_junction_sum_le (m r p : ℕ) :
    (∑ c : Component m r p,sourceJunctions c)≤r-1 := by
  simp_rw [sourceJunctions_card]
  rw [← Fintype.card_sigma]
  exact (Fintype.card_le_of_injective _ (allJunctionMap_injective m r p)).trans
    (strong_junction_count_le m r p)

end
end SubmittedGenus.GoldenGraph
