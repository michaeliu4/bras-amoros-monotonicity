import Results.Genus.GoldenGraph.RunJunctions

/-! Actual consecutive source-word junctions inject into their physical
internal strong vertices. No independent run-layout certificate is assumed. -/
namespace SubmittedGenus.GoldenGraph
open RawGraph RawGraph.SourceModel RawGraph.Topology CapFourMass.ActualComponent
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

abbrev PathWordJunction {m r p : ℕ} (c : Component m r p) :=
  WordJunction (edgeCount c) (fun j => kind r p (vertex c j.castSucc) (vertex c j.succ))

lemma path_word_junction_count {m r p : ℕ} (c : Component m r p) :
    wordJunctions (pathWord c)=Fintype.card (PathWordJunction c) :=
  wordJunctions_card _ _

def pathJunctionPosition {m r p : ℕ} (c : Component m r p) (j : PathWordJunction c) :
    Fin (edgeCount c+1) := ⟨j.val.val+1,by have:=j.val.isLt; omega⟩

lemma pathJunctionPosition_injective {m r p : ℕ} (c : Component m r p) :
    Function.Injective (pathJunctionPosition c) := by
  intro i j he
  apply Subtype.ext
  apply Fin.ext
  have hh:=congrArg (fun j : Fin (edgeCount c+1) => j.val) he
  change i.val.val+1=j.val.val+1 at hh
  omega

/-- The shared physical vertex of two adjacent ordinary strong source edges. -/
def pathJunctionVertex {m r p : ℕ} (c : Component m r p) (j : PathWordJunction c) :
    JunctionVertex m r p := by
  let k : Fin (edgeCount c):=⟨j.val.val,by have:=j.val.isLt; omega⟩
  let l : Fin (edgeCount c):=⟨j.val.val+1,by have:=j.val.isLt; omega⟩
  have hk : k.succ=pathJunctionPosition c j := rfl
  have hl : l.castSucc=pathJunctionPosition c j := rfl
  refine ⟨((freeComponentOrder m r p c).label (pathJunctionPosition c j)).val,?_⟩
  refine ⟨vertex c k.castSucc,vertex c l.succ,?_,?_,?_⟩
  · have hs:=(kind_ne_carry_iff (consecutive_adj c k)).mp j.property.1
    exact StrongRuns.strongStep_symm hs
  · exact (kind_ne_carry_iff (consecutive_adj c l)).mp j.property.2
  · intro he
    have hh:=congrArg Fin.val (vertex_injective c he)
    change j.val.val=j.val.val+1+1 at hh
    omega

lemma pathJunctionVertex_val {m r p : ℕ} (c : Component m r p) (j : PathWordJunction c) :
    (pathJunctionVertex c j).val=
      freeOrderedVertexEquiv m r p ⟨c,pathJunctionPosition c j⟩ := rfl

/-- Different ordered source junction positions are different physical vertices. -/
def pathJunctionMap (m r p : ℕ) : (Σ c : Component m r p,PathWordJunction c)→JunctionVertex m r p :=
  fun x => pathJunctionVertex x.1 x.2

lemma pathJunctionMap_injective (m r p : ℕ) : Function.Injective (pathJunctionMap m r p) := by
  rintro ⟨c,i⟩ ⟨d,j⟩ he
  have hv:=congrArg Subtype.val he
  change freeOrderedVertexEquiv m r p ⟨c,pathJunctionPosition c i⟩=
    freeOrderedVertexEquiv m r p ⟨d,pathJunctionPosition d j⟩ at hv
  have hs:=(freeOrderedVertexEquiv m r p).injective hv
  have hc : c=d := congrArg Sigma.fst hs
  subst d
  have hp : pathJunctionPosition c i=pathJunctionPosition c j := by
    exact eq_of_heq ((Sigma.mk.inj_iff.mp hs).2)
  exact congrArg (Sigma.mk c) ((pathJunctionPosition_injective c) hp)

/-- Complete path-word junction count, summed over the actual physical graph. -/
theorem path_word_junction_sum_le (m r p : ℕ) :
    (∑ c : Component m r p,wordJunctions (pathWord c))≤r-1 := by
  simp_rw [path_word_junction_count]
  rw [← Fintype.card_sigma]
  exact (Fintype.card_le_of_injective _ (pathJunctionMap_injective m r p)).trans
    (strong_junction_count_le m r p)

end
end SubmittedGenus.GoldenGraph
