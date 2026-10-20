import Results.Genus.CapFourMass.SignedReflectionPairedSource
import Results.Genus.RawGraph.PackedAcceptance.ReflectionFullLayout

/-! Exact coverage and absence of cross-component edges for each arithmetic
nonzero paired cycle. This remains a local branch, not a global free layout. -/
namespace SubmittedGenus.CapFourMass.SignedReflectionPaired
open RawGraph RawGraph.SourceModel RawGraph.Topology RawGraph.PackedAcceptance
open ReflectionPairedOrbit ReflectionFullLayout

variable {g : ℕ} [NeZero g]

/-- The original free physical vertices in one paired residue block. -/
def InBlock (n r p : ℕ) (a : Fin g) (v : FreeVertex (g*(n+2)) r p) : Prop :=
  residueClass n v.val=a ∨ residueClass n v.val=mate r a

lemma vertex_inBlock (n r p δ : ℕ) (hp : p=r+g*δ)
    (a : Fin g) (ha : a≤mate r a) (ha0 : a≠0)
    (x : PairedCosets (L:=n+2) r a) : InBlock n r p a (vertex n r p δ hp a ha ha0 x) := by
  unfold InBlock
  rcases x.property with hx|hx
  · left
    apply Fin.ext
    change physical (vertex n r p δ hp a ha ha0 x).val%g=a.val
    rwa [physical_vertex]
  · right
    apply Fin.ext
    change physical (vertex n r p δ hp a ha ha0 x).val%g=(mate r a).val
    rwa [physical_vertex]

/-- An explicit inverse recovers the original residue from a free physical
coordinate. The cycle therefore omits no vertex of its arithmetic block. -/
def blockEquiv (n r p δ : ℕ) (hp : p=r+g*δ)
    (a : Fin g) (ha : a≤mate r a) (ha0 : a≠0) :
    PairedCosets (L:=n+2) r a ≃ {v : FreeVertex (g*(n+2)) r p // InBlock n r p a v} where
  toFun x := ⟨vertex n r p δ hp a ha ha0 x,vertex_inBlock n r p δ hp a ha ha0 x⟩
  invFun v := ⟨(physical v.val.val:ZMod (g*(n+2))),by
    have hv : physical v.val.val<g*(n+2) := by
      have := v.val.val.isLt
      dsimp [physical]
      omega
    rw [ZMod.val_natCast,Nat.mod_eq_of_lt hv]
    exact v.property.elim (fun h=>Or.inl (congrArg Fin.val h))
      (fun h=>Or.inr (congrArg Fin.val h))⟩
  left_inv x := by
    apply Subtype.ext
    exact cast_physical_vertex n r p δ hp a ha ha0 x
  right_inv v := by
    apply Subtype.ext
    apply Subtype.ext
    apply Fin.ext
    have hv : physical v.val.val<g*(n+2) := by
      have := v.val.val.isLt
      dsimp [physical]
      omega
    change ((physical v.val.val:ZMod (g*(n+2))).val)-1=v.val.val
    rw [ZMod.val_natCast,Nat.mod_eq_of_lt hv]
    rfl

/-- Original edges cannot leave the paired block. This applies to any free
neighbor, not just the displayed consecutive/closing cycle positions. -/
theorem block_closed (n r p δ : ℕ) (hp : p=r+g*δ) (hpm : p<g*(n+2))
    (a : Fin g) (x y : FreeVertex (g*(n+2)) r p)
    (hx : InBlock n r p a x) (hxy : (freeGraph (g*(n+2)) r p).Adj x y) :
    InBlock n r p a y := by
  have hrm : r<g*(n+2) := by omega
  have hi := partner_involutive g r (NeZero.pos g) a
  change mate r (mate r a)=a at hi
  rcases hxy.2.2.2 with ht|ht
  · have he:=residueClass_pair n r hrm x.val y.val ht
    rcases hx with hx|hx
    · exact Or.inr (he.trans (congrArg (mate r) hx))
    · exact Or.inl ((he.trans (congrArg (mate r) hx)).trans hi)
  · have he:=residueClass_pair n p hpm x.val y.val ht
    rw [mate_gap r p δ hp] at he
    rcases hx with hx|hx
    · exact Or.inr (he.trans (congrArg (mate r) hx))
    · exact Or.inl ((he.trans (congrArg (mate r) hx)).trans hi)

/-- The finite ordered cycle is a bijection onto its exact free-vertex block.
The inverse is modular arithmetic and finite indexing, never a choice. -/
def cycleEquiv (n r p δ : ℕ) (hp : p=r+g*δ)
    (hc : Nat.Coprime δ (n+2)) (a : Fin g) (ha : a≤mate r a) (ha0 : a≠0)
    (hpair : a≠mate r a) :
    Fin (2*(n+2)) ≃ {v : FreeVertex (g*(n+2)) r p // InBlock n r p a v} :=
  (canonicalOrder r a hpair δ hc).trans (blockEquiv n r p δ hp a ha ha0)

/-- The complete local signed geometry contract for this branch: all block
vertices occur once, adjacency is exact in both directions, no edge leaves
the block, and the cycle has at least four vertices. -/
theorem strict_cycle (n r p δ : ℕ) (hp : p=r+g*δ) (hpm : p<g*(n+2))
    (hc : Nat.Coprime δ (n+2)) (a : Fin g) (ha : a≤mate r a) (ha0 : a≠0)
    (hpair : a≠mate r a) :
    4≤2*(n+2) ∧
    (∀i j, (freeGraph (g*(n+2)) r p).Adj
      ((cycleEquiv n r p δ hp hc a ha ha0 hpair) i).val
      ((cycleEquiv n r p δ hp hc a ha ha0 hpair) j).val ↔ CycleAdjacent i j) ∧
    (∀x y : FreeVertex (g*(n+2)) r p, InBlock n r p a x →
      (freeGraph (g*(n+2)) r p).Adj x y → InBlock n r p a y) := by
  refine ⟨original_cycle_min n,?_,block_closed n r p δ hp hpm a⟩
  intro i j
  exact original_adjacency_iff n r p δ hp hpm hc a ha ha0 hpair i j

end SubmittedGenus.CapFourMass.SignedReflectionPaired
