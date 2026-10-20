import Results.Genus.CapFourMass.SignedReflectionFixed

/-! Uniform source-exact geometry of fixed nonzero reflection paths. Both
fixed pivots lie outside these arithmetic blocks. The zero block is excluded. -/
namespace SubmittedGenus.CapFourMass.SignedReflectionFixed
open RawGraph RawGraph.SourceModel RawGraph.Topology RawGraph.PackedAcceptance
open ReflectionCoset ReflectionPairedOrbit ReflectionComponentOrders
open SignedReflectionPaired

variable {g : ℕ} [NeZero g]

/-- A fixed orbit's two nominal cosets are exactly the same source coset. -/
def fixedCosetEquiv (n r : ℕ) (a : Fin g) (hfix : a=mate r a) :
    Coset g (n+2) a ≃ PairedCosets (L:=n+2) r a where
  toFun x := ⟨x.val,Or.inl x.property⟩
  invFun x := ⟨x.val,x.property.elim id (fun h=>h.trans (congrArg Fin.val hfix.symm))⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The full fixed reflection order expressed in the shared paired-block
interface. Its labels remain the original physical residues. -/
def residueOrder (n r : ℕ) (a : Fin g) (hfix : a=mate r a)
    (δ : ℕ) (hc : Nat.Coprime δ (n+2)) : Fin (n+2) ≃ PairedCosets (L:=n+2) r a :=
  (ReflectionFixedOrbit.order n a (r:ZMod (g*(n+2)))
    (fixed_origin n r a hfix) (gapUnit n δ hc)).trans (fixedCosetEquiv n r a hfix)

/-- Explicit bijection onto every original free vertex in the nonzero fixed
block. No pivot deletion or artificial neutral bridge occurs here. -/
def pathEquiv (n r p δ : ℕ) (hp : p=r+g*δ)
    (hc : Nat.Coprime δ (n+2)) (a : Fin g) (ha : a≤mate r a) (ha0 : a≠0)
    (hfix : a=mate r a) :
    Fin (n+2) ≃ {v : FreeVertex (g*(n+2)) r p // InBlock n r p a v} :=
  (residueOrder n r a hfix δ hc).trans (blockEquiv n r p δ hp a ha ha0)

/-- Exact original ordinary adjacency, in both directions. -/
theorem original_adjacency_iff (n r p δ : ℕ) (hp : p=r+g*δ) (hpm : p<g*(n+2))
    (hc : Nat.Coprime δ (n+2)) (a : Fin g) (ha : a≤mate r a) (ha0 : a≠0)
    (hfix : a=mate r a) (i j : Fin (n+2)) :
    (freeGraph (g*(n+2)) r p).Adj
      ((pathEquiv n r p δ hp hc a ha ha0 hfix) i).val
      ((pathEquiv n r p δ hp hc a ha ha0 hfix) j).val ↔
      (i.val+1=j.val ∨ j.val+1=i.val) := by
  change (freeGraph (g*(n+2)) r p).Adj
    (vertex n r p δ hp a ha ha0 (residueOrder n r a hfix δ hc i))
    (vertex n r p δ hp a ha ha0 (residueOrder n r a hfix δ hc j)) ↔ _
  rw [vertex_adjacent_iff n r p δ hp hpm a ha ha0]
  have hne : residueOrder n r a hfix δ hc i≠residueOrder n r a hfix δ hc j ↔ i≠j :=
    not_congr (residueOrder n r a hfix δ hc).injective.eq_iff
  rw [hne]
  exact (adjacent_iff_pair n a (r:ZMod (g*(n+2))) (p:ZMod (g*(n+2)))
    (fixed_origin n r a hfix) (gapUnit n δ hc) (gap_value n r p δ hc hp) i j).symm

/-- The complete local signed path contract: original free-vertex bijection,
two-way adjacency, and no original graph edge leaving the block. -/
theorem strict_path (n r p δ : ℕ) (hp : p=r+g*δ) (hpm : p<g*(n+2))
    (hc : Nat.Coprime δ (n+2)) (a : Fin g) (ha : a≤mate r a) (ha0 : a≠0)
    (hfix : a=mate r a) :
    (∀i j, (freeGraph (g*(n+2)) r p).Adj
      ((pathEquiv n r p δ hp hc a ha ha0 hfix) i).val
      ((pathEquiv n r p δ hp hc a ha ha0 hfix) j).val ↔
      (i.val+1=j.val ∨ j.val+1=i.val)) ∧
    (∀x y : FreeVertex (g*(n+2)) r p, InBlock n r p a x →
      (freeGraph (g*(n+2)) r p).Adj x y → InBlock n r p a y) :=
  ⟨original_adjacency_iff n r p δ hp hpm hc a ha ha0 hfix,
    block_closed n r p δ hp hpm a⟩

end SubmittedGenus.CapFourMass.SignedReflectionFixed
