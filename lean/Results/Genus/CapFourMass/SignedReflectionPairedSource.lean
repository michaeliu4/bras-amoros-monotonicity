import Results.Genus.CapFourMass.SignedReflectionPaired

/-! Original free-vertex meaning of the strict nonzero paired reflection
cycle. The map below is explicit and injective, with exact source adjacency;
it is not a claimed global layout or a canonical carry-label program. -/
namespace SubmittedGenus.CapFourMass.SignedReflectionPaired
open RawGraph RawGraph.SourceModel RawGraph.Topology RawGraph.PackedAcceptance
open ReflectionPairedOrbit

variable {g : ℕ} [NeZero g]

lemma paired_val_pos (n r : ℕ) (a : Fin g) (ha : a≤mate r a) (ha0 : a≠0)
    (x : PairedCosets (L:=n+2) r a) : 0<x.val.val := by
  have hn:=ReflectionComponentOrders.paired_nonzero n r a ha ha0 x
  apply Nat.pos_of_ne_zero
  intro he
  apply hn
  rw [←ZMod.natCast_zmod_val x.val,he,Nat.cast_zero]

/-- Explicit original one-based residue coordinates, with both pivots
excluded by the arithmetic coset theorem rather than a finite checker. -/
def vertex (n r p δ : ℕ) (hp : p=r+g*δ)
    (a : Fin g) (ha : a≤mate r a) (ha0 : a≠0)
    (x : PairedCosets (L:=n+2) r a) : FreeVertex (g*(n+2)) r p := by
  have hpos:=paired_val_pos n r a ha ha0 x
  have hlt:=ZMod.val_lt x.val
  have hxr : x.val.val≠r := by
    intro he
    exact pivot_coset_excluded r a ha ha0 x (by rw [he])
  have hxp : x.val.val≠p := by
    intro he
    apply pivot_coset_excluded r a ha ha0 x
    rw [he,hp]
    simp [Nat.add_mod,Nat.mul_mod]
  refine ⟨⟨x.val.val-1,by omega⟩,?_⟩
  unfold IsFree IsPivot
  dsimp only [physical]
  omega

@[simp] lemma physical_vertex (n r p δ : ℕ) (hp : p=r+g*δ)
    (a : Fin g) (ha : a≤mate r a) (ha0 : a≠0)
    (x : PairedCosets (L:=n+2) r a) :
    physical (vertex n r p δ hp a ha ha0 x).val=x.val.val := by
  change x.val.val-1+1=x.val.val
  have := paired_val_pos n r a ha ha0 x
  omega

@[simp] lemma cast_physical_vertex (n r p δ : ℕ) (hp : p=r+g*δ)
    (a : Fin g) (ha : a≤mate r a) (ha0 : a≠0)
    (x : PairedCosets (L:=n+2) r a) :
    (physical (vertex n r p δ hp a ha ha0 x).val : ZMod (g*(n+2)))=x.val := by
  rw [physical_vertex,ZMod.natCast_zmod_val]

theorem vertex_injective (n r p δ : ℕ) (hp : p=r+g*δ)
    (a : Fin g) (ha : a≤mate r a) (ha0 : a≠0) :
    Function.Injective (vertex n r p δ hp a ha ha0) := by
  intro x y he
  have hv:=congrArg (fun v : FreeVertex (g*(n+2)) r p=>
    (physical v.val : ZMod (g*(n+2)))) he
  simpa only [cast_physical_vertex,Subtype.val_inj] using hv

/-- The true ordinary graph relation on these vertices is exactly the
original two target sums, with self-pairs excluded. -/
theorem vertex_adjacent_iff (n r p δ : ℕ) (hp : p=r+g*δ) (hpm : p<g*(n+2))
    (a : Fin g) (ha : a≤mate r a) (ha0 : a≠0)
    (x y : PairedCosets (L:=n+2) r a) :
    (freeGraph (g*(n+2)) r p).Adj (vertex n r p δ hp a ha ha0 x)
      (vertex n r p δ hp a ha ha0 y) ↔
      x≠y ∧ (x.val+y.val=(r:ZMod (g*(n+2))) ∨ x.val+y.val=(p:ZMod (g*(n+2)))) := by
  have hrm : r<g*(n+2) := by omega
  change ((vertex n r p δ hp a ha ha0 x).val≠(vertex n r p δ hp a ha ha0 y).val ∧
    IsFree r p (vertex n r p δ hp a ha ha0 x).val ∧
    IsFree r p (vertex n r p δ hp a ha ha0 y).val ∧
    (TargetPair r (vertex n r p δ hp a ha ha0 x).val (vertex n r p δ hp a ha ha0 y).val ∨
     TargetPair p (vertex n r p δ hp a ha ha0 x).val (vertex n r p δ hp a ha ha0 y).val)) ↔ _
  rw [targetPair_iff_zmod hrm,targetPair_iff_zmod hpm]
  simp only [cast_physical_vertex,(vertex n r p δ hp a ha ha0 x).property,
    (vertex n r p δ hp a ha ha0 y).property,true_and]
  have hinj : Function.Injective (fun z=> (vertex n r p δ hp a ha ha0 z).val) :=
    Subtype.val_injective.comp (vertex_injective n r p δ hp a ha ha0)
  exact and_congr (not_congr hinj.eq_iff) Iff.rfl

/-- Uniform source-exact cycle ordering for every canonical nonzero paired
orbit. All consecutive and closing factors are genuine original edges. -/
theorem original_adjacency_iff (n r p δ : ℕ) (hp : p=r+g*δ) (hpm : p<g*(n+2))
    (hc : Nat.Coprime δ (n+2)) (a : Fin g) (ha : a≤mate r a) (ha0 : a≠0)
    (hpair : a≠mate r a) (i j : Fin (2*(n+2))) :
    (freeGraph (g*(n+2)) r p).Adj
      (vertex n r p δ hp a ha ha0 (canonicalOrder r a hpair δ hc i))
      (vertex n r p δ hp a ha ha0 (canonicalOrder r a hpair δ hc j)) ↔
      CycleAdjacent i j := by
  rw [vertex_adjacent_iff n r p δ hp hpm a ha ha0]
  constructor
  · rintro ⟨_,he⟩
    apply canonicalOrder_adjacent r a hpair δ hc i j
    simpa only [hp] using he
  · intro he
    refine ⟨?_,?_⟩
    · intro hij
      have hij':= (canonicalOrder r a hpair δ hc).injective hij
      subst j
      unfold CycleAdjacent at he
      have hi:=i.isLt
      omega
    · simpa only [hp] using pair_of_cycleAdjacent r a hpair δ hc i j he

end SubmittedGenus.CapFourMass.SignedReflectionPaired
