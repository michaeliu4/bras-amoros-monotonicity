import Results.Genus.CapFourMass.SignedReflectionFreeBlock

/-! The zero paired orbit becomes one strict free path after deleting its
zero residue and both fixed pivots. Singleton paths are retained exactly. -/
namespace SubmittedGenus.CapFourMass.SignedReflectionZeroPaired
open RawGraph RawGraph.SourceModel RawGraph.Topology RawGraph.PackedAcceptance
open ReflectionPairedOrbit
open SignedReflectionFreeBlock

variable {g : ℕ} [NeZero g]

def firstPivotIndex (n : ℕ) : Fin (2*(n+2)) := ⟨1,by omega⟩
def lastPivotIndex (n : ℕ) : Fin (2*(n+2)) := ⟨2*(n+2)-1,by omega⟩

theorem order_first_pivot (n r δ : ℕ) (hpair : (0:Fin g)≠mate r 0)
    (hc : Nat.Coprime δ (n+2)) :
    (canonicalOrder r 0 hpair δ hc (firstPivotIndex n)).val=(r:ZMod (g*(n+2))) := by
  have he:=(canonicalOrder_even_odd_sum r (0:Fin g) hpair δ hc (0:Fin (n+2)))
  have hzero : (parityEquiv (n+2)).symm (false,(0:Fin (n+2)))=0 := Fin.ext rfl
  have hone : (parityEquiv (n+2)).symm (true,(0:Fin (n+2)))=firstPivotIndex n := Fin.ext rfl
  rw [hzero,hone,canonicalOrder_zero,zero_add] at he
  exact he

theorem order_last_pivot (n r p δ : ℕ) (hp : p=r+g*δ)
    (hpair : (0:Fin g)≠mate r 0) (hc : Nat.Coprime δ (n+2)) :
    (canonicalOrder r 0 hpair δ hc (lastPivotIndex n)).val=(p:ZMod (g*(n+2))) := by
  let k : Fin (n+2):=⟨n+1,by omega⟩
  have hn : next k=0 := by apply Fin.ext; simp [next,k]
  have hzero : (parityEquiv (n+2)).symm (false,(0:Fin (n+2)))=0 := Fin.ext rfl
  have hlast : (parityEquiv (n+2)).symm (true,k)=lastPivotIndex n := by
    apply Fin.ext
    change 2*(n+1)+1=2*(n+2)-1
    omega
  have he:=canonicalOrder_next_odd_sum r (0:Fin g) hpair δ hc k
  rw [hn,hzero,hlast,canonicalOrder_zero,zero_add,←hp] at he
  exact he

def trimIndex (n : ℕ) (i : Fin (2*n+1)) : Fin (2*(n+2)) := ⟨i.val+2,by have:=i.isLt; omega⟩

/-- The surviving interval is positions2 throughN-2, with no wraparound. -/
def trimEquiv (n : ℕ) : Fin (2*n+1) ≃ {j : Fin (2*(n+2)) // 2≤j.val ∧ j.val+1<2*(n+2)} where
  toFun i := ⟨trimIndex n i,by have:=i.isLt; dsimp [trimIndex]; omega⟩
  invFun j := ⟨j.val.val-2,by have:=j.property; omega⟩
  left_inv i := by apply Fin.ext; dsimp [trimIndex]; omega
  right_inv j := by apply Subtype.ext; apply Fin.ext; have:=j.property; dsimp [trimIndex]; omega

/-- Exactly zero and the two pivots are deleted; all other original residues
in this block are retained once. -/
theorem keep_iff (n r p δ : ℕ) (hp : p=r+g*δ)
    (hpair : (0:Fin g)≠mate r 0) (hc : Nat.Coprime δ (n+2)) (j : Fin (2*(n+2))) :
    (2≤j.val ∧ j.val+1<2*(n+2)) ↔ Keep n r p (canonicalOrder r 0 hpair δ hc j) := by
  let e:=canonicalOrder r (0:Fin g) hpair δ hc
  have hz : (e 0).val=0 := canonicalOrder_zero r hpair δ hc
  have hr : (e (firstPivotIndex n)).val=(r:ZMod (g*(n+2))) := order_first_pivot n r δ hpair hc
  have hplast : (e (lastPivotIndex n)).val=(p:ZMod (g*(n+2))) := order_last_pivot n r p δ hp hpair hc
  change (2≤j.val ∧ j.val+1<2*(n+2)) ↔ ((e j).val≠0 ∧ (e j).val≠(r:ZMod (g*(n+2))) ∧ (e j).val≠(p:ZMod (g*(n+2))))
  constructor
  · intro hj
    refine ⟨?_,?_,?_⟩
    · intro he
      have hh:=congrArg Fin.val (e.injective (Subtype.ext (he.trans hz.symm)))
      change j.val=0 at hh
      omega
    · intro he
      have hh:=congrArg Fin.val (e.injective (Subtype.ext (he.trans hr.symm)))
      change j.val=1 at hh
      omega
    · intro he
      have hh:=congrArg Fin.val (e.injective (Subtype.ext (he.trans hplast.symm)))
      change j.val=2*(n+2)-1 at hh
      omega
  · intro hj
    have h0 : j.val≠0 := by
      intro he
      have hh : j=0 := Fin.ext he
      exact hj.1 (hh ▸ hz)
    have h1 : j.val≠1 := by
      intro he
      have hh : j=firstPivotIndex n := Fin.ext he
      exact hj.2.1 (hh ▸ hr)
    have hl : j.val+1≠2*(n+2) := by
      intro he
      have hh : j=lastPivotIndex n := Fin.ext (by dsimp [lastPivotIndex]; omega)
      exact hj.2.2 (hh ▸ hplast)
    have :=j.isLt
    omega

/-- Computable source bijection after deletion of exactly positions0,1,last. -/
def residueEquiv (n r p δ : ℕ) (hp : p=r+g*δ)
    (hpair : (0:Fin g)≠mate r 0) (hc : Nat.Coprime δ (n+2)) :
    Fin (2*n+1) ≃ FreeResidue n r p (0:Fin g) :=
  (trimEquiv n).trans ((canonicalOrder r 0 hpair δ hc).subtypeEquiv
    (fun j=>keep_iff n r p δ hp hpair hc j))

@[simp] lemma residueEquiv_value (n r p δ : ℕ) (hp : p=r+g*δ)
    (hpair : (0:Fin g)≠mate r 0) (hc : Nat.Coprime δ (n+2)) (i : Fin (2*n+1)) :
    (residueEquiv n r p δ hp hpair hc i).val.val=
      (canonicalOrder r 0 hpair δ hc (trimIndex n i)).val := rfl

/-- Complete original free-vertex path for the paired zero orbit. -/
def pathEquiv (n r p δ : ℕ) (hp : p=r+g*δ) (hrm : r<g*(n+2)) (hpm : p<g*(n+2))
    (hpair : (0:Fin g)≠mate r 0) (hc : Nat.Coprime δ (n+2)) :
    Fin (2*n+1) ≃ {v : FreeVertex (g*(n+2)) r p // SignedReflectionPaired.InBlock n r p 0 v} :=
  (residueEquiv n r p δ hp hpair hc).trans (SignedReflectionFreeBlock.equiv n r p hrm hpm 0)

/-- Exact two-way adjacency after removing both pivot neighbors of zero.
No neutral shortcut and no closing edge is introduced. -/
theorem original_adjacency_iff (n r p δ : ℕ) (hp : p=r+g*δ)
    (hrm : r<g*(n+2)) (hpm : p<g*(n+2))
    (hpair : (0:Fin g)≠mate r 0) (hc : Nat.Coprime δ (n+2)) (i j : Fin (2*n+1)) :
    (freeGraph (g*(n+2)) r p).Adj
      ((pathEquiv n r p δ hp hrm hpm hpair hc) i).val
      ((pathEquiv n r p δ hp hrm hpm hpair hc) j).val ↔
      (i.val+1=j.val ∨ j.val+1=i.val) := by
  change (freeGraph (g*(n+2)) r p).Adj
    (vertex n r p 0 (residueEquiv n r p δ hp hpair hc i))
    (vertex n r p 0 (residueEquiv n r p δ hp hpair hc j)) ↔ _
  rw [vertex_adjacent_iff n r p hrm hpm 0]
  simp only [residueEquiv_value]
  constructor
  · rintro ⟨_,he⟩
    have hh:=canonicalOrder_adjacent r (0:Fin g) hpair δ hc (trimIndex n i) (trimIndex n j)
      (by simpa only [hp] using he)
    dsimp only [CycleAdjacent,trimIndex] at hh
    omega
  · intro hij
    refine ⟨?_,?_⟩
    · intro he
      have hh:=congrArg Fin.val ((residueEquiv n r p δ hp hpair hc).injective he)
      omega
    · have hcycle : CycleAdjacent (trimIndex n i) (trimIndex n j) := by
        dsimp only [CycleAdjacent,trimIndex]
        omega
      simpa only [hp] using SignedReflectionPaired.pair_of_cycleAdjacent r (0:Fin g) hpair δ hc
        (trimIndex n i) (trimIndex n j) hcycle

/-- Whole local strict path contract for the paired zero block. -/
theorem strict_path (n r p δ : ℕ) (hp : p=r+g*δ)
    (hrm : r<g*(n+2)) (hpm : p<g*(n+2))
    (hpair : (0:Fin g)≠mate r 0) (hc : Nat.Coprime δ (n+2)) :
    (∀i j, (freeGraph (g*(n+2)) r p).Adj
      ((pathEquiv n r p δ hp hrm hpm hpair hc) i).val
      ((pathEquiv n r p δ hp hrm hpm hpair hc) j).val ↔
      (i.val+1=j.val ∨ j.val+1=i.val)) ∧
    (∀x y : FreeVertex (g*(n+2)) r p, SignedReflectionPaired.InBlock n r p 0 x →
      (freeGraph (g*(n+2)) r p).Adj x y → SignedReflectionPaired.InBlock n r p 0 y) :=
  ⟨original_adjacency_iff n r p δ hp hrm hpm hpair hc,
    SignedReflectionPaired.block_closed n r p δ hp hpm 0⟩

end SubmittedGenus.CapFourMass.SignedReflectionZeroPaired
