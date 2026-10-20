import Results.Genus.RawGraph.PackedAcceptance.ReflectionComponentOrders
import Results.Genus.RawGraph.PackedAcceptance.ModularReflection
import Results.Genus.CapFourMass.ExecutableModeLayout

/-! Strict arithmetic geometry for the nonzero paired reflection components.
This supplies the reverse adjacency direction missing from scalar coverage.
It does not delete the zero-orbit pivots or accept any numerical prefix. -/
namespace SubmittedGenus.CapFourMass.SignedReflectionPaired
open RawGraph RawGraph.SourceModel RawGraph.Topology RawGraph.PackedAcceptance
open ReflectionPairedOrbit

variable {g L : ℕ} [NeZero g] [NeZero L]

lemma even_odd_adjacent_iff (k l : Fin L) :
    CycleAdjacent ((parityEquiv L).symm (false,k))
      ((parityEquiv L).symm (true,l)) ↔ k=l ∨ k=next l := by
  have hk:=k.isLt
  have hl:=l.isLt
  simp only [CycleAdjacent,parityEquiv_symm_even,parityEquiv_symm_odd,
    Fin.ext_iff,next]
  by_cases h : l.val+1<L
  · rw [Nat.mod_eq_of_lt h]
    omega
  · have he : l.val+1=L := by omega
    rw [he,Nat.mod_self]
    omega

/-- Every consecutive or closing pair is a real original reflection pair;
this is the converse of the previously accepted coverage theorem. -/
theorem pair_of_cycleAdjacent (r : ℕ) (a : Fin g) (ha : a≠mate r a)
    (δ : ℕ) (hc : Nat.Coprime δ L) (i j : Fin (2*L))
    (h : CycleAdjacent i j) :
    (canonicalOrder r a ha δ hc i).val+(canonicalOrder r a ha δ hc j).val=
      (r : ZMod (g*L)) ∨
    (canonicalOrder r a ha δ hc i).val+(canonicalOrder r a ha δ hc j).val=
      ((r+g*δ : ℕ) : ZMod (g*L)) := by
  obtain ⟨⟨bi,k⟩,rfl⟩ := (parityEquiv L).symm.surjective i
  obtain ⟨⟨bj,l⟩,rfl⟩ := (parityEquiv L).symm.surjective j
  cases bi <;> cases bj
  · simp only [CycleAdjacent,parityEquiv_symm_even] at h
    omega
  · rcases (even_odd_adjacent_iff k l).mp h with he|he
    · subst k
      exact Or.inl (canonicalOrder_even_odd_sum r a ha δ hc l)
    · subst k
      exact Or.inr (canonicalOrder_next_odd_sum r a ha δ hc l)
  · rcases (even_odd_adjacent_iff l k).mp h.symm with he|he
    · subst l
      exact Or.inl (by simpa only [add_comm] using canonicalOrder_even_odd_sum r a ha δ hc k)
    · subst l
      exact Or.inr (by simpa only [add_comm] using canonicalOrder_next_odd_sum r a ha δ hc k)
  · simp only [CycleAdjacent,parityEquiv_symm_odd] at h
    omega

/-- Exact two-way residue adjacency, before any numerical erasure. -/
theorem cycleAdjacent_iff_pair (r : ℕ) (a : Fin g) (ha : a≠mate r a)
    (δ : ℕ) (hc : Nat.Coprime δ L) (i j : Fin (2*L)) :
    CycleAdjacent i j ↔
      (canonicalOrder r a ha δ hc i).val+(canonicalOrder r a ha δ hc j).val=
        (r : ZMod (g*L)) ∨
      (canonicalOrder r a ha δ hc i).val+(canonicalOrder r a ha δ hc j).val=
        ((r+g*δ : ℕ) : ZMod (g*L)) :=
  ⟨pair_of_cycleAdjacent r a ha δ hc i j,
    canonicalOrder_adjacent r a ha δ hc i j⟩

lemma mate_zero_val (r : ℕ) : (mate r (0:Fin g)).val=r%g := by
  simp [mate,partner]

/-- A canonical nonzero pair cannot contain the coset of either pivot. -/
lemma pivot_coset_excluded (r : ℕ) (a : Fin g) (ha : a≤mate r a) (ha0 : a≠0)
    (x : PairedCosets (L:=L) r a) : x.val.val%g≠r%g := by
  intro he
  have hinv:=partner_involutive g r (NeZero.pos g)
  have hinj:=hinv.injective
  have hm0 : mate r a≠0 := by
    intro hz
    have hle : a≤0 := by simpa only [hz] using ha
    exact ha0 (le_antisymm hle (Fin.zero_le a))
  rw [←mate_zero_val r] at he
  rcases x.property with hx|hx
  · have hA : a=mate r 0 := Fin.ext (hx.symm.trans he)
    apply hm0
    rw [hA]
    exact hinv 0
  · exact ha0 (hinj (Fin.ext (hx.symm.trans he)))

/-- All paired cycles have at least four vertices in original gcd coordinates. -/
theorem original_cycle_min (n : ℕ) : 4≤2*(n+2) := by omega

end SubmittedGenus.CapFourMass.SignedReflectionPaired
