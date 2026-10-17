import Results.Genus.CapFourMass.SourceCoreFactorization

/-! Exact ordinary core factors, with each unordered physical edge used once. -/
namespace SubmittedGenus.CapFourMass.SourceCoreFactorization
open RawGraph RawGraph.SourceModel RawGraph.Topology FixedPivot
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

/-- The positive ordinary constraints in upper physical-coordinate order. -/
def coreEdgeSet {r N d : ℕ} (hN : d < N) (c : SourceComponent r N d) :
    Finset (CoreAt hN c × CoreAt hN c) :=
  Finset.univ.filter (fun ij => ij.1.val.val.val < ij.2.val.val.val ∧
    0 < coreStrongBound r (r+d) ij.1.val.val ij.2.val.val)

@[simp] theorem mem_coreEdgeSet {r N d : ℕ} (hN : d < N) (c : SourceComponent r N d)
    (ij : CoreAt hN c × CoreAt hN c) :
    ij ∈ coreEdgeSet hN c ↔ ij.1.val.val.val < ij.2.val.val.val ∧
      0 < coreStrongBound r (r+d) ij.1.val.val ij.2.val.val := by
  simp [coreEdgeSet]

/-- Symmetric and vacuous constraints are removed exactly, before taking any
absolute values or interpreting the other component factors. -/
theorem componentCoreAllowed_iff_upper {r N d : ℕ} (hN : d < N)
    (c : SourceComponent r N d) (x : CoreAt hN c → State) :
    componentCoreAllowed hN c x ↔
      (∀ k, CoreDomain r (r+d) k.val.val ((x k).val+1)) ∧
      ∀ ij ∈ coreEdgeSet hN c,
        coreStrongBound r (r+d) ij.1.val.val ij.2.val.val ≤
          ((x ij.1).val+1)+((x ij.2).val+1) := by
  constructor
  · intro h
    exact ⟨h.1, fun ij _ => h.2 ij.1 ij.2⟩
  · rintro ⟨hu, he⟩
    refine ⟨hu, fun i j => ?_⟩
    by_cases hz : coreStrongBound r (r+d) i.val.val j.val.val = 0
    · rw [hz]; exact Nat.zero_le _
    have hp := Nat.pos_of_ne_zero hz
    rcases lt_trichotomy i.val.val.val j.val.val.val with hij | hij | hij
    · exact he (i,j) ((mem_coreEdgeSet hN c _).mpr ⟨hij,hp⟩)
    · have hf : i.val.val=j.val.val := Fin.ext hij
      have hz' : coreStrongBound r (r+d) i.val.val j.val.val=0 := by
        simp [coreStrongBound,hf]
      exact False.elim (hz hz')
    · have hs := coreStrongBound_symm (r:=r) (p:=r+d) i.val.val j.val.val
      have hp' : 0 < coreStrongBound r (r+d) j.val.val i.val.val := by simpa only [← hs] using hp
      have he' := he (j,i) ((mem_coreEdgeSet hN c _).mpr ⟨hij,hp'⟩)
      simpa only [hs,Nat.add_comm] using he'

private theorem prod_gate_on {I R : Type*} [CommMonoidWithZero R]
    (s : Finset I) (P : I → Prop) [DecidablePred P] (f : I → R) :
    (∏ i ∈ s, if P i then f i else 0)=
      if ∀ i ∈ s, P i then ∏ i ∈ s, f i else 0 := by
  classical
  by_cases h : ∀ i ∈ s, P i
  · rw [if_pos h]
    exact Finset.prod_congr rfl (fun i hi => if_pos (h i hi))
  · rw [if_neg h]
    push Not at h
    obtain ⟨i,hi,hp⟩ := h
    exact Finset.prod_eq_zero hi (if_neg hp)

/-- One full weight per physical core vertex and one gate per unordered ordinary
edge. The identity is valid in every commutative semiring. -/
theorem componentCoreTerm_eq_vertex_edge_product {R : Type*} [CommSemiring R]
    {r N d : ℕ} (hN : d < N) (z : R) (c : SourceComponent r N d)
    (x : CoreAt hN c → State) :
    componentCoreTerm hN z c x =
      (∏ k : CoreAt hN c,
        if CoreDomain r (r+d) k.val.val ((x k).val+1)
        then z^((x k).val+1) else 0) *
      ∏ ij ∈ coreEdgeSet hN c,
        (if coreStrongBound r (r+d) ij.1.val.val ij.2.val.val ≤
          ((x ij.1).val+1)+((x ij.2).val+1) then (1 : R) else 0) := by
  rw [Factorization.prod_gate,prod_gate_on,Finset.prod_pow_eq_pow_sum]
  simp only [Finset.prod_const_one]
  unfold componentCoreTerm
  by_cases hu : ∀ k : CoreAt hN c, CoreDomain r (r+d) k.val.val ((x k).val+1)
  · rw [if_pos hu]
    by_cases he : ∀ ij ∈ coreEdgeSet hN c,
        coreStrongBound r (r+d) ij.1.val.val ij.2.val.val ≤
          ((x ij.1).val+1)+((x ij.2).val+1)
    · rw [if_pos he,if_pos ((componentCoreAllowed_iff_upper hN c x).mpr ⟨hu,he⟩),mul_one]
    · rw [if_neg he,if_neg (fun h => he ((componentCoreAllowed_iff_upper hN c x).mp h).2),mul_zero]
  · rw [if_neg hu,if_neg (fun h => hu ((componentCoreAllowed_iff_upper hN c x).mp h).1),zero_mul]

end
end SubmittedGenus.CapFourMass.SourceCoreFactorization
