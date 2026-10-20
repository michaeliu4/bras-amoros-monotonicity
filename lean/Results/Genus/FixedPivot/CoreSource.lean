import Results.Genus.FixedPivot.ConditionedSource
import Results.Genus.FixedPivot.SourceConstraints

/-! The exact cap-four finite-core factor is independent of multiplicity
throughout the original long-multiplicity region m>2p. -/
namespace SubmittedGenus.FixedPivot
open RawGraph RawGraph.SourceModel
open scoped BigOperators
noncomputable section

def CoreDomain (r p : ℕ) (k : Fin p) (v : ℕ) : Prop :=
  ((k.val + 1 = r ∨ k.val + 1 = p) → v = 4) ∧
    (¬ (k.val + 1 = r ∨ k.val + 1 = p) →
      1 ≤ v ∧ v ≤ (if k.val + 1 < r then 4 else 3) ∧
        ((2 * (k.val + 1) = r ∨ 2 * (k.val + 1) = p) → 4 ≤ 2 * v))

def coreStrongBound (r p : ℕ) (k l : Fin p) : ℕ :=
  if (k.val + 1 = r ∨ k.val + 1 = p) ∨ (l.val + 1 = r ∨ l.val + 1 = p) ∨ k = l then 0
  else if (k.val + 1) + (l.val + 1) = r ∨ (k.val + 1) + (l.val + 1) = p then 4 else 0

def StableCoreAllowed (r p : ℕ) (x : Fin p → Fin 5) : Prop :=
  (∀ k, CoreDomain r p k (x k).val) ∧
    ∀ k l, coreStrongBound r p k l ≤ (x k).val + (x l).val

instance (r p : ℕ) (k : Fin p) (v : ℕ) : Decidable (CoreDomain r p k v) := by
  unfold CoreDomain; infer_instance
instance (r p : ℕ) (x : Fin p → Fin 5) : Decidable (StableCoreAllowed r p x) := by
  unfold StableCoreAllowed; infer_instance

def stableCoreTerm (r p : ℕ) (x : Fin p → Fin 5) : Polynomial ℕ :=
  if StableCoreAllowed r p x then Polynomial.X ^ (∑ k, (x k).val) else 0

lemma conditioning_core_domain {m r p : ℕ} (hp : Parameters m r p 4) (hm : 2 * p < m)
    (k : Fin p) (v : ℕ) :
    Domain r p 4 (RawGraph.Conditioning.coreVertex (conditioningLayout hp hm) k) v ↔
      CoreDomain r p k v := by
  have hk := k.isLt
  have hc : ¬ CarryLoop r p (RawGraph.Conditioning.coreVertex (conditioningLayout hp hm) k) := by
    unfold CarryLoop
    rw [conditioning_core_physical]
    omega
  rw [domain_iff_unary]
  simp only [Unary, IsFree, IsPivot, StrongLoop, upper, conditioning_core_physical, hc,
    false_implies, and_true]
  rfl

lemma conditioning_core_bound {m r p : ℕ} (hp : Parameters m r p 4) (hm : 2 * p < m)
    (k l : Fin p) :
    edgeBound r p 4 (RawGraph.Conditioning.coreVertex (conditioningLayout hp hm) k)
      (RawGraph.Conditioning.coreVertex (conditioningLayout hp hm) l) = coreStrongBound r p k l := by
  let L := conditioningLayout hp hm
  have hk : physical (RawGraph.Conditioning.coreVertex L k) ≤ p := by
    rw [conditioning_core_physical]; have := k.isLt; omega
  have hl : physical (RawGraph.Conditioning.coreVertex L l) ≤ p := by
    rw [conditioning_core_physical]; have := l.isLt; omega
  have hij : RawGraph.Conditioning.coreVertex L k = RawGraph.Conditioning.coreVertex L l ↔ k = l := by
    constructor
    · intro h
      exact Sum.inl.inj (L.label.injective h)
    · exact congrArg (RawGraph.Conditioning.coreVertex L)
  rw [core_edgeBound hm _ _ hk hl]
  change (if IsPivot r p (RawGraph.Conditioning.coreVertex L k) ∨
    IsPivot r p (RawGraph.Conditioning.coreVertex L l) ∨
      RawGraph.Conditioning.coreVertex L k = RawGraph.Conditioning.coreVertex L l then 0 else
    if physical (RawGraph.Conditioning.coreVertex L k) + physical (RawGraph.Conditioning.coreVertex L l) = r ∨
      physical (RawGraph.Conditioning.coreVertex L k) + physical (RawGraph.Conditioning.coreVertex L l) = p then 4 else 0) = _
  simp only [IsPivot, hij, L, conditioning_core_physical, coreStrongBound]
  split_ifs <;> rfl

/-- No multiplicity remains in the complete finite-core admissibility test. -/
lemma conditioning_core_allowed {m r p : ℕ} (hp : Parameters m r p 4) (hm : 2 * p < m)
    (x : Fin p → Fin 5) :
    RawGraph.Conditioning.CoreAllowed (conditioningLayout hp hm) r p 4 x ↔ StableCoreAllowed r p x := by
  unfold RawGraph.Conditioning.CoreAllowed StableCoreAllowed
  simp_rw [conditioning_core_domain, conditioning_core_bound]

lemma conditioning_core_term {m r p : ℕ} (hp : Parameters m r p 4) (hm : 2 * p < m)
    (x : Fin p → Fin 5) :
    RawGraph.Conditioning.coreTerm (conditioningLayout hp hm) r p 4 x = stableCoreTerm r p x := by
  unfold RawGraph.Conditioning.coreTerm stableCoreTerm
  simp only [conditioning_core_allowed]

/-- The exact original raw source is a contraction of a multiplicity-independent
finite core with the original carry-tail transfer kernels. -/
theorem rawPolynomial_eq_stable_core_carry {m r p : ℕ} (hp : Parameters m r p 4)
    (hm : 2 * p < m) :
    rawPolynomial m r p 4 = ∑ x : Fin p → Fin 5,
      stableCoreTerm r p x * ∏ c : TailRepresentative hp,
        RawGraph.Conditioning.componentRun (conditioningLayout hp hm) r p 4 x c := by
  classical
  rw [rawPolynomial_eq_core_carry_transfers hp hm]
  simp_rw [conditioning_core_term]

end
end SubmittedGenus.FixedPivot
