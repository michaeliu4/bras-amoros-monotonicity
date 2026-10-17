import Results.Genus.CapFiveMass.MatrixSource
import Results.Genus.CapFiveMass.ZeroExtension
import Results.Genus.RawGraph.RawComponents

/-!
# Actual raw-domain and reflection-edge domination

Every half weight here is extracted from the original raw compiler's Domain,
and every compatibility from its original edgeBound. Carry endpoint values
are proved at most four from physical reflection geometry, not postulated.
-/

noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFiveMass
namespace LocalSource
open RawGraph RawGraph.SourceModel

def domainHalf {m : ℕ} (r p : ℕ) (i : Fin (m - 1)) (z : ℝ) (v : BoundedState) : ℝ :=
  if Domain r p 5 i v.val then Real.sqrt (z ^ v.val) else 0

def edgeFactor {m : ℕ} (r p : ℕ) (i j : Fin (m - 1)) (v w : BoundedState) : ℝ :=
  if edgeBound r p 5 i j ≤ v.val + w.val then 1 else 0

def StrongEdge {m : ℕ} (r p : ℕ) (i j : Fin (m - 1)) : Prop :=
  physical i + physical j = r ∨ physical i + physical j = p

instance {m r p : ℕ} (i j : Fin (m - 1)) : Decidable (StrongEdge r p i j) := by
  unfold StrongEdge
  infer_instance

def sourceTransfer {m : ℕ} (r p : ℕ) (i j : Fin (m - 1)) : MatrixBounds.Controlled (ι := BoundedState) :=
  if StrongEdge r p i j then strongTransferSix else carryTransferSix

lemma domainHalf_nonneg {m r p : ℕ} (i : Fin (m - 1)) (z : ℝ) (v : BoundedState) :
    0 ≤ domainHalf r p i z v := by
  unfold domainHalf
  split_ifs
  · exact Real.sqrt_nonneg _
  · rfl

lemma domainHalf_sq {m r p : ℕ} (i : Fin (m - 1)) {z : ℝ} (hz : 0 ≤ z) (v : BoundedState) :
    domainHalf r p i z v ^ 2 = if Domain r p 5 i v.val then z ^ v.val else 0 := by
  unfold domainHalf
  split_ifs
  · exact Real.sq_sqrt (pow_nonneg hz _)
  · ring

lemma domain_bounds {m r p : ℕ} {i : Fin (m - 1)} (hi : IsFree r p i) {v : ℕ}
    (hv : Domain r p 5 i v) : 1 ≤ v ∧ v ≤ 5 := by
  have h := ((domain_iff_unary i v).mp hv).2 hi
  refine ⟨h.1, ?_⟩
  have hu := h.2.1
  unfold upper at hu
  split_ifs at hu <;> omega

lemma domain_carry_bound {m r p : ℕ} {i j : Fin (m - 1)}
    (hi : IsFree r p i) (hcarry : physical i + physical j = m + r ∨ physical i + physical j = m + p)
    (hrp : r < p) {v : ℕ} (hv : Domain r p 5 i v) : v ≤ 4 := by
  have hj := j.isLt
  have hh : ¬ physical i < r := by dsimp [physical] at *; omega
  have hu := ((domain_iff_unary i v).mp hv).2 hi |>.2.1
  simpa [upper, hh] using hu

lemma domain_zero_impossible {m r p : ℕ} {i : Fin (m - 1)} (hi : IsFree r p i) :
    ¬ Domain r p 5 i 0 := by
  intro h
  have := (domain_bounds hi h).1
  omega

lemma domainHalf_le_free {m r p : ℕ} {i : Fin (m - 1)} (hi : IsFree r p i)
    (z : ℝ) (v : BoundedState) : domainHalf r p i z v ≤ endpointVectorSix .free z v := by
  refine Fin.cases ?_ (fun v => ?_) v
  · simp [domainHalf, domain_zero_impossible hi, endpointVectorSix, zeroExtendVector]
  · simp only [domainHalf, endpointVectorSix, zeroExtendVector, Fin.cases_succ, endpointVector,
      vertexHalf, Fin.val_succ]
    split_ifs
    · rfl
    · exact Real.sqrt_nonneg _

lemma domainHalf_le_strong {m r p : ℕ} {i : Fin (m - 1)} (hi : IsFree r p i)
    (hloop : StrongLoop r p i) (z : ℝ) (v : BoundedState) :
    domainHalf r p i z v ≤ endpointVectorSix .strongLoop z v := by
  by_cases hd : Domain r p 5 i v.val
  · have hv := ((domain_iff_unary i v.val).mp hd).2 hi |>.2.2.1 hloop
    have hv0 : v ≠ 0 := by intro he; simp [he] at hv
    obtain ⟨v, rfl⟩ := Fin.exists_succ_eq.mpr hv0
    have hge : 3 ≤ v.val + 1 := by simp only [Fin.val_succ] at hv; omega
    simp only [Fin.val_succ] at hd
    simp [domainHalf, hd, endpointVectorSix, zeroExtendVector, endpointVector, vertexHalf, hge]
  · simpa [domainHalf, hd] using endpointSix_nonneg .strongLoop z v

lemma domainHalf_le_carry {m r p : ℕ} {i : Fin (m - 1)}
    (hp : Parameters m r p 5) (hi : IsFree r p i) (hloop : CarryLoop r p i)
    (z : ℝ) (v : BoundedState) :
    domainHalf r p i z v ≤ endpointVectorSix .carryLoop z v := by
  by_cases hd : Domain r p 5 i v.val
  · have hv := ((domain_iff_unary i v.val).mp hd).2 hi |>.2.2.2 hloop
    have hcarry : physical i + physical i = m + r ∨ physical i + physical i = m + p := by
      simpa only [CarryLoop, two_mul] using hloop
    have hup := domain_carry_bound hi hcarry hp.2.1 hd
    have hv0 : v ≠ 0 := by intro he; simp [he] at hv
    obtain ⟨v, rfl⟩ := Fin.exists_succ_eq.mpr hv0
    have hge : 2 ≤ v.val + 1 ∧ v.val + 1 ≤ 4 := by
      simp only [Fin.val_succ] at hv hup
      omega
    simp only [Fin.val_succ] at hd
    simp [domainHalf, hd, endpointVectorSix, zeroExtendVector, endpointVector, vertexHalf, hge]
  · simpa [domainHalf, hd] using endpointSix_nonneg .carryLoop z v

lemma sourceTransfer_nonneg {m r p : ℕ} (i j : Fin (m - 1)) (v w : BoundedState) :
    0 ≤ (sourceTransfer r p i j).matrix v w := by
  unfold sourceTransfer
  split_ifs <;> exact thresholdSix_nonneg _ _ v w

/-- Exact reflection geometry supplies the carry alphabet cutoff. -/
lemma split_edge_le_transfer {m r p : ℕ} (hp : Parameters m r p 5)
    {i j : Fin (m - 1)} (hadj : (RawGraph.Topology.rawGraph m r p).Adj i j)
    (v w : BoundedState) :
    domainHalf r p i radius v * edgeFactor r p i j v w * domainHalf r p j radius w ≤
      (sourceTransfer r p i j).matrix v w := by
  have hi : IsFree r p i := hadj.2.1
  have hj : IsFree r p j := hadj.2.2.1
  by_cases hdi : Domain r p 5 i v.val
  swap
  · simpa [domainHalf, hdi] using sourceTransfer_nonneg i j v w
  by_cases hdj : Domain r p 5 j w.val
  swap
  · simpa [domainHalf, hdj] using sourceTransfer_nonneg i j v w
  by_cases hedge : edgeBound r p 5 i j ≤ v.val + w.val
  swap
  · simpa [edgeFactor, hedge] using sourceTransfer_nonneg i j v w
  have hv0 : v ≠ 0 := by intro he; exact domain_zero_impossible hi (by simpa [he] using hdi)
  have hw0 : w ≠ 0 := by intro he; exact domain_zero_impossible hj (by simpa [he] using hdj)
  obtain ⟨v, rfl⟩ := Fin.exists_succ_eq.mpr hv0
  obtain ⟨w, rfl⟩ := Fin.exists_succ_eq.mpr hw0
  have hi' : ¬ IsPivot r p i := hi
  have hj' : ¬ IsPivot r p j := hj
  by_cases hs : StrongEdge r p i j
  · have hs' : physical i + physical j = r ∨ physical i + physical j = p := hs
    have he : edgeBound r p 5 i j = 5 := by simp [edgeBound, hi', hj', hadj.1, hs']
    have hel : eligible 5 v w := by
      rw [he] at hedge
      have hv := v.isLt
      have hw := w.isLt
      simp only [eligible, Fin.val_succ] at *
      omega
    simp only [Fin.val_succ] at hdi hdj hedge
    simp [domainHalf, edgeFactor, hdi, hdj, hedge, sourceTransfer, hs, strongTransferSix,
      extendControlled, strongTransfer, zeroExtend, thresholdMatrix, hel, vertexHalf]
  · have hc : physical i + physical j = m + r ∨ physical i + physical j = m + p := by
      rcases hadj.2.2.2 with hr | hp
      · rcases hr with hr | hr
        · exact (hs (Or.inl hr)).elim
        · exact Or.inl hr
      · rcases hp with hp | hp
        · exact (hs (Or.inr hp)).elim
        · exact Or.inr hp
    have hs' : ¬ (physical i + physical j = r ∨ physical i + physical j = p) := hs
    have he : edgeBound r p 5 i j = 4 := by simp [edgeBound, hi', hj', hadj.1, hs', hc]
    have hvi := domain_carry_bound hi hc hp.2.1 hdi
    have hwj := domain_carry_bound (j := i) hj (by simpa only [Nat.add_comm (physical i) (physical j)] using hc) hp.2.1 hdj
    have hel : eligible 4 v w := by
      rw [he] at hedge
      simp only [eligible, Fin.val_succ] at *
      omega
    simp only [Fin.val_succ] at hdi hdj hedge
    simp [domainHalf, edgeFactor, hdi, hdj, hedge, sourceTransfer, hs, carryTransferSix,
      extendControlled, carryTransfer, zeroExtend, thresholdMatrix, hel, vertexHalf]

end LocalSource
end SubmittedGenus.CapFiveMass
