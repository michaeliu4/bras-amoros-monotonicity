import Results.Genus.CapFourMass.IndexedModePrefixAggregation

/-! Bounded row chunks assemble into the exact original prefix. The source
sums remain abstract throughout; the only arithmetic is interval addition.
These lemmas also permit rounded stored row/chunk boxes to be reused. -/
open scoped BigOperators
namespace SubmittedGenus.CapFourMass.Interval.IndexedModePrefix

theorem sumBox_Ico_consecutive (b : ℕ → Box) {a c e : ℕ} (hac : a ≤ c) (hce : c ≤ e) :
    add (sumBox (Finset.Ico a c) b) (sumBox (Finset.Ico c e) b) =
      sumBox (Finset.Ico a e) b := by
  simp only [sumBox, add, Finset.sum_Ico_consecutive _ hac hce]

theorem sumBox_range_add_Ico (b : ℕ → Box) {P Q : ℕ} (hPQ : P ≤ Q) :
    add (sumBox (Finset.range P) b) (sumBox (Finset.Ico P Q) b) =
      sumBox (Finset.range Q) b := by
  simpa only [Finset.range_eq_Ico] using sumBox_Ico_consecutive b (Nat.zero_le P) hPQ

def pureChunk (b : BaseBoxes) (den : Box) (start stop : ℕ) : Box :=
  pureRows b den (Finset.Ico start stop)

def mixedChunk (b : BaseBoxes) (den : ℕ → Box) (start stop : ℕ) : Box :=
  mixedRows b den (Finset.Ico start stop)

theorem pureChunk_contains (b : BaseBoxes) (den : Box) (start stop : ℕ)
    (hbase : ∀ p ∈ Finset.Ico start stop, ∀ r ∈ Finset.Ico 1 p, ∀ n : Fin 2,
      Contains (b r (p-r) n.val) (sourcePureSeries r (p-r) n.val))
    (hden : Contains den (1-(normalizer*lam)^2)) (hpos : 0 < den.lo) :
    Contains (pureChunk b den start stop) (∑ p ∈ Finset.Ico start stop, pureSourceRow p) :=
  pureRows_contains b den _ hbase hden hpos

theorem mixedChunk_contains (b : BaseBoxes) (den : ℕ → Box) (start stop : ℕ)
    (hbase : ∀ p ∈ Finset.Ico start stop, ∀ r ∈ Finset.Ico 1 p, ∀ n : Fin (2*(p-r)),
      Contains (b r (p-r) n.val) (sourceMixedSeries r (p-r) n.val))
    (hden : ∀ p ∈ Finset.Ico start stop, ∀ r ∈ Finset.Ico 1 p, Contains (den (p-r))
      (1-(normalizer*lam)^(2*(p-r))*rho^2))
    (hpos : ∀ p ∈ Finset.Ico start stop, ∀ r ∈ Finset.Ico 1 p, 0 < (den (p-r)).lo) :
    Contains (mixedChunk b den start stop) (∑ p ∈ Finset.Ico start stop, mixedSourceRow p) :=
  mixedRows_contains b den _ hbase hden hpos

theorem pureChunk_add (b : BaseBoxes) (den : Box) {a c e : ℕ} (hac : a ≤ c) (hce : c ≤ e) :
    add (pureChunk b den a c) (pureChunk b den c e) = pureChunk b den a e :=
  sumBox_Ico_consecutive _ hac hce

theorem mixedChunk_add (b : BaseBoxes) (den : ℕ → Box) {a c e : ℕ} (hac : a ≤ c) (hce : c ≤ e) :
    add (mixedChunk b den a c) (mixedChunk b den c e) = mixedChunk b den a e :=
  sumBox_Ico_consecutive _ hac hce

theorem purePrefix_add_chunk (b : BaseBoxes) (den : Box) {P Q : ℕ} (hPQ : P ≤ Q) :
    add (purePrefix b den P) (pureChunk b den (P+1) (Q+1)) = purePrefix b den Q :=
  sumBox_range_add_Ico _ (Nat.succ_le_succ hPQ)

theorem mixedPrefix_add_chunk (b : BaseBoxes) (den : ℕ → Box) {P Q : ℕ} (hPQ : P ≤ Q) :
    add (mixedPrefix b den P) (mixedChunk b den (P+1) (Q+1)) = mixedPrefix b den Q :=
  sumBox_range_add_Ico _ (Nat.succ_le_succ hPQ)

theorem originalPurePrefix_add_chunk {P Q : ℕ} (hPQ : P ≤ Q) :
    originalPurePrefix P + (∑ p ∈ Finset.Ico (P+1) (Q+1), pureSourceRow p) =
      originalPurePrefix Q := by
  change (∑ p ∈ Finset.range (P+1), pureSourceRow p) + _ =
    ∑ p ∈ Finset.range (Q+1), pureSourceRow p
  simpa only [Finset.range_eq_Ico] using
    Finset.sum_Ico_consecutive pureSourceRow (Nat.zero_le (P+1)) (Nat.succ_le_succ hPQ)

theorem originalMixedPrefix_add_chunk {P Q : ℕ} (hPQ : P ≤ Q) :
    originalMixedPrefix P + (∑ p ∈ Finset.Ico (P+1) (Q+1), mixedSourceRow p) =
      originalMixedPrefix Q := by
  change (∑ p ∈ Finset.range (P+1), mixedSourceRow p) + _ =
    ∑ p ∈ Finset.range (Q+1), mixedSourceRow p
  simpa only [Finset.range_eq_Ico] using
    Finset.sum_Ico_consecutive mixedSourceRow (Nat.zero_le (P+1)) (Nat.succ_le_succ hPQ)

/-- The stored prefix and stored next chunk need not share a box evaluator. -/
theorem purePrefix_contains_add_chunk {P Q : ℕ} {prior chunk : Box} (hPQ : P ≤ Q)
    (hp : Contains prior (originalPurePrefix P))
    (hc : Contains chunk (∑ p ∈ Finset.Ico (P+1) (Q+1), pureSourceRow p)) :
    Contains (add prior chunk) (originalPurePrefix Q) := by
  rw [← originalPurePrefix_add_chunk hPQ]
  exact add_contains hp hc

theorem mixedPrefix_contains_add_chunk {P Q : ℕ} {prior chunk : Box} (hPQ : P ≤ Q)
    (hp : Contains prior (originalMixedPrefix P))
    (hc : Contains chunk (∑ p ∈ Finset.Ico (P+1) (Q+1), mixedSourceRow p)) :
    Contains (add prior chunk) (originalMixedPrefix Q) := by
  rw [← originalMixedPrefix_add_chunk hPQ]
  exact add_contains hp hc

/-- Widening to a stored integer box is an independently checked small step. -/
theorem contains_enlarge {a b : Box} {x : ℝ} (ha : Contains a x)
    (hlo : b.lo ≤ a.lo) (hhi : a.hi ≤ b.hi) : Contains b x := by
  have hlo' : (b.lo : ℝ) ≤ a.lo := by exact_mod_cast hlo
  have hhi' : (a.hi : ℝ) ≤ b.hi := by exact_mod_cast hhi
  exact ⟨hlo'.trans ha.1, ha.2.trans hhi'⟩

#print axioms purePrefix_contains_add_chunk
#print axioms mixedPrefix_contains_add_chunk

end SubmittedGenus.CapFourMass.Interval.IndexedModePrefix
