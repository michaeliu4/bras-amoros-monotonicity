import Results.Genus.RawGraph.RawComponents

/-! Exact source geometry used to group maximal strong/carry runs. -/
namespace SubmittedGenus.RawGraph.StrongRuns
open SourceModel Topology

/-- A retained ordinary strong edge, with no self-pair or pivot incidence. -/
def StrongStep {m : ℕ} (r p : ℕ) (i j : Fin (m - 1)) : Prop :=
  (rawGraph m r p).Adj i j ∧ (physical i + physical j = r ∨ physical i + physical j = p)

/-- A retained ordinary carry edge, separate from its unary self-pairs. -/
def CarryStep {m : ℕ} (r p : ℕ) (i j : Fin (m - 1)) : Prop :=
  (rawGraph m r p).Adj i j ∧ (physical i + physical j = m + r ∨ physical i + physical j = m + p)

instance {m r p : ℕ} (i j : Fin (m - 1)) : Decidable (StrongStep r p i j) := by
  unfold StrongStep; infer_instance
instance {m r p : ℕ} (i j : Fin (m - 1)) : Decidable (CarryStep r p i j) := by
  unfold CarryStep; infer_instance

lemma strongStep_symm {m r p : ℕ} {i j : Fin (m - 1)} (h : StrongStep r p i j) :
    StrongStep r p j i := ⟨h.1.symm, by simpa [Nat.add_comm] using h.2⟩
lemma carryStep_symm {m r p : ℕ} {i j : Fin (m - 1)} (h : CarryStep r p i j) :
    CarryStep r p j i := ⟨h.1.symm, by simpa [Nat.add_comm] using h.2⟩

lemma edge_strong_or_carry {m r p : ℕ} {i j : Fin (m - 1)}
    (h : (rawGraph m r p).Adj i j) : StrongStep r p i j ∨ CarryStep r p i j := by
  rcases h.2.2.2 with (hr | hr) | (hp | hp)
  · exact Or.inl ⟨h, Or.inl hr⟩
  · exact Or.inr ⟨h, Or.inl hr⟩
  · exact Or.inl ⟨h, Or.inr hp⟩
  · exact Or.inr ⟨h, Or.inr hp⟩

lemma strong_carry_disjoint {m r p a : ℕ} (hp : Parameters m r p a) (i j : Fin (m - 1)) :
    ¬ (StrongStep r p i j ∧ CarryStep r p i j) := by
  have h1 := hp.1; have h2 := hp.2.1; have h3 := hp.2.2.1
  rintro ⟨hs, hc⟩
  have hs' := hs.2; have hc' := hc.2
  omega

/-- Every carry incidence forces both endpoint alphabets into1,2,3 in cap4. -/
lemma carry_endpoint_gt_r {m r p a : ℕ} (hp : Parameters m r p a)
    {i j : Fin (m - 1)} (h : CarryStep r p i j) : r < physical i := by
  have hj : physical j < m := by have := j.isLt; unfold physical; omega
  have hrp := hp.2.1
  have hh := h.2
  omega

lemma strong_endpoint_lt_p {m r p a : ℕ} (hp : Parameters m r p a)
    {i j : Fin (m - 1)} (h : StrongStep r p i j) : physical i < p := by
  have hj : 0 < physical j := Nat.succ_pos _
  have hrp := hp.2.1
  have hh := h.2
  omega

/-- Any internal vertex of a strong run lies strictly left of r. -/
lemma internal_strong_lt_r {m r p : ℕ} {i j k : Fin (m - 1)}
    (hj : StrongStep r p i j) (hk : StrongStep r p i k) (hne : j ≠ k) : physical i < r := by
  have hj0 : 0 < physical j := Nat.succ_pos _
  have hk0 : 0 < physical k := Nat.succ_pos _
  by_contra h
  have hjp : physical i + physical j = p := by have := hj.2; omega
  have hkp : physical i + physical k = p := by have := hk.2; omega
  apply hne
  apply Fin.ext
  unfold physical at hjp hkp
  omega

/-- A strong edge with both endpoints right of r cannot be extended by another
strong edge at either endpoint; it is exactly a one-edge restricted run. -/
lemma high_strong_unique {m r p : ℕ} {i j k : Fin (m - 1)}
    (hi : r < physical i) (hj : StrongStep r p i j) (hk : StrongStep r p i k) : j = k := by
  by_contra hne
  have hh := internal_strong_lt_r hj hk hne
  omega

lemma restricted_strong_run {m r p : ℕ} {i j : Fin (m - 1)}
    (hi : r < physical i) (hj : r < physical j) (hs : StrongStep r p i j) :
    (∀ k, StrongStep r p i k → k = j) ∧ (∀ k, StrongStep r p j k → k = i) := by
  exact ⟨fun k hk => (high_strong_unique hi hs hk).symm,
    fun k hk => (high_strong_unique hj (strongStep_symm hs) hk).symm⟩

lemma loop_excludes_two_neighbors {m r p : ℕ} {i j k : Fin (m - 1)}
    (hl : StrongLoop r p i ∨ CarryLoop r p i)
    (hj : (rawGraph m r p).Adj i j) (hk : (rawGraph m r p).Adj i k) : j = k := by
  have hself : TargetPair r i i ∨ TargetPair p i i := by
    unfold StrongLoop CarryLoop at hl
    unfold TargetPair
    rcases hl with (h | h) | (h | h)
    · exact Or.inl (Or.inl (by omega))
    · exact Or.inr (Or.inl (by omega))
    · exact Or.inl (Or.inr (by omega))
    · exact Or.inr (Or.inr (by omega))
  rcases hself with hr | hp
  · have hjp := hj.2.2.2.resolve_left (fun h => hj.1 (target_partner_unique hr h))
    have hkp := hk.2.2.2.resolve_left (fun h => hk.1 (target_partner_unique hr h))
    exact target_partner_unique hjp hkp
  · have hjr := hj.2.2.2.resolve_right (fun h => hj.1 (target_partner_unique hp h))
    have hkr := hk.2.2.2.resolve_right (fun h => hk.1 (target_partner_unique hp h))
    exact target_partner_unique hjr hkr

/-- Internal strong-run vertices have exactly the full four-letter alphabet;
there is no hidden loop projection inside a D-power block. -/
lemma internal_strong_domain {m r p : ℕ} {i j k : Fin (m - 1)}
    (hj : StrongStep r p i j) (hk : StrongStep r p i k) (hne : j ≠ k) (v : ℕ) :
    Domain r p 4 i v ↔ 1 ≤ v ∧ v ≤ 4 := by
  have hi := internal_strong_lt_r hj hk hne
  have hf := hj.1.2.1
  have hl : ¬ (StrongLoop r p i ∨ CarryLoop r p i) :=
    fun h => hne (loop_excludes_two_neighbors h hj.1 hk.1)
  have hs : ¬ StrongLoop r p i := fun h => hl (Or.inl h)
  have hc : ¬ CarryLoop r p i := fun h => hl (Or.inr h)
  rw [domain_iff_unary]
  simp [Unary, show ¬ IsPivot r p i from hf, hf, upper, hi, hs, hc]

lemma carry_domain_upper {m r p : ℕ} (hp : Parameters m r p 4)
    {i j : Fin (m - 1)} (he : CarryStep r p i j) {v : ℕ} (hv : Domain r p 4 i v) :
    1 ≤ v ∧ v ≤ 3 := by
  have hi := carry_endpoint_gt_r hp he
  have hf := he.1.2.1
  rw [domain_iff_unary] at hv
  have hh := hv.2 hf
  have hu : upper r 4 i = 3 := by unfold upper; rw [if_neg (by omega)]
  exact ⟨hh.1, by simpa only [hu] using hh.2.1⟩

end SubmittedGenus.RawGraph.StrongRuns
