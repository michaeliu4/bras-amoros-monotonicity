import Results.Genus.RawGraph.SourceModel

/-!
# Original reflection-incidence counting

The two target labels are kept distinct. A self-pair is one incidence at its
vertex, whereas an ordinary edge has two incidences. Missing incidences after
pivot deletion can occur only at the partner of the other deleted pivot.
-/

namespace SubmittedGenus.RawGraph.Incidence

open SourceModel

def target (r p : ℕ) (b : Bool) : ℕ := if b then p else r

/-- A target incidence is free exactly when its reflection partner was deleted. -/
def Missing {m : ℕ} (r p : ℕ) (b : Bool) (i : Fin (m - 1)) : Prop :=
  ¬ IsPivot r p i ∧ ∀ j, ¬ IsPivot r p j → ¬ TargetPair (target r p b) i j

instance {m r p : ℕ} (b : Bool) (i : Fin (m - 1)) : Decidable (Missing r p b i) := by
  unfold Missing IsPivot TargetPair
  infer_instance

def missingIncidences (m r p : ℕ) : Finset (Bool × Fin (m - 1)) :=
  Finset.univ.filter (fun bi => Missing r p bi.1 bi.2)

theorem reflection_partner_exists {m t : ℕ} (ht : 0 < t ∧ t < m)
    (i : Fin (m - 1)) (hi : physical i ≠ t) :
    ∃ j : Fin (m - 1), TargetPair t i j := by
  have him := i.isLt
  by_cases hil : physical i < t
  · let j : Fin (m - 1) := ⟨t - physical i - 1, by dsimp [physical] at *; omega⟩
    refine ⟨j, Or.inl ?_⟩
    dsimp [physical, j]
    dsimp [physical] at hil
    omega
  · let j : Fin (m - 1) := ⟨m + t - physical i - 1, by dsimp [physical] at *; omega⟩
    refine ⟨j, Or.inr ?_⟩
    dsimp [physical, j]
    dsimp [physical] at hi hil
    omega

/-- The target-r missing incidence can only reflect to the deleted pivot p. -/
theorem missing_left_location {m r p a : ℕ} (hp : Parameters m r p a)
    (i : Fin (m - 1)) (hi : Missing r p false i) :
    physical i + p = m + r := by
  have h1 := hp.1
  have h2 := hp.2.1
  have h3 := hp.2.2.1
  have hn : physical i ≠ r := fun h => hi.1 (Or.inl h)
  obtain ⟨j, hj⟩ := reflection_partner_exists (by omega : 0 < r ∧ r < m) i hn
  have hjpivot : IsPivot r p j := by
    by_contra hnot
    exact hi.2 j hnot (by simpa [target] using hj)
  have him := i.isLt
  dsimp [TargetPair, IsPivot, physical] at *
  omega

/-- The target-p missing incidence can only reflect to the deleted pivot r.
When p=2r the removed incidence is a loop on the deleted pivot itself. -/
theorem missing_right_location {m r p a : ℕ} (hp : Parameters m r p a)
    (i : Fin (m - 1)) (hi : Missing r p true i) :
    physical i + r = p := by
  have h1 := hp.1
  have h2 := hp.2.1
  have h3 := hp.2.2.1
  have hn : physical i ≠ p := fun h => hi.1 (Or.inr h)
  obtain ⟨j, hj⟩ := reflection_partner_exists (by omega : 0 < p ∧ p < m) i hn
  have hjpivot : IsPivot r p j := by
    by_contra hnot
    exact hi.2 j hnot (by simpa [target] using hj)
  have him := i.isLt
  dsimp [TargetPair, IsPivot, physical] at *
  omega

/-- There is at most one missing incidence for each target label. -/
theorem missing_unique {m r p a : ℕ} (hp : Parameters m r p a)
    (b : Bool) {i j : Fin (m - 1)} (hi : Missing r p b i) (hj : Missing r p b j) : i = j := by
  apply Fin.ext
  cases b
  · have hli := missing_left_location hp i hi
    have hlj := missing_left_location hp j hj
    dsimp [physical] at *
    omega
  · have hri := missing_right_location hp i hi
    have hrj := missing_right_location hp j hj
    dsimp [physical] at *
    omega

/-- The original bound u≤2, including exceptional pivot-to-pivot self-pairs. -/
theorem missingIncidences_card_le_two {m r p a : ℕ} (hp : Parameters m r p a) :
    (missingIncidences m r p).card ≤ 2 := by
  classical
  have hi : Set.InjOn Prod.fst (missingIncidences m r p : Set (Bool × Fin (m - 1))) := by
    intro bi hbi bj hbj he
    have hbi' := (Finset.mem_filter.mp hbi).2
    have hbj' := (Finset.mem_filter.mp hbj).2
    apply Prod.ext he
    exact missing_unique hp bi.1 hbi' (by simpa [he] using hbj')
  have hh := Finset.card_le_card_of_injOn Prod.fst (s := missingIncidences m r p)
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _) hi
  simpa using hh

end SubmittedGenus.RawGraph.Incidence
