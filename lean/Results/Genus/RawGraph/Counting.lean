import Results.Genus.RawGraph.RawComponents

namespace SubmittedGenus.RawGraph.Incidence

open SourceModel
open scoped BigOperators

/-- Split a symmetric ordered incidence relation into ordinary edges (two
orientations) and self-pairs (one unary incidence). -/
theorem symmetric_relation_card {V : Type*} [Fintype V] [LinearOrder V]
    (R : V → V → Prop) [DecidableRel R] (hR : Symmetric R) :
    (Finset.univ.filter (fun ij : V × V => R ij.1 ij.2)).card =
      2 * (Finset.univ.filter (fun ij : V × V => ij.1 < ij.2 ∧ R ij.1 ij.2)).card +
        (Finset.univ.filter (fun i : V => R i i)).card := by
  classical
  let hi := Finset.univ.filter (fun ij : V × V => ij.1 < ij.2 ∧ R ij.1 ij.2)
  let lo := Finset.univ.filter (fun ij : V × V => ij.2 < ij.1 ∧ R ij.1 ij.2)
  let diag := Finset.univ.filter (fun ij : V × V => ij.1 = ij.2 ∧ R ij.1 ij.2)
  have hl : lo.card = hi.card := by
    apply Finset.card_bij (fun ij _ => (ij.2, ij.1))
    · intro ij hij
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hij).2.1,
        hR (Finset.mem_filter.mp hij).2.2⟩
    · intro ij hij kl hkl he
      exact Prod.ext (congrArg Prod.snd he) (congrArg Prod.fst he)
    · intro ij hij
      refine ⟨(ij.2, ij.1), ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hij).2.1,
        hR (Finset.mem_filter.mp hij).2.2⟩
  have hd : diag.card = (Finset.univ.filter (fun i : V => R i i)).card := by
    apply Finset.card_bij (fun ij _ => ij.1)
    · intro ij hij
      obtain ⟨_, he, hr⟩ := Finset.mem_filter.mp hij
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [he] using hr⟩
    · intro ij hij kl hkl he
      have hij' := (Finset.mem_filter.mp hij).2.1
      have hkl' := (Finset.mem_filter.mp hkl).2.1
      exact Prod.ext he (hij'.symm.trans (he.trans hkl'))
    · intro i hi
      exact ⟨(i, i), Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl,
        (Finset.mem_filter.mp hi).2⟩, rfl⟩
  have hp : ∀ ij : V × V,
      (if R ij.1 ij.2 then 1 else 0 : ℕ) =
        (if ij.1 < ij.2 ∧ R ij.1 ij.2 then 1 else 0) +
        (if ij.2 < ij.1 ∧ R ij.1 ij.2 then 1 else 0) +
        (if ij.1 = ij.2 ∧ R ij.1 ij.2 then 1 else 0) := by
    intro ij
    by_cases hr : R ij.1 ij.2
    · rcases lt_trichotomy ij.1 ij.2 with h | h | h
      · simp [hr, h, not_lt_of_ge h.le, ne_of_lt h]
      · simp [h, hr]
      · simp [hr, h, not_lt_of_ge h.le, ne_of_gt h]
    · simp [hr]
  have hh := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun ij _ => hp ij)
  simp only [Finset.sum_add_distrib, Finset.sum_boole] at hh
  change _ = hi.card + lo.card + diag.card at hh
  rw [hl, hd] at hh
  simpa [hi, two_mul] using hh

/-- Retained strong ordered pairs; diagonal pairs are strong loops. -/
def StrongPair {m : ℕ} (r p : ℕ) (i j : Fin (m - 1)) : Prop :=
  ¬ IsPivot r p i ∧ ¬ IsPivot r p j ∧
    (physical i + physical j = r ∨ physical i + physical j = p)

instance {m r p : ℕ} (i j : Fin (m - 1)) : Decidable (StrongPair r p i j) := by
  unfold StrongPair IsPivot
  infer_instance

def strongEdges (m r p : ℕ) : Finset (Fin (m - 1) × Fin (m - 1)) :=
  Finset.univ.filter (fun ij => ij.1 < ij.2 ∧ StrongPair r p ij.1 ij.2)

def strongLoops (m r p : ℕ) : Finset (Fin (m - 1)) :=
  Finset.univ.filter (fun i => ¬ IsPivot r p i ∧ StrongLoop r p i)

theorem strong_ordered_count (m r p : ℕ) :
    (Finset.univ.filter (fun ij : Fin (m - 1) × Fin (m - 1) => StrongPair r p ij.1 ij.2)).card =
      2 * (strongEdges m r p).card + (strongLoops m r p).card := by
  have hs : Symmetric (StrongPair (m := m) r p) := by
    intro i j h
    exact ⟨h.2.1, h.1, by simpa [Nat.add_comm] using h.2.2⟩
  simpa [strongEdges, strongLoops, StrongPair, StrongLoop, two_mul] using
    symmetric_relation_card (StrongPair (m := m) r p) hs

def allStrongIncidences (m r p : ℕ) : Finset (Bool × Fin (m - 1)) :=
  Finset.univ.filter (fun bi => physical bi.2 < target r p bi.1)

def RetainedStrong {m : ℕ} (r p : ℕ) (b : Bool) (i : Fin (m - 1)) : Prop :=
  ∃ j : Fin (m - 1), ¬ IsPivot r p i ∧ ¬ IsPivot r p j ∧ physical i + physical j = target r p b

instance {m r p : ℕ} (b : Bool) (i : Fin (m - 1)) : Decidable (RetainedStrong r p b i) := by
  unfold RetainedStrong IsPivot
  infer_instance

def retainedStrongIncidences (m r p : ℕ) : Finset (Bool × Fin (m - 1)) :=
  Finset.univ.filter (fun bi => RetainedStrong r p bi.1 bi.2)

def deletedStrongIncidences (m r p : ℕ) : Finset (Bool × Fin (m - 1)) :=
  Finset.univ.filter (fun bi => bi.1 = true ∧
    (physical bi.2 = r ∨ physical bi.2 + r = p))

theorem physical_lt_sum {m t : ℕ} (ht : 0 < t ∧ t < m) :
    (∑ i : Fin (m - 1), if physical i < t then 1 else 0 : ℕ) = t - 1 := by
  have he : ∀ i : Fin (m - 1), physical i < t ↔ i.val < t - 1 := by
    intro i
    dsimp [physical]
    omega
  simp_rw [he]
  rw [Finset.sum_boole, Fin.card_filter_val_lt]
  exact min_eq_right (by omega)

theorem allStrongIncidences_card {m r p a : ℕ} (hp : Parameters m r p a) :
    (allStrongIncidences m r p).card = (r - 1) + (p - 1) := by
  have hr : 0 < r ∧ r < m := by have := hp.1; have := hp.2.1; have := hp.2.2.1; omega
  have hpp : 0 < p ∧ p < m := by have := hp.1; have := hp.2.1; have := hp.2.2.1; omega
  unfold allStrongIncidences
  rw [Finset.card_filter, Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [target, Bool.false_eq_true, if_false, if_true, physical_lt_sum hr,
    physical_lt_sum hpp]
  omega

theorem deletedStrongIncidences_card_le_two {m r p a : ℕ} (hp : Parameters m r p a) :
    (deletedStrongIncidences m r p).card ≤ 2 := by
  have h1 := hp.1
  have h2 := hp.2.1
  have h3 := hp.2.2.1
  let ri : Fin (m - 1) := ⟨r - 1, by omega⟩
  let di : Fin (m - 1) := ⟨p - r - 1, by omega⟩
  have hsub : deletedStrongIncidences m r p ⊆ {(true, ri), (true, di)} := by
    rintro ⟨b, i⟩ hi
    obtain ⟨_, hb, hr | hd⟩ := Finset.mem_filter.mp hi
    · have he : i = ri := Fin.ext (by dsimp [physical, ri] at *; omega)
      change b = true at hb
      simp [hb, he]
    · have he : i = di := Fin.ext (by dsimp [physical, di] at *; omega)
      change b = true at hb
      simp [hb, he]
  exact (Finset.card_le_card hsub).trans Finset.card_le_two

theorem allStrong_subset_retained_deleted {m r p a : ℕ} (hp : Parameters m r p a) :
    allStrongIncidences m r p ⊆ retainedStrongIncidences m r p ∪ deletedStrongIncidences m r p := by
  rintro ⟨b, i⟩ hi
  have h1 := hp.1
  have h2 := hp.2.1
  have h3 := hp.2.2.1
  have hii := i.isLt
  have hit := (Finset.mem_filter.mp hi).2
  apply Finset.mem_union.mpr
  cases b
  · change physical i < r at hit
    let j : Fin (m - 1) := ⟨r - physical i - 1, by dsimp [physical] at *; omega⟩
    have hj : physical i + physical j = r := by change (i.val + 1) + (r - (i.val + 1) - 1 + 1) = r; dsimp [physical] at hit; omega
    left
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, j,
      by change ¬ IsPivot r p i; unfold IsPivot; have hi0 : 0 < physical i := Nat.succ_pos _; have hj0 : 0 < physical j := Nat.succ_pos _; omega,
      by change ¬ IsPivot r p j; unfold IsPivot; have hi0 : 0 < physical i := Nat.succ_pos _; have hj0 : 0 < physical j := Nat.succ_pos _; omega, hj⟩
  · change physical i < p at hit
    by_cases hbad : physical i = r ∨ physical i + r = p
    · right
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, hbad⟩
    · let j : Fin (m - 1) := ⟨p - physical i - 1, by dsimp [physical] at *; omega⟩
      have hj : physical i + physical j = p := by change (i.val + 1) + (p - (i.val + 1) - 1 + 1) = p; dsimp [physical] at hit; omega
      left
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, j,
        by change ¬ IsPivot r p i; unfold IsPivot; have hi0 : 0 < physical i := Nat.succ_pos _; have hj0 : 0 < physical j := Nat.succ_pos _; omega,
        by change ¬ IsPivot r p j; unfold IsPivot; have hi0 : 0 < physical i := Nat.succ_pos _; have hj0 : 0 < physical j := Nat.succ_pos _; omega, hj⟩


theorem retainedStrong_card {m r p a : ℕ} (hp : Parameters m r p a) :
    (retainedStrongIncidences m r p).card =
      (Finset.univ.filter (fun ij : Fin (m - 1) × Fin (m - 1) =>
        StrongPair r p ij.1 ij.2)).card := by
  classical
  let f (bi : Bool × Fin (m - 1)) (h : bi ∈ retainedStrongIncidences m r p) :=
    (bi.2, Classical.choose ((Finset.mem_filter.mp h).2))
  have hf (bi : Bool × Fin (m - 1)) (h : bi ∈ retainedStrongIncidences m r p) :
      ¬ IsPivot r p bi.2 ∧ ¬ IsPivot r p (f bi h).2 ∧
        physical bi.2 + physical (f bi h).2 = target r p bi.1 :=
    Classical.choose_spec ((Finset.mem_filter.mp h).2)
  apply Finset.card_bij f
  · intro bi h
    have hh := hf bi h
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh.1, hh.2.1, ?_⟩
    change physical bi.2 + physical (f bi h).2 = r ∨ physical bi.2 + physical (f bi h).2 = p
    cases hb : bi.1 <;> simp only [target, hb, Bool.false_eq_true, if_false, if_true] at hh
    · exact Or.inl hh.2.2
    · exact Or.inr hh.2.2
  · intro bi hb cj hc he
    have hv : bi.2 = cj.2 := congrArg Prod.fst he
    have hw : (f bi hb).2 = (f cj hc).2 := congrArg Prod.snd he
    have ht : target r p bi.1 = target r p cj.1 := by
      rw [← (hf bi hb).2.2, ← (hf cj hc).2.2, hv, hw]
    have hbc : bi.1 = cj.1 := by
      have hrp := hp.2.1
      cases hbi : bi.1 <;> cases hcj : cj.1 <;> simp_all [target]
    exact Prod.ext hbc hv
  · rintro ⟨i, j⟩ h
    obtain ⟨_, hi, hj, hs⟩ := Finset.mem_filter.mp h
    dsimp only [Prod.fst, Prod.snd] at hi hj hs
    have hpre (b : Bool) (hb : physical i + physical j = target r p b) :
        ∃ bi, ∃ hbi : bi ∈ retainedStrongIncidences m r p, f bi hbi = (i, j) := by
      have hbi : (b, i) ∈ retainedStrongIncidences m r p :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, hi, hj, hb⟩
      refine ⟨(b, i), hbi, Prod.ext rfl ?_⟩
      have hh := (hf (b, i) hbi).2.2
      apply Fin.ext
      dsimp only [Prod.fst, Prod.snd] at hh ⊢
      dsimp [physical] at hh hb
      omega
    rcases hs with hs | hs
    · exact hpre false hs
    · exact hpre true hs

/-- The manuscript's strong-incidence lower bound, directly from the original
ordinary reflections; deletion removes at most two ordered incidences. -/
theorem strong_incidence_lower {m r p a : ℕ} (hp : Parameters m r p a) :
    r + p ≤ 2 * (strongEdges m r p).card + (strongLoops m r p).card + 4 := by
  have hh := Finset.card_le_card (allStrong_subset_retained_deleted hp)
  have hu := Finset.card_union_le (retainedStrongIncidences m r p)
    (deletedStrongIncidences m r p)
  have hd := deletedStrongIncidences_card_le_two hp
  rw [allStrongIncidences_card hp] at hh
  rw [retainedStrong_card hp, strong_ordered_count] at hu
  have hr := hp.1
  have hrp := hp.2.1
  omega

end SubmittedGenus.RawGraph.Incidence
