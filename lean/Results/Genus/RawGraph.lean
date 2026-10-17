import Results.Genus.Kunz
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega

/-!
# The original submitted paper's raw two-pivot source

Source: submitted/manuscript.tex, blob e04fb276e8ceed829059cf724ead1e18e8bc9e9f,
lines 748--833. Physical coordinates are 1,...,m-1, represented by Fin (m-1).
The two fixed pivots are the two rightmost occurrences of the maximum. Both
noncarry and carry self-pairs are retained. Every physical coordinate has
exactly one weight. This file does not assert the omitted-pivot tail estimate.
-/

namespace SubmittedGenus.RawGraph

abbrev Word (m : ℕ) := Fin (m - 1) → ℕ

def physical {m : ℕ} (i : Fin (m - 1)) : ℕ := i.val + 1

def Parameters (m r p a : ℕ) : Prop :=
  1 ≤ r ∧ r < p ∧ p < m ∧ (a = 4 ∨ a = 5)

instance (m r p a : ℕ) : Decidable (Parameters m r p a) := by
  unfold Parameters
  infer_instance

def IsPivot {m : ℕ} (r p : ℕ) (i : Fin (m - 1)) : Prop :=
  physical i = r ∨ physical i = p

instance {m r p : ℕ} (i : Fin (m - 1)) : Decidable (IsPivot r p i) := by
  unfold IsPivot
  infer_instance

def IsFree {m : ℕ} (r p : ℕ) (i : Fin (m - 1)) : Prop :=
  ¬ IsPivot r p i

/-- The original two-rightmost-maxima alphabets, including fixed pivots. -/
def Alphabet {m : ℕ} (r p a : ℕ) (x : Word m) : Prop :=
  ∀ i, if IsPivot r p i then x i = a
       else 1 ≤ x i ∧ x i ≤ if physical i < r then a else a - 1

/-- Exactly the two noncarry targets; the quantifiers include self-pairs. -/
def Ordinary {m : ℕ} (r p a : ℕ) (x : Word m) : Prop :=
  ∀ i j, physical i + physical j = r ∨ physical i + physical j = p →
    a ≤ x i + x j

/-- Exactly the two carry targets; the quantifiers include self-pairs. -/
def Carried {m : ℕ} (r p a : ℕ) (x : Word m) : Prop :=
  ∀ i j, physical i + physical j = m + r ∨ physical i + physical j = m + p →
    a - 1 ≤ x i + x j

def RawAdmissible {m : ℕ} (r p a : ℕ) (x : Word m) : Prop :=
  Parameters m r p a ∧ Alphabet r p a x ∧ Ordinary r p a x ∧ Carried r p a x

/-- Genus counts each physical coordinate once, including loop vertices. -/
def genus {m : ℕ} (x : Word m) : ℕ := ∑ i, x i

/-- Removing the fixed pivots leaves binary edges and unary loop restrictions. -/
def GraphAdmissible {m : ℕ} (r p a : ℕ) (x : Word m) : Prop :=
  Parameters m r p a ∧ Alphabet r p a x ∧
  (∀ i j, IsFree r p i → IsFree r p j → i ≠ j →
    physical i + physical j = r ∨ physical i + physical j = p →
    a ≤ x i + x j) ∧
  (∀ i j, IsFree r p i → IsFree r p j → i ≠ j →
    physical i + physical j = m + r ∨ physical i + physical j = m + p →
    a - 1 ≤ x i + x j) ∧
  (∀ i, IsFree r p i →
    2 * physical i = r ∨ 2 * physical i = p → a ≤ 2 * x i) ∧
  (∀ i, IsFree r p i →
    2 * physical i = m + r ∨ 2 * physical i = m + p → a - 1 ≤ 2 * x i)

instance {m r p a : ℕ} (x : Word m) : Decidable (Alphabet r p a x) := by
  unfold Alphabet
  haveI : DecidablePred (fun i : Fin (m - 1) =>
      if IsPivot r p i then x i = a
      else 1 ≤ x i ∧ x i ≤ if physical i < r then a else a - 1) := by
    intro i
    dsimp only
    split_ifs <;> infer_instance
  infer_instance

instance {m r p a : ℕ} (x : Word m) : Decidable (RawAdmissible r p a x) := by
  unfold RawAdmissible Ordinary Carried
  infer_instance

theorem alphabet_pivot {m r p a : ℕ} {x : Word m}
    (h : Alphabet r p a x) {i : Fin (m - 1)} (hi : IsPivot r p i) : x i = a := by
  simpa [Alphabet, hi] using h i

theorem alphabet_positive {m r p a : ℕ} {x : Word m}
    (ha : 1 ≤ a) (h : Alphabet r p a x) (i : Fin (m - 1)) : 1 ≤ x i := by
  by_cases hi : IsPivot r p i
  · simpa [alphabet_pivot h hi] using ha
  · exact (by simpa [hi] using h i : 1 ≤ x i ∧
      x i ≤ if physical i < r then a else a - 1).1

/-- Pivot incidences are automatic; self-pairs become unary restrictions. -/
theorem raw_iff_graph {m r p a : ℕ} (x : Word m) :
    RawAdmissible r p a x ↔ GraphAdmissible r p a x := by
  constructor
  · rintro ⟨hp, ha, ho, hc⟩
    refine ⟨hp, ha, ?_, ?_, ?_, ?_⟩
    · intro i j _ _ _ ht
      exact ho i j ht
    · intro i j _ _ _ ht
      exact hc i j ht
    · intro i _ ht
      simpa [two_mul] using ho i i (by simpa [two_mul] using ht)
    · intro i _ ht
      simpa [two_mul] using hc i i (by simpa [two_mul] using ht)
  · rintro ⟨hp, ha, ho, hc, hlo, hlc⟩
    refine ⟨hp, ha, ?_, ?_⟩
    · intro i j ht
      by_cases hi : IsPivot r p i
      · rw [alphabet_pivot ha hi]
        omega
      by_cases hj : IsPivot r p j
      · rw [alphabet_pivot ha hj]
        omega
      by_cases hij : i = j
      · subst j
        simpa [two_mul] using hlo i hi (by simpa [two_mul] using ht)
      · exact ho i j hi hj hij ht
    · intro i j ht
      by_cases hi : IsPivot r p i
      · rw [alphabet_pivot ha hi]
        omega
      by_cases hj : IsPivot r p j
      · rw [alphabet_pivot ha hj]
        omega
      by_cases hij : i = j
      · subst j
        simpa [two_mul] using hlc i hi (by simpa [two_mul] using ht)
      · exact hc i j hi hj hij ht

instance {m r p a : ℕ} (x : Word m) : Decidable (GraphAdmissible r p a x) :=
  decidable_of_iff (RawAdmissible r p a x) (raw_iff_graph x)

/-- Reject invalid pivot/cap input before any graph is counted. -/
theorem invalid_parameters_rejected {m r p a : ℕ} (h : ¬ Parameters m r p a)
    (x : Word m) : ¬ RawAdmissible r p a x := fun hx => h hx.1

/-- Source inclusion from all genuine ordinary/carried inequalities and alphabets.
This is the interface used by the actual Kunz-coordinate bridge. -/
theorem raw_of_full_constraints {m r p a : ℕ} {x : Word m}
    (hp : Parameters m r p a) (ha : Alphabet r p a x)
    (ho : ∀ i j k : Fin (m - 1), physical i + physical j = physical k →
      x k ≤ x i + x j)
    (hc : ∀ i j k : Fin (m - 1), physical i + physical j = m + physical k →
      x k ≤ x i + x j + 1) : RawAdmissible r p a x := by
  have hparam := hp
  rcases hparam with ⟨h1, h2, h3, h4⟩
  have hr : r - 1 < m - 1 := by omega
  have hpp : p - 1 < m - 1 := by omega
  let ri : Fin (m - 1) := ⟨r - 1, hr⟩
  let pi : Fin (m - 1) := ⟨p - 1, hpp⟩
  have eri : physical ri = r := by dsimp [physical, ri]; omega
  have epi : physical pi = p := by dsimp [physical, pi]; omega
  have xr : x ri = a := alphabet_pivot ha (Or.inl eri)
  have xp : x pi = a := alphabet_pivot ha (Or.inr epi)
  refine ⟨hp, ha, ?_, ?_⟩
  · intro i j ht
    rcases ht with ht | ht
    · simpa [xr] using ho i j ri (ht.trans eri.symm)
    · simpa [xp] using ho i j pi (ht.trans epi.symm)
  · intro i j ht
    rcases ht with ht | ht
    · have h := hc i j ri (by simpa [eri] using ht)
      omega
    · have h := hc i j pi (by simpa [epi] using ht)
      omega

/-- Every genuine positive Kunz word with these two-rightmost-maxima alphabets
belongs to the exact raw relaxation. -/
theorem raw_of_kunz {m r p a : ℕ} {x : Word m}
    (hp : Parameters m r p a) (ha : Alphabet r p a x)
    (hx : KunzWord.Valid x) : RawAdmissible r p a x := by
  apply raw_of_full_constraints hp ha
  · intro i j k he
    have hi := i.isLt
    have hj := j.isLt
    have hk := k.isLt
    have hh := hx.noncarry (physical i) (physical j)
      (by dsimp [physical]; omega) (by dsimp [physical]; omega)
      (by dsimp [physical]; omega) (by dsimp [physical]; omega)
      (by dsimp [physical] at he ⊢; omega)
    rw [he] at hh
    simpa only [physical, KunzWord.coord_index] using hh
  · intro i j k he
    have hi := i.isLt
    have hj := j.isLt
    have hh := hx.carry (physical i) (physical j)
      (by dsimp [physical]; omega) (by dsimp [physical]; omega)
      (by dsimp [physical]; omega) (by dsimp [physical]; omega)
      (by dsimp [physical] at he ⊢; omega)
    rw [he, Nat.add_sub_cancel_left] at hh
    simpa only [physical, KunzWord.coord_index] using hh

/-- Source inclusion with no pivots supplied: the two rightmost maxima are
selected from the genuine word itself. Maxima before the left pivot are allowed. -/
theorem exists_raw_of_kunz_two_maxima {m a : ℕ} {x : Word m}
    (ha : a = 4 ∨ a = 5) (hx : KunzWord.Valid x)
    (hcap : ∀ i, x i ≤ a)
    (htwo : ∃ i j, i ≠ j ∧ x i = a ∧ x j = a) :
    ∃ r p, RawAdmissible r p a x := by
  classical
  let s : Finset (Fin (m - 1)) := Finset.univ.filter (fun i => x i = a)
  have hs : s.Nonempty := by
    obtain ⟨i, j, hij, hi, hj⟩ := htwo
    exact ⟨i, by simp [s, hi]⟩
  let pi := s.max' hs
  have hpi : pi ∈ s := s.max'_mem hs
  have hsr : (s.erase pi).Nonempty := by
    obtain ⟨i, j, hij, hi, hj⟩ := htwo
    by_cases hip : i = pi
    · refine ⟨j, Finset.mem_erase.mpr ⟨?_, ?_⟩⟩
      · intro hjp
        exact hij (hip.trans hjp.symm)
      · simp [s, hj]
    · exact ⟨i, by simp [s, hi, hip]⟩
  let ri := (s.erase pi).max' hsr
  have hri : ri ∈ s.erase pi := (s.erase pi).max'_mem hsr
  have hne : ri ≠ pi := (Finset.mem_erase.mp hri).1
  have hris : ri ∈ s := (Finset.mem_erase.mp hri).2
  have hrp : ri ≤ pi := s.le_max' ri hris
  have xr : x ri = a := (Finset.mem_filter.mp hris).2
  have xp : x pi = a := (Finset.mem_filter.mp hpi).2
  refine ⟨physical ri, physical pi, raw_of_kunz ?_ ?_ hx⟩
  · refine ⟨?_, ?_, ?_, ha⟩
    · simp [physical]
    · have hneval : ri.val ≠ pi.val := fun hh => hne (Fin.ext hh)
      change ri.val ≤ pi.val at hrp
      dsimp [physical]
      omega
    · have hh := pi.isLt
      dsimp [physical]
      omega
  · intro i
    by_cases hip : IsPivot (physical ri) (physical pi) i
    · simp only [hip, ↓reduceIte]
      rcases hip with hi | hi
      · have hei : i = ri := Fin.ext (by dsimp [physical] at hi; omega)
        simpa [hei] using xr
      · have hei : i = pi := Fin.ext (by dsimp [physical] at hi; omega)
        simpa [hei] using xp
    · simp only [hip, ↓reduceIte]
      refine ⟨hx.positive i, ?_⟩
      by_cases hil : physical i < physical ri
      · simpa [hil] using hcap i
      · simp only [hil, ↓reduceIte]
        have hnot : x i ≠ a := by
          intro hia
          have hine : i ≠ pi := by
            intro heq
            apply hip
            right
            exact congrArg physical heq
          have his : i ∈ s.erase pi := by simp [s, hine, hia]
          have hle : i ≤ ri := (s.erase pi).le_max' i his
          have hiner : i ≠ ri := by
            intro heq
            apply hip
            left
            exact congrArg physical heq
          have hneval : i.val ≠ ri.val := fun heq => hiner (Fin.ext heq)
          change i.val ≤ ri.val at hle
          dsimp [physical] at hil
          omega
        have hb := hcap i
        omega

/-- Every raw coordinate is positive and bounded by the specified cap. -/
theorem raw_coordinate_bounds {m r p a : ℕ} {x : Word m}
    (h : RawAdmissible r p a x) (i : Fin (m - 1)) : 1 ≤ x i ∧ x i ≤ a := by
  have hcap : 1 ≤ a := by rcases h.1.2.2.2 with rfl | rfl <;> decide
  refine ⟨alphabet_positive hcap h.2.1 i, ?_⟩
  by_cases hi : IsPivot r p i
  · exact (alphabet_pivot h.2.1 hi).le
  · have hb := h.2.1 i
    simp only [hi, ↓reduceIte] at hb
    split_ifs at hb <;> omega

/-- No maximum occurs after the right pivot. -/
theorem maximum_at_most_right_pivot {m r p a : ℕ} {x : Word m}
    (h : RawAdmissible r p a x) (i : Fin (m - 1)) (hi : x i = a) :
    physical i ≤ p := by
  have horder := h.1.2.1
  have hcap : 1 ≤ a := (raw_coordinate_bounds h i).1.trans_eq hi
  by_contra hn
  have hnpi : ¬ IsPivot r p i := by unfold IsPivot; omega
  have hnr : ¬ physical i < r := by omega
  have hb := h.2.1 i
  simp only [hnpi, hnr, ↓reduceIte] at hb
  omega

/-- Above the left pivot, the right pivot is the only maximum. -/
theorem maximum_after_left_is_right {m r p a : ℕ} {x : Word m}
    (h : RawAdmissible r p a x) (i : Fin (m - 1)) (hr : r < physical i)
    (hi : x i = a) : physical i = p := by
  have hcap : 1 ≤ a := (raw_coordinate_bounds h i).1.trans_eq hi
  by_contra hn
  have hnpi : ¬ IsPivot r p i := by unfold IsPivot; omega
  have hnr : ¬ physical i < r := by omega
  have hb := h.2.1 i
  simp only [hnpi, hnr, ↓reduceIte] at hb
  omega

/-- The pivot labels of a source word are unique, as required before summing
raw polynomials over both pivot positions. -/
theorem raw_parameters_unique {m r p r' p' a : ℕ} {x : Word m}
    (h : RawAdmissible r p a x) (h' : RawAdmissible r' p' a x) :
    r = r' ∧ p = p' := by
  have h1 := h.1.1
  have h2 := h.1.2.1
  have h3 := h.1.2.2.1
  have h1' := h'.1.1
  have h2' := h'.1.2.1
  have h3' := h'.1.2.2.1
  let ri : Fin (m - 1) := ⟨r - 1, by omega⟩
  let pi : Fin (m - 1) := ⟨p - 1, by omega⟩
  let ri' : Fin (m - 1) := ⟨r' - 1, by omega⟩
  let pi' : Fin (m - 1) := ⟨p' - 1, by omega⟩
  have eri : physical ri = r := by dsimp [physical, ri]; omega
  have epi : physical pi = p := by dsimp [physical, pi]; omega
  have eri' : physical ri' = r' := by dsimp [physical, ri']; omega
  have epi' : physical pi' = p' := by dsimp [physical, pi']; omega
  have xr : x ri = a := alphabet_pivot h.2.1 (Or.inl eri)
  have xp : x pi = a := alphabet_pivot h.2.1 (Or.inr epi)
  have xr' : x ri' = a := alphabet_pivot h'.2.1 (Or.inl eri')
  have xp' : x pi' = a := alphabet_pivot h'.2.1 (Or.inr epi')
  have hpp : p = p' := by
    have hp₁ := maximum_at_most_right_pivot h' pi xp
    have hp₂ := maximum_at_most_right_pivot h pi' xp'
    omega
  refine ⟨?_, hpp⟩
  by_contra hrr
  rcases lt_or_gt_of_ne hrr with hlt | hgt
  · have hc := maximum_after_left_is_right h ri' (by omega) xr'
    omega
  · have hc := maximum_after_left_is_right h' ri (by omega) xr
    omega

/-- The elementary support bound from positive coordinates and two pivots. -/
theorem genus_two_pivots_lower {m r p a : ℕ} {x : Word m}
    (h : RawAdmissible r p a x) : (m - 1) + 2 * (a - 1) ≤ genus x := by
  have h1 := h.1.1
  have h2 := h.1.2.1
  have h3 := h.1.2.2.1
  have hcap : 1 ≤ a := by rcases h.1.2.2.2 with rfl | rfl <;> decide
  let ri : Fin (m - 1) := ⟨r - 1, by omega⟩
  let pi : Fin (m - 1) := ⟨p - 1, by omega⟩
  have eri : physical ri = r := by dsimp [physical, ri]; omega
  have epi : physical pi = p := by dsimp [physical, pi]; omega
  have hne : ri ≠ pi := by intro heq; have := congrArg physical heq; omega
  have xr : x ri = a := alphabet_pivot h.2.1 (Or.inl eri)
  have xp : x pi = a := alphabet_pivot h.2.1 (Or.inr epi)
  have hb : ∀ i, 1 + (if i = ri then a - 1 else 0) +
      (if i = pi then a - 1 else 0) ≤ x i := by
    intro i
    by_cases hir : i = ri
    · subst i
      simp only [hne, if_false, if_true, xr, add_zero]
      omega
    by_cases hip : i = pi
    · subst i
      simp only [hir, if_false, if_true, xp, add_zero]
      omega
    · simpa [hir, hip] using (raw_coordinate_bounds h i).1
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hb i)
  simpa [genus, Finset.sum_add_distrib, two_mul, Nat.add_assoc] using hs

/-- The submitted cap-four multiplicity cutoff. -/
theorem cap_four_genus_multiplicity {m r p : ℕ} {x : Word m}
    (h : RawAdmissible r p 4 x) : m + 5 ≤ genus x := by
  have hs := genus_two_pivots_lower h
  have hp := h.1.2.2.1
  omega

/-! ## Reflection support, including its central fixed points -/

private def reflectedPhysical (m p n : ℕ) : ℕ :=
  if n < p then p - n else if n = p then p else m + p - n

private theorem reflectedPhysical_bounds {m p n : ℕ}
    (hp : 0 < p ∧ p < m) (hn : 0 < n ∧ n < m) :
    0 < reflectedPhysical m p n ∧ reflectedPhysical m p n < m := by
  unfold reflectedPhysical
  split_ifs <;> omega

private theorem reflectedPhysical_involutive {m p n : ℕ}
    (hp : 0 < p ∧ p < m) (hn : 0 < n ∧ n < m) :
    reflectedPhysical m p (reflectedPhysical m p n) = n := by
  unfold reflectedPhysical
  split_ifs <;> omega

private def reflectIndex {m p : ℕ} (hp : 0 < p ∧ p < m)
    (i : Fin (m - 1)) : Fin (m - 1) :=
  ⟨reflectedPhysical m p (physical i) - 1, by
    have hi := i.isLt
    have hb := reflectedPhysical_bounds hp (n := physical i) (by
      dsimp [physical]; omega)
    omega⟩

private theorem physical_reflectIndex {m p : ℕ} (hp : 0 < p ∧ p < m)
    (i : Fin (m - 1)) :
    physical (reflectIndex hp i) = reflectedPhysical m p (physical i) := by
  have hi := i.isLt
  have hb := reflectedPhysical_bounds hp (n := physical i) (by
    dsimp [physical]; omega)
  change reflectedPhysical m p (physical i) - 1 + 1 = reflectedPhysical m p (physical i)
  omega

private theorem reflectIndex_involutive {m p : ℕ} (hp : 0 < p ∧ p < m) :
    Function.Involutive (reflectIndex hp) := by
  intro i
  apply Fin.ext
  have hi := i.isLt
  have hb := reflectedPhysical_involutive hp (n := physical i) (by
    dsimp [physical]; omega)
  have he : physical (reflectIndex hp (reflectIndex hp i)) = physical i := by
    rw [physical_reflectIndex, physical_reflectIndex, hb]
  dsimp [physical] at he
  omega

/-- The exact finite support inequality in the original submitted manuscript.
The proof sums one reflection incidence per physical coordinate, so self-pairs
contribute twice that vertex value and never create a second vertex weight. -/
theorem genus_reflection_support {m r p a : ℕ} {x : Word m}
    (h : RawAdmissible r p a x) : (a - 1) * m + p + 1 ≤ 2 * genus x := by
  have h1 := h.1.1
  have h2 := h.1.2.1
  have h3 := h.1.2.2.1
  have hcap : 1 ≤ a := by rcases h.1.2.2.2 with rfl | rfl <;> decide
  have hp : 0 < p ∧ p < m := by omega
  let pi : Fin (m - 1) := ⟨p - 1, by omega⟩
  have epi : physical pi = p := by dsimp [physical, pi]; omega
  have heq : ∀ i : Fin (m - 1), physical i = p ↔ i = pi := by
    intro i
    constructor
    · intro he
      apply Fin.ext
      dsimp [physical, pi] at *
      omega
    · rintro rfl
      exact epi
  have hleft : (∑ i : Fin (m - 1), if physical i < p then 1 else 0) = p - 1 := by
    have he : ∀ i : Fin (m - 1), physical i < p ↔ i.val < p - 1 := by
      intro i
      dsimp [physical]
      omega
    simp_rw [he]
    rw [Finset.sum_boole, Fin.card_filter_val_lt]
    exact min_eq_right (by omega)
  have hpivot : (∑ i : Fin (m - 1), if physical i = p then a + 1 else 0) = a + 1 := by
    simp_rw [heq]
    simp
  have hreflection : (∑ i, x (reflectIndex hp i)) = genus x := by
    exact (reflectIndex_involutive hp).bijective.sum_comp x
  have hpoint : ∀ i : Fin (m - 1),
      (a - 1) + (if physical i < p then 1 else 0) +
        (if physical i = p then a + 1 else 0) ≤ x i + x (reflectIndex hp i) := by
    intro i
    have hir := physical_reflectIndex hp i
    by_cases hi : physical i < p
    · have hi' : physical i ≠ p := by omega
      have hr : physical i + physical (reflectIndex hp i) = p := by
        simp only [reflectedPhysical, hi, ↓reduceIte] at hir
        omega
      have ho := h.2.2.1 i (reflectIndex hp i) (Or.inr hr)
      simp only [hi, hi', ↓reduceIte]
      omega
    · by_cases hip : physical i = p
      · have hv : x i = a := alphabet_pivot h.2.1 (Or.inr hip)
        have hr : physical (reflectIndex hp i) = p := by
          simpa [reflectedPhysical, hip] using hir
        have hvr : x (reflectIndex hp i) = a := alphabet_pivot h.2.1 (Or.inr hr)
        simp only [hip, Nat.lt_irrefl, ↓reduceIte, hv, hvr]
        omega
      · have his := i.isLt
        have hr : physical i + physical (reflectIndex hp i) = m + p := by
          simp only [reflectedPhysical, hi, hip, ↓reduceIte] at hir
          dsimp [physical] at *
          omega
        have hc := h.2.2.2 i (reflectIndex hp i) (Or.inr hr)
        simpa [hi, hip] using hc
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hpoint i)
  have hw : (∑ i : Fin (m - 1), ((a - 1) + (if physical i < p then 1 else 0) +
      (if physical i = p then a + 1 else 0))) =
      (m - 1) * (a - 1) + (p - 1) + (a + 1) := by
    simp only [Finset.sum_add_distrib, hleft, hpivot, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [hw, Finset.sum_add_distrib, hreflection] at hsum
  change (m - 1) * (a - 1) + (p - 1) + (a + 1) ≤ genus x + genus x at hsum
  rcases h.1.2.2.2 with rfl | rfl <;> simp only [Nat.reduceSub] at * <;> omega

/-- The original cap-four pivot cutoff. -/
theorem cap_four_genus_pivot {m r p : ℕ} {x : Word m}
    (h : RawAdmissible r p 4 x) : 2 * p + 2 ≤ genus x := by
  have hs := genus_reflection_support h
  have hp := h.1.2.2.1
  omega

/-- The omitted-pivot sector is empty below genus604, without a leaf or one test. -/
theorem omitted_pivot_genus_at_least_604 {m r p : ℕ} {x : Word m}
    (h : RawAdmissible r p 4 x) (hp : 300 < p) : 604 ≤ genus x := by
  have hs := cap_four_genus_pivot h
  omega

/-- Finite bounded assignments. The filter also enforces the positive alphabets. -/
def boundedWord {m a : ℕ} (x : Fin (m - 1) → Fin (a + 1)) : Word m :=
  fun i => (x i).val

/-- Every source word has exactly one bounded encoding. This verifies that the
finite polynomial enumerator neither drops a raw word nor counts one twice. -/
def boundedSourceEquiv (m r p a : ℕ) :
    {x : Fin (m - 1) → Fin (a + 1) // RawAdmissible r p a (boundedWord x)} ≃
      {x : Word m // RawAdmissible r p a x} where
  toFun x := ⟨boundedWord x.val, x.property⟩
  invFun x := ⟨fun i => ⟨x.val i, Nat.lt_succ_of_le (raw_coordinate_bounds x.property i).2⟩,
    x.property⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    apply Fin.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl

/-- The raw polynomial, with one exponent contribution per physical coordinate. -/
noncomputable def rawPolynomial (m r p a : ℕ) : Polynomial ℕ :=
  ∑ x : Fin (m - 1) → Fin (a + 1),
    if RawAdmissible r p a (boundedWord x) then Polynomial.X ^ genus (boundedWord x)
    else 0

/-- The same finite partition function evaluated using pivot-removed graph tests. -/
noncomputable def graphPolynomial (m r p a : ℕ) : Polynomial ℕ :=
  ∑ x : Fin (m - 1) → Fin (a + 1),
    if GraphAdmissible r p a (boundedWord x) then Polynomial.X ^ genus (boundedWord x)
    else 0

theorem rawPolynomial_eq_graphPolynomial (m r p a : ℕ) :
    rawPolynomial m r p a = graphPolynomial m r p a := by
  unfold rawPolynomial graphPolynomial
  apply Finset.sum_congr rfl
  intro x _
  simp only [raw_iff_graph]

theorem rawPolynomial_invalid {m r p a : ℕ} (h : ¬ Parameters m r p a) :
    rawPolynomial m r p a = 0 := by
  unfold rawPolynomial
  apply Finset.sum_eq_zero
  intro x _
  simp [invalid_parameters_rejected h]

/-- Each coefficient is the exact cardinality of the original bounded source
at that genus; every summand is an ordinary natural-number count. -/
theorem rawPolynomial_coeff (m r p a g : ℕ) :
    (rawPolynomial m r p a).coeff g =
      (Finset.univ.filter (fun x : Fin (m - 1) → Fin (a + 1) =>
        RawAdmissible r p a (boundedWord x) ∧ genus (boundedWord x) = g)).card := by
  classical
  rw [rawPolynomial, Polynomial.finsetSum_coeff, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : RawAdmissible r p a (boundedWord x)
  · simp [hx, Polynomial.coeff_X_pow, eq_comm]
  · simp [hx]

/-- Exact coefficient rejection from the submitted support inequality. -/
theorem rawPolynomial_coeff_zero_of_support {m r p a g : ℕ}
    (hg : 2 * g < (a - 1) * m + p + 1) :
    (rawPolynomial m r p a).coeff g = 0 := by
  rw [rawPolynomial_coeff]
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨_, hx, he⟩ := Finset.mem_filter.mp hx
  have hs := genus_reflection_support hx
  omega

theorem omitted_pivot_coeff_zero {m r p g : ℕ} (hp : 300 < p) (hg : g < 604) :
    (rawPolynomial m r p 4).coeff g = 0 := by
  rw [rawPolynomial_coeff]
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨_, hx, he⟩ := Finset.mem_filter.mp hx
  have hs := omitted_pivot_genus_at_least_604 hx hp
  omega

/-! ## Complete source-correct loop-bearing fixture
For m=4,r=1,p=2,a=4 the only free vertex is coordinate3.
Its carry self-pair 3+3=4+2 requires 2*x3≥3, and its alphabet is {1,2,3}.
Consequently precisely [4,4,2] and [4,4,3] are retained, with weights z^10,z^11.
-/

theorem fixture_source_iff (x : Word 4) :
    RawAdmissible 1 2 4 x ↔ x 0 = 4 ∧ x 1 = 4 ∧ (x 2 = 2 ∨ x 2 = 3) := by
  simp [RawAdmissible, Parameters, Alphabet, Ordinary, Carried, IsPivot,
    physical, Fin.forall_fin_succ]
  omega

theorem fixture_graph_iff (x : Word 4) :
    GraphAdmissible 1 2 4 x ↔ x 0 = 4 ∧ x 1 = 4 ∧ (x 2 = 2 ∨ x 2 = 3) := by
  rw [← raw_iff_graph]
  exact fixture_source_iff x

theorem fixture_rejects_missing_loop : ¬ RawAdmissible (m := 4) 1 2 4 ![4, 4, 1] := by
  simp [fixture_source_iff]

theorem fixture_accepts_two : RawAdmissible (m := 4) 1 2 4 ![4, 4, 2] := by
  simp [fixture_source_iff]

theorem fixture_accepts_three : RawAdmissible (m := 4) 1 2 4 ![4, 4, 3] := by
  simp [fixture_source_iff]

theorem fixture_genus_two : genus (m := 4) ![4, 4, 2] = 10 := by decide

theorem fixture_genus_three : genus (m := 4) ![4, 4, 3] = 11 := by decide

private def fixtureTwo : Fin 3 → Fin 5 := ![4, 4, 2]
private def fixtureThree : Fin 3 → Fin 5 := ![4, 4, 3]

private theorem fixture_bounded_iff (x : Fin 3 → Fin 5) :
    RawAdmissible 1 2 4 (boundedWord (m := 4) (a := 4) x) ↔ x = fixtureTwo ∨ x = fixtureThree := by
  rw [fixture_source_iff]
  constructor
  · rintro ⟨h0, h1, h2 | h3⟩
    · left
      funext i
      fin_cases i <;> apply Fin.ext <;> assumption
    · right
      funext i
      fin_cases i <;> apply Fin.ext <;> assumption
  · rintro (rfl | rfl) <;> simp [boundedWord, fixtureTwo, fixtureThree]

/-- Complete equality with the original source polynomial, not an abstract
checker acceptance or a floating-point sample. -/
theorem fixture_rawPolynomial : rawPolynomial 4 1 2 4 =
    (Polynomial.X : Polynomial ℕ) ^ 10 + Polynomial.X ^ 11 := by
  classical
  unfold rawPolynomial
  rw [Finset.sum_eq_add_of_mem fixtureTwo fixtureThree (Finset.mem_univ _)
    (Finset.mem_univ _) (by decide)]
  · simp [fixture_bounded_iff, fixtureTwo, fixtureThree, genus, boundedWord,
      Fin.sum_univ_succ]
  · intro x _ hx
    simp [fixture_bounded_iff, hx.1, hx.2]

/-- This zero-edge component has a loop; its free vertex contributes once. -/
theorem fixture_graphPolynomial : graphPolynomial 4 1 2 4 =
    (Polynomial.X : Polynomial ℕ) ^ 8 * (Polynomial.X ^ 2 + Polynomial.X ^ 3) := by
  rw [← rawPolynomial_eq_graphPolynomial, fixture_rawPolynomial]
  ring

theorem fixture_equal_pivots_rejected : rawPolynomial 4 2 2 4 = 0 :=
  rawPolynomial_invalid (by decide)

theorem fixture_zero_pivot_rejected : rawPolynomial 4 0 2 4 = 0 :=
  rawPolynomial_invalid (by decide)

theorem fixture_wrong_cap_rejected : rawPolynomial 4 1 2 3 = 0 :=
  rawPolynomial_invalid (by decide)

end SubmittedGenus.RawGraph
