import Results.Genus.Injection.LetterCounts
import Results.Genus.RawGraph

/-! The two exact cap-four exclusions in the submitted raw envelope.
All self-pairs are retained, including the final-one obstruction. -/
namespace SubmittedGenus
namespace KunzWord

lemma coord_ge_of_bound {m a : ℕ} {x : KunzWord m} (hb : ∀ i, a ≤ x i)
    {n : ℕ} (hn : 0 < n) (hnm : n < m) : a ≤ coord x n := by
  simp only [coord, dif_pos (show 0 < n ∧ n < m from ⟨hn, hnm⟩)]
  exact hb _

/-- Every word on {2,3,4} is genuinely Kunz-valid. -/
theorem valid_of_two_to_four {m : ℕ} {x : KunzWord m}
    (hb : ∀ i, 2 ≤ x i ∧ x i ≤ 4) : Valid x where
  positive i := by have := (hb i).1; omega
  noncarry i j hi him hj hjm hij := by
    have ht := coord_le_of_bound (fun k => (hb k).2) (i + j)
    have h1 := coord_ge_of_bound (fun k => (hb k).1) hi him
    have h2 := coord_ge_of_bound (fun k => (hb k).1) hj hjm
    omega
  carry i j hi him hj hjm hij := by
    have ht := coord_le_of_bound (fun k => (hb k).2) (i + j - m)
    have h1 := coord_ge_of_bound (fun k => (hb k).1) hi him
    have h2 := coord_ge_of_bound (fun k => (hb k).1) hj hjm
    omega

/-- One occurs only at the final physical coordinate. -/
def SoleFinalOne {m : ℕ} (x : KunzWord m) : Prop :=
  coord x (m - 1) = 1 ∧ ∀ i, i.val + 1 ≠ m - 1 → x i ≠ 1

/-- All full Kunz inequalities for a sole-final-one cap-four word reduce
to the final self-pair, targeting the penultimate position. -/
theorem valid_of_sole_final_one {m : ℕ} {x : KunzWord m}
    (hb : ∀ i, 1 ≤ x i ∧ x i ≤ 4) (hone : SoleFinalOne x)
    (hpen : coord x (m - 2) ≤ 3) : Valid x := by
  have hcoord (n : ℕ) (hn : 0 < n) (hnm : n < m) (hne : n ≠ m - 1) :
      2 ≤ coord x n := by
    let i : Fin (m - 1) := ⟨n - 1, by omega⟩
    have hi : i.val + 1 = n := by dsimp [i]; omega
    have hp := (hb i).1
    have hn1 := hone.2 i (by omega)
    rw [← hi, coord_index]
    omega
  refine ⟨fun i => by have := (hb i).1; omega, ?_, ?_⟩
  · intro i j hi him hj hjm hij
    have ht := coord_le_of_bound (fun k => (hb k).2) (i + j)
    have h1 := hcoord i hi him (by omega)
    have h2 := hcoord j hj hjm (by omega)
    omega
  · intro i j hi him hj hjm hij
    by_cases hi1 : i = m - 1
    · by_cases hj1 : j = m - 1
      · have he : i + j - m = m - 2 := by omega
        rw [he, hi1, hj1, hone.1]
        exact hpen
      · have h2 := hcoord j hj hjm hj1
        have ht := coord_le_of_bound (fun k => (hb k).2) (i + j - m)
        rw [hi1] at ht
        rw [hi1, hone.1]
        omega
    · have h1 := hcoord i hi him hi1
      by_cases hj1 : j = m - 1
      · have ht := coord_le_of_bound (fun k => (hb k).2) (i + j - m)
        rw [hj1] at ht
        rw [hj1, hone.1]
        omega
      · have h2 := hcoord j hj hjm hj1
        have ht := coord_le_of_bound (fun k => (hb k).2) (i + j - m)
        omega

end KunzWord
namespace RawGraph

lemma raw_has_two_maxima {m r p a : ℕ} {x : Word m} (h : RawAdmissible r p a x) :
    ∃ i j, i ≠ j ∧ x i = a ∧ x j = a := by
  have hr := h.1.1
  have hrp := h.1.2.1
  have hpm := h.1.2.2.1
  let i : Fin (m - 1) := ⟨r - 1, by omega⟩
  let j : Fin (m - 1) := ⟨p - 1, by omega⟩
  have hi : physical i = r := by dsimp [physical, i]; omega
  have hj : physical j = p := by dsimp [physical, j]; omega
  refine ⟨i, j, ?_, alphabet_pivot h.2.1 (Or.inl hi), alphabet_pivot h.2.1 (Or.inr hj)⟩
  intro he
  have hh := congrArg physical he
  omega

/-- The raw cap-four no-one population is exactly the {2,3,4} source
with at least two fours. In particular every excluded word is genuine. -/
theorem raw_four_no_one_iff {m : ℕ} (x : Word m) :
    ((∃ r p, RawAdmissible r p 4 x) ∧ ∀ i, x i ≠ 1) ↔
      (∀ i, 2 ≤ x i ∧ x i ≤ 4) ∧ (∃ i j, i ≠ j ∧ x i = 4 ∧ x j = 4) := by
  constructor
  · rintro ⟨⟨r, p, h⟩, hn⟩
    refine ⟨?_, raw_has_two_maxima h⟩
    intro i
    have := raw_coordinate_bounds h i
    have := hn i
    omega
  · rintro ⟨hb, ht⟩
    refine ⟨exists_raw_of_kunz_two_maxima (Or.inl rfl) (KunzWord.valid_of_two_to_four hb)
      (fun i => (hb i).2) ht, ?_⟩
    intro i
    have := (hb i).1
    omega

/-- A raw sole-final-one word retains the penultimate self-pair obstruction. -/
theorem raw_four_sole_final_penultimate {m r p : ℕ} {x : Word m}
    (h : RawAdmissible r p 4 x) (hone : KunzWord.SoleFinalOne x) :
    KunzWord.coord x (m - 2) ≤ 3 := by
  have hr := h.1.1
  have hrp := h.1.2.1
  have hpm := h.1.2.2.1
  have hm : 3 ≤ m := by omega
  let last : Fin (m - 1) := ⟨m - 2, by omega⟩
  let pen : Fin (m - 1) := ⟨m - 3, by omega⟩
  have hlast : physical last = m - 1 := by dsimp [physical, last]; omega
  have hpen : physical pen = m - 2 := by dsimp [physical, pen]; omega
  have hxlast : x last = 1 := by
    have hh := hone.1
    rw [← hlast, physical, KunzWord.coord_index] at hh
    exact hh
  have hxp : p ≠ m - 1 := by
    intro hp
    have he : x last = 4 := alphabet_pivot h.2.1 (Or.inr (hlast.trans hp.symm))
    omega
  have hb := (raw_coordinate_bounds h pen).2
  have hn : x pen ≠ 4 := by
    intro he
    have hle := maximum_at_most_right_pivot h pen he
    have hp : p = m - 2 := by omega
    have hc := h.2.2.2 last last (Or.inr (by omega : physical last + physical last = m + p))
    rw [hxlast] at hc
    omega
  rw [← hpen, physical, KunzWord.coord_index]
  omega

/-- Raw and genuine cap-four populations coincide on the sole-final-one exclusion. -/
theorem raw_four_sole_final_valid {m r p : ℕ} {x : Word m}
    (h : RawAdmissible r p 4 x) (hone : KunzWord.SoleFinalOne x) : KunzWord.Valid x :=
  KunzWord.valid_of_sole_final_one (raw_coordinate_bounds h) hone
    (raw_four_sole_final_penultimate h hone)

end RawGraph
end SubmittedGenus
