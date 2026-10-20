import Results.Genus.Injection.RawFourSources

namespace SubmittedGenus.KunzWord

lemma coord_ofList_value (w : List ℕ) {i : ℕ} (hi : 0 < i) (him : i ≤ w.length) :
    coord (ofList w) i = w[i - 1]'(by omega) := by
  simp only [coord, dif_pos (show 0 < i ∧ i < w.length + 1 from ⟨hi, by omega⟩), ofList]

lemma coord_two_suffix_last (v : List ℕ) (a : ℕ) :
    coord (ofList (v ++ [a, 1])) ((v ++ [a, 1]).length + 1 - 1) = 1 := by
  simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_sub_cancel]
  rw [coord_ofList_value _ (by omega) (by simp)]
  simp

lemma coord_two_suffix_pen (v : List ℕ) (a : ℕ) :
    coord (ofList (v ++ [a, 1])) ((v ++ [a, 1]).length + 1 - 2) = a := by
  simp only [List.length_append, List.length_cons, List.length_nil]
  have he : v.length + (1 + (1 + 0)) + 1 - 2 = v.length + 1 := by omega
  rw [he, coord_ofList_value _ (by omega) (by simp)]
  simp

lemma soleFinalOne_two_suffix (v : List ℕ) (a : ℕ) (ha : 2 ≤ a)
    (hv : ∀ b ∈ v, 2 ≤ b) : SoleFinalOne (ofList (v ++ [a, 1])) := by
  refine ⟨coord_two_suffix_last v a, ?_⟩
  intro i hi
  have hib := i.isLt
  simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_sub_cancel] at hi hib
  change (v ++ [a, 1])[i.val] ≠ 1
  by_cases hil : i.val < v.length
  · rw [List.getElem_append_left hil]
    have := hv _ (List.getElem_mem hil)
    omega
  · have he : i.val = v.length := by omega
    simp [he]
    omega

lemma valid_two_suffix (v : List ℕ) (a : ℕ) (ha : a = 2 ∨ a = 3)
    (hv : ∀ b ∈ v, 2 ≤ b ∧ b ≤ 4) : Valid (ofList (v ++ [a, 1])) := by
  apply valid_of_sole_final_one
  · intro i
    have hi := List.getElem_mem (l := v ++ [a, 1]) (n := i.val) (by simpa using i.isLt)
    rcases List.mem_append.mp hi with h | h
    · have hb := hv _ h
      change 1 ≤ (v ++ [a, 1])[i.val] ∧ (v ++ [a, 1])[i.val] ≤ 4
      omega
    · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at h
      change 1 ≤ (v ++ [a, 1])[i.val] ∧ (v ++ [a, 1])[i.val] ≤ 4
      omega
  · exact soleFinalOne_two_suffix v a (by omega) (fun b hb => (hv b hb).1)
  · rw [coord_two_suffix_pen]
    omega

end SubmittedGenus.KunzWord
namespace SubmittedGenus.OriginalPopulations
open OriginalSources FiniteArithmetic

noncomputable def finalOneData {g : ℕ} (w : NWords g) (a : ℕ) (ha : a = 2 ∨ a = 3) : KunzData :=
  ⟨⟨(nWord w ++ [a, 1]).length + 1, by omega⟩,
    ⟨KunzWord.ofList (nWord w ++ [a, 1]), KunzWord.valid_two_suffix _ _ ha (nWord_bounds w)⟩⟩

@[simp] lemma finalOneData_toList {g : ℕ} (w : NWords g) (a : ℕ) (ha : a = 2 ∨ a = 3) :
    (finalOneData w a ha).toList = nWord w ++ [a, 1] := KunzWord.ofFn_ofList _

lemma finalOneData_weight {g : ℕ} (w : NWords g) (a : ℕ) (ha : a = 2 ∨ a = 3) :
    (finalOneData w a ha).weight = g + a + 1 := by
  rw [← KunzData.sum_toList, finalOneData_toList, List.sum_append, nWord_sum]
  simp [Nat.add_assoc]

lemma finalOneData_multipleFour {g : ℕ} (w : NWords g) (a : ℕ) (ha : a = 2 ∨ a = 3) :
    HasMultipleFour (finalOneData w a ha) := by
  constructor
  · intro i
    have hi := List.getElem_mem (l := nWord w ++ [a, 1]) (n := i.val) (by
      change i.val < (nWord w ++ [a, 1]).length
      have := i.isLt
      simpa only [finalOneData, Nat.add_sub_cancel] using this)
    change (nWord w ++ [a, 1])[i.val] ≤ 4
    rcases List.mem_append.mp hi with h | h
    · exact (nWord_bounds w _ h).2
    · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at h
      omega
  · apply (KunzData.twoLetters_iff_count _ _).mpr
    rw [finalOneData_toList]
    have := nWord_count_four w
    rcases ha with rfl | rfl <;> simpa using this

lemma finalOneData_finalOne {g : ℕ} (w : NWords g) (a : ℕ) (ha : a = 2 ∨ a = 3) :
    soleOneFinal (finalOneData w a ha) :=
  KunzWord.soleFinalOne_two_suffix _ _ (by omega) (fun b hb => (nWord_bounds w b hb).1)

end SubmittedGenus.OriginalPopulations
