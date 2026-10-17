import Results.Genus.Injection.RawFourSources

namespace SubmittedGenus
namespace KunzData

def prefixTwoList (d : KunzData) : List ℕ :=
  List.ofFn (fun i : Fin (d.1.val - 3) => d.2.val ⟨i.val, by omega⟩)

lemma toList_eq_prefixTwo (d : KunzData) (hm : 3 ≤ d.1.val) :
    d.toList = d.prefixTwoList ++
      [KunzWord.coord d.2.val (d.1.val - 2), KunzWord.coord d.2.val (d.1.val - 1)] := by
  rcases d with ⟨⟨m, hmpos⟩, ⟨x, hx⟩⟩
  change 3 ≤ m at hm
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hm
  have hk' : m = k + 3 := by omega
  clear hk
  subst m
  change (Fin (k + 2) → ℕ) at x
  change List.ofFn x =
    (List.ofFn fun i : Fin k => x i.castSucc.castSucc) ++
      [KunzWord.coord (m := k + 3) x (k + 1), KunzWord.coord (m := k + 3) x (k + 2)]
  have hp : KunzWord.coord (m := k + 3) x (k + 1) = x (Fin.last k).castSucc :=
    KunzWord.coord_index (m := k + 3) x (Fin.last k).castSucc
  have hl : KunzWord.coord (m := k + 3) x (k + 2) = x (Fin.last (k + 1)) :=
    KunzWord.coord_index (m := k + 3) x (Fin.last (k + 1))
  rw [hp, hl, List.ofFn_succ' x, List.ofFn_succ' (fun i : Fin (k + 1) => x i.castSucc)]
  simp only [List.concat_eq_append, List.append_assoc, List.singleton_append]

end KunzData
namespace OriginalPopulations
open OriginalSources

lemma genuineFour_multiplicity_ge_three (d : GenuineFour) : 3 ≤ d.val.1.val := by
  obtain ⟨i, j, hij, hi, hj⟩ := d.property.2
  have hi := i.isLt
  have hj := j.isLt
  by_contra hm
  have he : i.val = j.val := by omega
  exact hij (Fin.ext he)

/-- The sole-final-one exclusion has precisely a {2,3,4} prefix, at
least two fours, and one of the two suffixes (2,1) and (3,1). -/
lemma genuineFour_final_one_shape (d : GenuineFour) (hf : soleOneFinal d.val) :
    ∃ a : ℕ, (a = 2 ∨ a = 3) ∧ d.val.toList = d.val.prefixTwoList ++ [a, 1] ∧
      (∀ b ∈ d.val.prefixTwoList, 2 ≤ b ∧ b ≤ 4) ∧ 2 ≤ d.val.prefixTwoList.count 4 := by
  have hm := genuineFour_multiplicity_ge_three d
  obtain ⟨r, p, hr⟩ := RawGraph.exists_raw_of_kunz_two_maxima (Or.inl rfl)
    d.val.2.property d.property.1 d.property.2
  have hpen := RawGraph.raw_four_sole_final_penultimate hr hf
  let a := KunzWord.coord d.val.2.val (d.val.1.val - 2)
  have ha0 := d.val.2.property.coord_pos (by omega : 0 < d.val.1.val - 2)
    (by omega : d.val.1.val - 2 < d.val.1.val)
  have hane : a ≠ 1 := by
    let i : Fin (d.val.1.val - 1) := ⟨d.val.1.val - 3, by omega⟩
    have hi : i.val + 1 = d.val.1.val - 2 := by dsimp [i]; omega
    change KunzWord.coord d.val.2.val (d.val.1.val - 2) ≠ 1
    rw [← hi, KunzWord.coord_index]
    exact hf.2 i (by omega)
  have ha : a = 2 ∨ a = 3 := by dsimp [a] at *; omega
  have hw : d.val.toList = d.val.prefixTwoList ++ [a, 1] := by
    rw [KunzData.toList_eq_prefixTwo _ hm, hf.1]
  refine ⟨a, ha, hw, ?_, ?_⟩
  · intro b hb
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
    let j : Fin (d.val.1.val - 1) := ⟨i.val, by omega⟩
    have hp := d.val.2.property.positive j
    have hu := d.property.1 j
    have hn := hf.2 j (by dsimp [j]; omega)
    change 2 ≤ d.val.2.val j ∧ d.val.2.val j ≤ 4
    omega
  · have hc := (KunzData.twoLetters_iff_count d.val 4).mp d.property.2
    rw [hw] at hc
    rcases ha with ha | ha <;> simpa [ha] using hc

end OriginalPopulations
end SubmittedGenus
