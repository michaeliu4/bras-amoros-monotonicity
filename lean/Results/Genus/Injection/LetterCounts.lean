import Results.Genus.Injection.CodeMap
import Mathlib.Data.List.Duplicate

namespace SubmittedGenus

lemma KunzData.twoLetters_iff_count (d : KunzData) (a : ℕ) :
    OriginalSources.twoLetters d a ↔ 2 ≤ d.toList.count a := by
  rw [← List.duplicate_iff_two_le_count, List.duplicate_iff_exists_distinct_get]
  constructor
  · rintro ⟨p, q, hpq, hp, hq⟩
    have hne : p.val ≠ q.val := fun h => hpq (Fin.ext h)
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · refine ⟨⟨p.val, by simpa using p.isLt⟩, ⟨q.val, by simpa using q.isLt⟩, hlt, ?_, ?_⟩
      · simpa [KunzData.toList] using hp.symm
      · simpa [KunzData.toList] using hq.symm
    · refine ⟨⟨q.val, by simpa using q.isLt⟩, ⟨p.val, by simpa using p.isLt⟩, hlt, ?_, ?_⟩
      · simpa [KunzData.toList] using hq.symm
      · simpa [KunzData.toList] using hp.symm
  · rintro ⟨p, q, hpq, hp, hq⟩
    let i : Fin (d.1.val - 1) := ⟨p.val, by have := p.isLt; simpa using this⟩
    let j : Fin (d.1.val - 1) := ⟨q.val, by have := q.isLt; simpa using this⟩
    refine ⟨i, j, ?_, ?_, ?_⟩
    · intro h
      have he := congrArg Fin.val h
      dsimp [i, j] at he
      exact (ne_of_lt hpq) (Fin.ext he)
    · simpa [KunzData.toList, i] using hp.symm
    · simpa [KunzData.toList, j] using hq.symm

/-- The code reservation prefix contains at least two physical fours. -/
lemma OriginalMaps.B_prefix_two_fours {d : KunzData} (hB : OriginalSources.sector d = .B) :
    2 ≤ d.prefixList.count 4 := by
  have h := (KunzData.twoLetters_iff_count d 4).mp (OriginalSources.B_two_fours hB)
  rw [OriginalMaps.B_toList_eq hB] at h
  simpa using h

end SubmittedGenus
