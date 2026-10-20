import Results.Genus.RawGraph.PackedAcceptance.InvolutionPartition.Base

namespace SubmittedGenus.RawGraph.PackedAcceptance.InvolutionPartition
variable {g : ℕ}

/-- Explicit executable index of the canonical representative in filtered finRange. -/
def repIndex (s : Fin g → Fin g) (hs : Function.Involutive s) (x : Fin g) : Fin (count s) :=
  ⟨(reps s).idxOf (canonical s x),List.idxOf_lt_length_iff.mpr (canonical_mem s hs x)⟩

lemma representative_repIndex (s : Fin g → Fin g) (hs : Function.Involutive s) (x : Fin g) :
    representative s (repIndex s hs x) = canonical s x :=
  List.idxOf_get _

lemma canonical_representative (s : Fin g → Fin g) (c : Fin (count s)) :
    canonical s (representative s c) = representative s c :=
  min_eq_left (representative_le_mate s c)

lemma repIndex_representative (s : Fin g → Fin g) (hs : Function.Involutive s)
    (c : Fin (count s)) : repIndex s hs (representative s c) = c := by
  apply representative_injective s
  rw [representative_repIndex,canonical_representative]

lemma repIndex_mate (s : Fin g → Fin g) (hs : Function.Involutive s) (x : Fin g) :
    repIndex s hs (s x) = repIndex s hs x := by
  apply representative_injective s
  rw [representative_repIndex,representative_repIndex]
  exact canonical_mate s hs x

/-- Exact ownership criterion for both singleton and paired blocks. -/
theorem repIndex_eq_iff (s : Fin g → Fin g) (hs : Function.Involutive s)
    (x : Fin g) (c : Fin (count s)) :
    repIndex s hs x = c ↔ x = representative s c ∨ x = s (representative s c) := by
  constructor
  · intro h
    have he : canonical s x = representative s c := by rw [←representative_repIndex s hs x,h]
    rcases canonical_cases s x with h' | h'
    · exact Or.inl (h'.symm.trans he)
    · exact Or.inr (by rw [←he,h',hs x])
  · rintro (rfl | rfl)
    · exact repIndex_representative s hs c
    · rw [repIndex_mate,repIndex_representative]

lemma repIndex_surjective (s : Fin g → Fin g) (hs : Function.Involutive s) :
    Function.Surjective (repIndex s hs) :=
  fun c => ⟨representative s c,repIndex_representative s hs c⟩


#check repIndex_eq_iff
end SubmittedGenus.RawGraph.PackedAcceptance.InvolutionPartition
