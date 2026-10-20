import Mathlib.Data.List.Basic

namespace SubmittedGenus.OriginalReservoir

/-- Actual tail positions witnessing a prefix `3` at physical distance `d`
from the last prefix letter. Self-pairs are permitted. -/
def TailWitness (t : List ℕ) (d : ℕ) : Prop :=
  ∃ j k : Fin t.length, t[j.val] = 1 ∧ t[k.val] = 1 ∧
    (j.val + 1) + (k.val + 1) + d = t.length + 1

/-- Every actual occurrence of `3` in the prefix has a tail witness. -/
def FullyWitnessed (p t : List ℕ) : Prop :=
  ∀ i : Fin p.length, p[i.val] = 3 → TailWitness t (p.length - 1 - i.val)

end SubmittedGenus.OriginalReservoir
