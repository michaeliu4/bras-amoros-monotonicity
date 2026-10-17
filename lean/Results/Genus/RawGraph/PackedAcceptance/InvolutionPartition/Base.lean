import Mathlib.Data.List.FinRange
import Mathlib.Data.List.NodupEquivFin

/-! Executable canonical singleton/two-element blocks of a finite involution.
The list is the increasing finRange filtered by a≤s(a); indices use idxOf.
No chosen representatives or unverified component enumeration are used. -/
namespace SubmittedGenus.RawGraph.PackedAcceptance.InvolutionPartition

variable {g : ℕ}

def reps (s : Fin g → Fin g) : List (Fin g) :=
  (List.finRange g).filter (fun a => decide (a ≤ s a))

def count (s : Fin g → Fin g) : ℕ := (reps s).length

def representative (s : Fin g → Fin g) (c : Fin (count s)) : Fin g :=
  (reps s).get c

lemma mem_reps (s : Fin g → Fin g) (a : Fin g) :
    a ∈ reps s ↔ a ≤ s a := by simp [reps]

lemma reps_nodup (s : Fin g → Fin g) : (reps s).Nodup :=
  (List.nodup_finRange g).filter _

lemma representative_le_mate (s : Fin g → Fin g) (c : Fin (count s)) :
    representative s c ≤ s (representative s c) :=
  (mem_reps s _).mp (List.get_mem _ _)

lemma representative_injective (s : Fin g → Fin g) : Function.Injective (representative s) :=
  (List.nodup_iff_injective_get.mp (reps_nodup s))

def canonical (s : Fin g → Fin g) (x : Fin g) : Fin g := min x (s x)

lemma canonical_cases (s : Fin g → Fin g) (x : Fin g) :
    canonical s x = x ∨ canonical s x = s x := by
  by_cases h : x ≤ s x
  · exact Or.inl (min_eq_left h)
  · exact Or.inr (min_eq_right (le_of_not_ge h))

lemma canonical_mate (s : Fin g → Fin g) (hs : Function.Involutive s) (x : Fin g) :
    canonical s (s x) = canonical s x := by simp only [canonical,hs x,min_comm]

lemma canonical_mem (s : Fin g → Fin g) (hs : Function.Involutive s) (x : Fin g) :
    canonical s x ∈ reps s := by
  rw [mem_reps]
  by_cases h : x ≤ s x
  · simpa only [canonical,min_eq_left h] using h
  · have h' := le_of_not_ge h
    simpa only [canonical,min_eq_right h',hs x] using h'


#check canonical_mem
end SubmittedGenus.RawGraph.PackedAcceptance.InvolutionPartition
