import Results.Genus.FiniteArithmetic.CapacitySeries
import Mathlib.Data.Nat.Fib.Basic

namespace SubmittedGenus.FiniteArithmetic

open scoped BigOperators

abbrev alphabet12 : WeightedAlphabet where
  size := 2
  weight a := a.val + 1
  positive a := by omega

abbrev BinaryWords (n : ℕ) := ExactWords alphabet12 n

noncomputable instance binaryWordsFintype (n : ℕ) : Fintype (BinaryWords n) :=
  exactWordsFintype alphabet12 n

theorem binaryWordCount_one : wordCount alphabet12 1 = 1 := by
  have h := wordCount_succ alphabet12 1 (by decide)
  rw [← Finset.sum_subtype (Finset.univ.filter (fun a : Fin 2 => a.val + 1 ≤ 1))
    (by simp) (fun a : Fin 2 => wordCount alphabet12 (1 - (a.val + 1)))] at h
  rw [Finset.sum_filter] at h
  simp only [Fin.sum_univ_succ] at h
  simpa using h

theorem binaryWordCount_add_two (n : ℕ) :
    wordCount alphabet12 (n + 2) = wordCount alphabet12 (n + 1) + wordCount alphabet12 n := by
  have h := wordCount_succ alphabet12 (n + 2) (by omega)
  rw [← Finset.sum_subtype (Finset.univ.filter (fun a : Fin 2 => a.val + 1 ≤ n + 2))
    (by simp) (fun a : Fin 2 => wordCount alphabet12 (n + 2 - (a.val + 1)))] at h
  rw [Finset.sum_filter] at h
  simp only [Fin.sum_univ_succ] at h
  simpa using h

/-- Binary compositions of weight n are counted by the standard Fibonacci
number F_(n+1), including the empty word at n=0. -/
theorem binaryWordCount_eq_fib (n : ℕ) : wordCount alphabet12 n = Nat.fib (n + 1) := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simpa using binaryWordCount_one
  | more n ih0 ih1 =>
    rw [binaryWordCount_add_two, ih0, ih1]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (Nat.fib_add_two (n := n + 1)).symm

theorem binaryWords_card (n : ℕ) : Fintype.card (BinaryWords n) = Nat.fib (n + 1) :=
  binaryWordCount_eq_fib n

#print axioms binaryWords_card

end SubmittedGenus.FiniteArithmetic
