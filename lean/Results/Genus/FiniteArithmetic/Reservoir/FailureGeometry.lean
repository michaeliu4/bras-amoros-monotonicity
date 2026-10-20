import Results.Genus.FiniteArithmetic.ReflectionConstraints
import Results.Genus.Injection.ReservoirSources.TailWitness
import Mathlib.Data.List.Forall2

namespace SubmittedGenus.FiniteArithmetic.Reservoir

open Reflection

/-- Each physical coordinate is paired with its reflected coordinate;
central coordinates are included, without a separate parity assumption. -/
theorem bounded_language_reverse {threshold cap : ℕ} {w : List ℕ}
    (h : Language (boundedSystem threshold cap).pairAllowed
      (boundedSystem threshold cap).centerAllowed w) :
    List.Forall₂ (fun a b => threshold ≤ a+b) w w.reverse := by
  induction h with
  | nil => exact .nil
  | singleton a ha =>
    simpa using List.Forall₂.cons (show threshold ≤ a+a from by have := ha.2.2; omega)
      List.Forall₂.nil
  | pair a b w hab hw ih =>
    have h1 : threshold ≤ a+b := hab.2.2.2.2
    have h2 : threshold ≤ b+a := by omega
    have hh : List.Forall₂ (fun a b => threshold ≤ a+b) (a :: (w ++ [b])) (b :: (w.reverse ++ [a])) :=
      List.Forall₂.cons h1 (List.rel_append ih (List.Forall₂.cons h2 .nil))
    simpa using hh

theorem bounded_language_pairs {threshold cap : ℕ} {w : List ℕ}
    (h : Language (boundedSystem threshold cap).pairAllowed
      (boundedSystem threshold cap).centerAllowed w)
    (i j : Fin w.length) (hij : i.val+j.val+1=w.length) :
    threshold ≤ w[i.val]+w[j.val] := by
  have hh := (bounded_language_reverse h).get i.isLt (by simpa using i.isLt)
  simp only [List.get_eq_getElem, List.getElem_reverse] at hh
  have he : w.length-1-i.val=j.val := by omega
  simpa only [he] using hh

abbrev failureSystem := boundedSystem 3 2

/-- Failing a distance-d witness is precisely a reflected initial block
with no (1,1) pair; the last d physical positions are unrestricted. -/
theorem no_tailWitness_iff_prefix_language (t : List ℕ) (d : ℕ)
    (ht : ∀ a ∈ t, a=1 ∨ a=2) (hd : d ≤ t.length) :
    ¬ OriginalReservoir.TailWitness t d ↔
      Language failureSystem.pairAllowed failureSystem.centerAllowed (t.take (t.length-d)) := by
  let n := t.length-d
  have hn : n ≤ t.length := Nat.sub_le _ _
  have hlen : (t.take n).length=n := by simp [List.length_take, Nat.min_eq_left hn]
  constructor
  · intro h
    have hlang := ofFn_bounded_language 3 2 n (fun i => t[i.val]'(by omega))
      (by intro i; have := ht t[i.val] (List.getElem_mem _); omega) (by
        intro i j hij
        have hi := ht t[i.val] (List.getElem_mem _)
        have hj := ht t[j.val] (List.getElem_mem _)
        by_contra hsum
        have hi1 : t[i.val]=1 := by omega
        have hj1 : t[j.val]=1 := by omega
        apply h
        refine ⟨⟨i.val,by omega⟩,⟨j.val,by omega⟩,hi1,hj1,?_⟩
        dsimp
        dsimp [n] at hij
        omega)
    have he : List.ofFn (fun i : Fin n => t[i.val]'(by omega)) = t.take n := by
      apply List.ext_getElem
      · simpa using hlen.symm
      · intro i hi hj
        simp only [List.getElem_ofFn, List.getElem_take]
    simpa only [he] using hlang
  · intro h hw
    rcases hw with ⟨i,j,hi,hj,hij⟩
    have hin : i.val < n := by dsimp [n]; omega
    have hjn : j.val < n := by dsimp [n]; omega
    have hp := bounded_language_pairs h ⟨i.val,by change i.val < (t.take n).length; rw [hlen]; exact hin⟩
      ⟨j.val,by change j.val < (t.take n).length; rw [hlen]; exact hjn⟩ (by
        change i.val+j.val+1=(t.take n).length
        rw [hlen]; dsimp [n]; omega)
    simp only [List.getElem_take, hi, hj] at hp
    omega

theorem no_tailWitness_of_short (t : List ℕ) (d : ℕ) (h : t.length < d) :
    ¬ OriginalReservoir.TailWitness t d := by
  rintro ⟨i,j,hi,hj,hij⟩
  omega

#print axioms no_tailWitness_iff_prefix_language
end SubmittedGenus.FiniteArithmetic.Reservoir
