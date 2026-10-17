import Results.Genus.FiniteArithmetic.Reservoir.PrefixSeries
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace SubmittedGenus.FiniteArithmetic.Reservoir

open PowerSeries
open scoped BigOperators

/-- Actual binary tails of an exact physical length and exact weight. -/
abbrev BinaryLengthSource (length : ℕ) := Graded.Atoms
  (fun f : Fin length → Fin 2 => ∑ i, ((f i).val + 1))

noncomputable instance binaryLengthFintype (length g : ℕ) :
    Fintype (BinaryLengthSource length g) := Fintype.ofFinite _

def binaryLengthWord {length g : ℕ} (a : BinaryLengthSource length g) : List ℕ :=
  List.ofFn (fun i => (a.val i).val + 1)

@[simp] theorem binaryLengthWord_length {length g : ℕ} (a : BinaryLengthSource length g) :
    (binaryLengthWord a).length = length := List.length_ofFn

theorem binaryLengthWord_weight {length g : ℕ} (a : BinaryLengthSource length g) :
    (binaryLengthWord a).sum = g := by
  simpa only [binaryLengthWord, List.sum_ofFn] using a.property

theorem binaryLengthWord_binary {length g : ℕ} (a : BinaryLengthSource length g) :
    ∀ x ∈ binaryLengthWord a, x = 1 ∨ x = 2 := by
  intro x hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  have h := (a.val i).isLt
  omega

theorem binaryLengthWord_injective (length g : ℕ) :
    Function.Injective (@binaryLengthWord length g) := by
  intro a b h
  apply Subtype.ext
  funext i
  apply Fin.ext
  have he := congrFun (List.ofFn_inj.mp h) i
  omega

theorem exists_binaryLengthSource (w : List ℕ) (hw : ∀ a ∈ w, a = 1 ∨ a = 2) :
    ∃ a : BinaryLengthSource w.length w.sum, binaryLengthWord a = w := by
  let f : Fin w.length → Fin 2 := fun i => ⟨w[i.val] - 1, by
    have ha := hw w[i.val] (List.getElem_mem _)
    omega⟩
  have hf : ∀ i : Fin w.length, (f i).val + 1 = w[i.val] := by
    intro i
    have ha := hw w[i.val] (List.getElem_mem _)
    dsimp [f]
    omega
  have he : List.ofFn (fun i : Fin w.length => (f i).val + 1) = w := by
    simp_rw [hf]
    exact List.ofFn_getElem
  refine ⟨⟨f, ?_⟩, he⟩
  change (∑ i, ((f i).val + 1)) = w.sum
  rw [← List.sum_ofFn, he]

noncomputable def binaryLengthSeries (length : ℕ) : PowerSeries ℤ :=
  Graded.series (BinaryLengthSource length)

/-- The exact-length tail source has the original polynomial c^length. -/
theorem binaryLengthSeries_identity (length : ℕ) : binaryLengthSeries length = c^length := by
  unfold binaryLengthSeries
  change Graded.atomSeries (fun f : Fin length → Fin 2 => ∑ i, ((f i).val + 1)) = _
  rw [Graded.atomSeries_eq_sum]
  have hc : c = ∑ a : Fin 2, (X : PowerSeries ℤ)^(a.val + 1) := by
    simp only [Fin.sum_univ_succ]
    norm_num [c]
  rw [hc, Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro f _
  exact (Finset.prod_pow_eq_pow_sum Finset.univ (fun i => (f i).val + 1) X).symm

#print axioms binaryLengthSeries_identity
#print axioms exists_binaryLengthSource

end SubmittedGenus.FiniteArithmetic.Reservoir
