import Results.Genus.RawGraph.Transfer
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-!
# The submitted cap-three carry transfer

This is the rational-weight matrix M of the submitted manuscript, implemented
as its action on three endpoint values. Its entries assign the full weight to
the arriving vertex. The equal second and third rows give the rank-two
recurrence. The free and loop terminal vectors satisfy it starting at length
zero; thus the isolated free-to-loop case is included exactly.
-/

namespace SubmittedGenus.FixedPivot

open scoped BigOperators

section Ring
variable {R : Type*} [CommRing R]

/-- The original sum and product of the two nonzero carry eigenvalues. -/
def carryB (z : R) : R := z^2+z^3

def carryC (z : R) : R := -z^3-z^4

/-- Original cap-three alphabet, physically labelled 1,2,3. -/
def carryWeight (z : R) (i : Fin 3) : R := z^(i.val+1)

def carryCompatibility (i j : Fin 3) : R :=
  if 3 ≤ (i.val+1)+(j.val+1) then 1 else 0

/-- Exact rational-weight carry matrix action Mv. -/
def carryStep (z : R) (v : Fin 3 → R) : Fin 3 → R :=
  ![z^2*v 1+z^3*v 2, z*v 0+z^2*v 1+z^3*v 2, z*v 0+z^2*v 1+z^3*v 2]

def carryPower (z : R) : ℕ → (Fin 3 → R) → (Fin 3 → R)
  | 0, v => v
  | n+1, v => carryStep z (carryPower z n v)

/-- Every summand has precisely the compatibility and arriving-vertex weight. -/
lemma carryStep_eq_sum (z : R) (v : Fin 3 → R) (i : Fin 3) :
    carryStep z v i = ∑ j : Fin 3, carryCompatibility i j * carryWeight z j * v j := by
  fin_cases i <;> simp [carryStep, carryCompatibility, carryWeight, Fin.sum_univ_succ] <;> ring

lemma carryStep_rows (z : R) (v : Fin 3 → R) : carryStep z v 2 = carryStep z v 1 := rfl

/-- Rank-two recurrence on the actual nonzero invariant subspace. -/
lemma carryStep_second_order (z : R) (v : Fin 3 → R) (hv : v 2 = v 1) :
    carryStep z (carryStep z v) = fun i => carryB z * carryStep z v i - carryC z*v i := by
  funext i
  fin_cases i <;> simp [carryStep, carryB, carryC, hv] <;> ring

/-- For arbitrary endpoint vectors, the null mode disappears after one edge. -/
lemma carryStep_third_order (z : R) (v : Fin 3 → R) :
    carryStep z (carryStep z (carryStep z v)) =
      fun i => carryB z * carryStep z (carryStep z v) i - carryC z*carryStep z v i :=
  carryStep_second_order z (carryStep z v) (carryStep_rows z v)

lemma carryPower_rows (z : R) (n : ℕ) (v : Fin 3 → R) :
    carryPower z (n+1) v 2 = carryPower z (n+1) v 1 := rfl

lemma carryPower_rows_of (z : R) (n : ℕ) (v : Fin 3 → R) (hv : v 2 = v 1) :
    carryPower z n v 2 = carryPower z n v 1 := by
  cases n with
  | zero => exact hv
  | succ n => rfl

/-- Structural carry recurrence for every length, including zero. -/
theorem carryPower_recurrence (z : R) (n : ℕ) (v : Fin 3 → R) (hv : v 2 = v 1) :
    carryPower z (n+2) v =
      fun i => carryB z * carryPower z (n+1) v i - carryC z*carryPower z n v i :=
  carryStep_second_order z (carryPower z n v) (carryPower_rows_of z n v hv)

/-- Arbitrary port-to-port kernels have the same recurrence from one edge onward. -/
theorem carryPower_positive_recurrence (z : R) (n : ℕ) (v : Fin 3 → R) :
    carryPower z (n+3) v =
      fun i => carryB z * carryPower z (n+2) v i - carryC z*carryPower z (n+1) v i :=
  carryStep_second_order z (carryPower z (n+1) v) (carryPower_rows z n v)

/-- No unary restriction at a free endpoint. -/
def freeTerminal : Fin 3 → R := ![1,1,1]

/-- Both kinds of carry loops impose exactly the same unary restriction. -/
def loopTerminal : Fin 3 → R := ![0,1,1]

lemma freeTerminal_loop_free (i : Fin 3) : (freeTerminal : Fin 3 → R) i = 1 := by
  fin_cases i <;> rfl

lemma loopTerminal_eq_gate (i : Fin 3) :
    (loopTerminal : Fin 3 → R) i = if 3 ≤ 2*(i.val+1) then 1 else 0 := by
  fin_cases i <;> rfl

/-- The actual raw-source transfer equals powers of the paper's matrix M. -/
theorem raw_run_eq_carryPower (z : R) (n : ℕ) (finish : Fin 3 → R) (first : Fin 3) :
    RawGraph.Transfer.run n (fun _ => carryWeight z)
      (fun _ => carryCompatibility) finish first =
      carryWeight z first * carryPower z n finish first := by
  induction n generalizing first with
  | zero => rfl
  | succ n ih =>
    change carryWeight z first *
      (∑ next, carryCompatibility first next * RawGraph.Transfer.run n
        (fun _ => carryWeight z) (fun _ => carryCompatibility) finish next) = _
    simp_rw [ih]
    rw [carryPower, carryStep_eq_sum]
    simp only [mul_assoc]

/-- Direct physical-vertex path source with a terminal restriction. -/
def carryPathSource (z : R) (n : ℕ) (finish : Fin 3 → R) : R :=
  ∑ x : Fin (n+1) → Fin 3,
    RawGraph.Transfer.sourceTerm n (fun _ => carryWeight z)
      (fun _ => carryCompatibility) finish x

/-- Exact finite source equality; it covers unary loop restrictions and length0. -/
theorem carryPathSource_eq (z : R) (n : ℕ) (finish : Fin 3 → R) :
    carryPathSource z n finish = ∑ first, carryWeight z first * carryPower z n finish first := by
  unfold carryPathSource
  rw [RawGraph.Transfer.sum_cons]
  apply Finset.sum_congr rfl
  intro first _
  rw [← raw_run_eq_carryPower, RawGraph.Transfer.run_eq_fixedSource]
  rfl

/-- The terminal-boundary source has an exact second-order recurrence from n=0. -/
theorem carryPathSource_recurrence (z : R) (n : ℕ) (finish : Fin 3 → R)
    (hf : finish 2 = finish 1) :
    carryPathSource z (n+2) finish =
      carryB z * carryPathSource z (n+1) finish - carryC z*carryPathSource z n finish := by
  simp_rw [carryPathSource_eq, carryPower_recurrence z n finish hf]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The original isolated free-to-loop component is a single vertex of value2 or3. -/
theorem free_to_loop_zero (z : R) : carryPathSource z 0 loopTerminal = z^2+z^3 := by
  simp [carryPathSource_eq, carryPower, carryWeight, loopTerminal, Fin.sum_univ_succ]

/-- No extra null-mode transient appears when the pivot-deleted component has no edge. -/
theorem free_to_loop_recurrence (z : R) (n : ℕ) :
    carryPathSource z (n+2) loopTerminal =
      carryB z * carryPathSource z (n+1) loopTerminal -
        carryC z*carryPathSource z n loopTerminal :=
  carryPathSource_recurrence z n loopTerminal rfl

end Ring
end SubmittedGenus.FixedPivot
