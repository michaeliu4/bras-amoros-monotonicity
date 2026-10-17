import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

/-!
# Complete multiplicity sums from finite progression bases

The two positive parity bases and 2d mixed bases use this same exact source
partition of the natural numbers. A recurrence bound is propagated and summed;
no value of a divergent series is used.
-/
noncomputable section
open scoped BigOperators
namespace SubmittedGenus.CapFourMass

lemma progression_term_le (f : ℕ → ℝ) (q : ℕ) {c : ℝ} (hc : 0 ≤ c)
    (hstep : ∀ n, f (n+q) ≤ c*f n) (k s : ℕ) :
    f (k*q+s) ≤ c^k*f s := by
  induction k with
  | zero => simp
  | succ k ih =>
    have he : (k+1)*q+s=(k*q+s)+q := by ring
    rw [he,pow_succ]
    exact (hstep _).trans ((mul_le_mul_of_nonneg_left ih hc).trans_eq (by ring))

lemma progression_term_eq (f : ℕ → ℝ) (q : ℕ) {c : ℝ}
    (hstep : ∀ n, f (n+q)=c*f n) (k s : ℕ) :
    f (k*q+s)=c^k*f s := by
  induction k with
  | zero => simp
  | succ k ih =>
    have he : (k+1)*q+s=(k*q+s)+q := by ring
    rw [he,hstep,ih,pow_succ]
    ring

lemma progression_majorant_hasSum (q : ℕ) {c : ℝ} (hc : 0 ≤ c) (hc1 : c < 1)
    (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) :
    HasSum (fun x : ℕ×Fin q => c^x.1*f x.2.val)
      ((∑ s : Fin q, f s.val)/(1-c)) := by
  have hg := hasSum_geometric_of_lt_one hc hc1
  have hb := hasSum_fintype (fun s : Fin q => f s.val)
  have h := hg.mul hb (hg.summable.mul_of_nonneg hb.summable
    (fun _ => pow_nonneg hc _) (fun _ => hf _))
  have he : (1-c)⁻¹*(∑ s : Fin q, f s.val) = (∑ s : Fin q, f s.val)/(1-c) := by
    simp only [div_eq_mul_inv,mul_comm]
  rw [he] at h
  exact h

/-- Complete normalized mixed progression, with precisely q bases. -/
theorem complete_progression_le (q : ℕ) [NeZero q] {c : ℝ} (hc : 0 ≤ c) (hc1 : c < 1)
    (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (hstep : ∀ n, f (n+q) ≤ c*f n) :
    Summable f ∧ (∑' n, f n) ≤ (∑ s : Fin q, f s.val)/(1-c) := by
  let e := (Nat.divModEquiv q).symm
  have hg := progression_majorant_hasSum q hc hc1 f hf
  have hpoint (x : ℕ×Fin q) : f (e x) ≤ c^x.1*f x.2.val :=
    progression_term_le f q hc hstep x.1 x.2.val
  have hs : Summable (fun x => f (e x)) := hg.summable.of_nonneg_of_le
    (fun _ => hf _) hpoint
  have hle := hs.tsum_le_tsum hpoint hg.summable
  rw [e.tsum_eq,hg.tsum_eq] at hle
  exact ⟨e.summable_iff.mp hs,hle⟩

/-- Complete positive-mode progression is an equality, not a loss of the
negative-mode cancellation or an assumed bound by the raw partition. -/
theorem complete_progression_hasSum (q : ℕ) [NeZero q] {c : ℝ} (hc : 0 ≤ c) (hc1 : c < 1)
    (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (hstep : ∀ n, f (n+q)=c*f n) :
    HasSum f ((∑ s : Fin q, f s.val)/(1-c)) := by
  let e := (Nat.divModEquiv q).symm
  have hg := progression_majorant_hasSum q hc hc1 f hf
  have he : (fun x : ℕ×Fin q => f (e x)) = fun x => c^x.1*f x.2.val :=
    funext (fun x => progression_term_eq f q hstep x.1 x.2.val)
  rw [← he] at hg
  exact e.hasSum_iff.mp hg

end SubmittedGenus.CapFourMass
