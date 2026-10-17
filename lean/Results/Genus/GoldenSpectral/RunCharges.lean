import Results.Genus.GoldenSpectral.Runs

/-! Exact original paid-run edge charges. Ordinary D edges cost R and restricted
E edges cost R³; each internal block additionally pays ν/R³. -/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.GoldenSpectral

def paidCost : ℝ := overlap/strongBound^3
lemma paidCost_pos : 0<paidCost := div_pos overlap_pos (pow_pos strongBound_pos _)
lemma paidCost_lt_one : paidCost<1 := paid_decay_comparisons.1.trans paid_decay_comparisons.2.1
lemma paidCost_lt_gap : paidCost<gapDecay^2 := paid_decay_comparisons.1

lemma strong_paid_charge (k : ℕ) :
    strongBound^(k-3)*overlap ≤ strongBound^k*paidCost := by
  unfold paidCost
  rw [←mul_div_assoc]
  apply (le_div_iff₀ (pow_pos strongBound_pos 3)).mpr
  calc
    strongBound^(k-3)*overlap*strongBound^3=strongBound^((k-3)+3)*overlap := by rw [pow_add]; ring
    _ ≤ strongBound^k*overlap := mul_le_mul_of_nonneg_right
      (pow_le_pow_of_le_one strongBound_pos.le strongBound_lt_one.le (by omega)) overlap_pos.le

lemma blockDominated_bound_le (b : CoupledRun) :
    (blockDominated b).bound ≤ strongBound^(runCharge b.strong)*paidCost := by
  cases b with
  | mk s n hn =>
    cases s with
    | full k hk => exact strong_paid_charge k
    | restricted =>
      change overlap ≤ strongBound^3*(overlap/strongBound^3)
      exact le_of_eq (by field_simp [ne_of_gt strongBound_pos])

lemma block_bounds_nonneg (l : List CoupledRun) :
    0 ≤ (l.map (fun b => (blockDominated b).bound)).prod := List.prod_nonneg (by
  intro x hx
  obtain ⟨b,hb,rfl⟩:=List.mem_map.mp hx
  exact (blockDominated b).bound_nonneg)

lemma blocks_paid_charge (l : List CoupledRun) :
    (l.map (fun b => (blockDominated b).bound)).prod ≤
      strongBound^((l.map (fun b => runCharge b.strong)).sum)*paidCost^l.length := by
  induction l with
  | nil => simp
  | cons b l ih =>
    simp only [List.map_cons,List.prod_cons,List.sum_cons,List.length_cons]
    have h:=mul_le_mul (blockDominated_bound_le b) ih (block_bounds_nonneg l)
      (mul_nonneg (pow_nonneg strongBound_pos.le _) paidCost_pos.le)
    exact h.trans_eq (by simp only [pow_add,pow_succ]; ring)

lemma blocks_charge_eq (l : List CoupledRun) :
    (l.map (fun b => runCharge b.strong)).sum=
      (l.map (fun b => b.strong.strongCount)).sum+2*(l.map (fun b => b.strong.restrictedCount)).sum := by
  induction l with
  | nil => simp
  | cons b l ih =>
    simp only [List.map_cons,List.sum_cons]
    rw [ih,runCharge_eq]
    omega

/-- All cycle strong runs are paid; the source conversion has no dimension factor. -/
theorem cycle_paid_bound (b : CoupledRun) (l : List CoupledRun) :
    (blockMatrix b*(l.map blockMatrix).prod).trace ≤
      strongBound^(((b::l).map (fun b => b.strong.strongCount)).sum+
        2*(((b::l).map (fun b => b.strong.restrictedCount)).sum))*paidCost^(l.length+1) := by
  have h:=(coupled_cycle_le b l).trans (blocks_paid_charge (b::l))
  simpa only [blocks_charge_eq,List.length_cons] using h

/-- A weaker paid exponent can safely discard genuine extra paid blocks. -/
lemma paid_exponent_weaken (n k : ℕ) (h : k ≤ n) : paidCost^n ≤ paidCost^k :=
  pow_le_pow_of_le_one paidCost_pos.le paidCost_lt_one.le h

end SubmittedGenus.GoldenSpectral
