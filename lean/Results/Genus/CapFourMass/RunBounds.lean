import Results.Genus.CapFourMass.AlternatingRuns
import Results.Genus.CapFourMass.Normalization

/-! Exact D/E/carry exponent accounting for the original component envelope. -/
noncomputable section
open scoped BigOperators
namespace SubmittedGenus.CapFourMass

def StrongRun.strongCount : StrongRun → ℕ
  | .full k _ => k
  | .restricted => 1

def StrongRun.restrictedCount : StrongRun → ℕ
  | .full _ _ => 0
  | .restricted => 1

lemma StrongRun.bound_eq (s : StrongRun) :
    s.bound=strongBound^s.strongCount*sigma^s.restrictedCount := by
  cases s with
  | full k hk => simp [StrongRun.bound,StrongRun.strongCount,StrongRun.restrictedCount]
  | restricted => norm_num [StrongRun.bound,StrongRun.strongCount,StrongRun.restrictedCount,
      sigma,strongBound,restrictedBound]

lemma coupled_bounds_product (l : List CoupledRun) :
    (l.map (fun b => b.dominated.bound)).prod=
      strongBound^((l.map (fun b => b.strong.strongCount)).sum)*
      sigma^((l.map (fun b => b.strong.restrictedCount)).sum)*
      lam^((l.map CoupledRun.carryLength).sum) := by
  induction l with
  | nil => simp
  | cons b l ih =>
    rw [List.map_cons,List.prod_cons,ih]
    simp only [List.map_cons,List.sum_cons,CoupledRun.dominated_bound,StrongRun.bound_eq,pow_add]
    ring

/-- Replacing λ by the original L and enlarging only the total edge budget.
This is the exact scalar identity producing η^e_D σ^e_E. -/
lemma edge_budget_bound (D E C total : ℕ) (hcount : D+C≤total) :
    strongBound^D*sigma^E*lam^C ≤ lambdaBound^total*eta^D*sigma^E := by
  have hs : 0≤sigma^E := pow_nonneg sigma_bounds.1.le E
  have hR : 0≤strongBound^D := pow_nonneg strongBound_pos.le D
  have hL:=pow_le_pow_left₀ lam_pos.le lam_lt_bound.le C
  have he : strongBound^D*lambdaBound^C=lambdaBound^(D+C)*eta^D := by
    rw [eta,pow_add,div_pow]
    field_simp [ne_of_gt lambdaBound_pos]
  calc
    strongBound^D*sigma^E*lam^C ≤ strongBound^D*sigma^E*lambdaBound^C :=
      mul_le_mul_of_nonneg_left hL (mul_nonneg hR hs)
    _ = lambdaBound^(D+C)*eta^D*sigma^E := by rw [mul_assoc,mul_comm (sigma^E),← mul_assoc,he]
    _ ≤ lambdaBound^total*eta^D*sigma^E :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ lambdaBound_gt_one.le hcount) (pow_nonneg eta_bounds.1.le D)) hs

lemma coupled_bounds_le_budget (l : List CoupledRun) (total : ℕ)
    (hcount : (l.map (fun b => b.strong.strongCount)).sum+
      (l.map CoupledRun.carryLength).sum ≤ total) :
    (l.map (fun b => b.dominated.bound)).prod ≤
      lambdaBound^total*eta^((l.map (fun b => b.strong.strongCount)).sum)*
      sigma^((l.map (fun b => b.strong.restrictedCount)).sum) := by
  rw [coupled_bounds_product]
  exact edge_budget_bound _ _ _ _ hcount

end SubmittedGenus.CapFourMass
