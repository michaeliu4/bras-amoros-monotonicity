import Results.Genus.FixedPivot.KernelModes
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Exact finite mode assignment expansion and its structural annihilator. -/
namespace SubmittedGenus.FixedPivot
open scoped BigOperators
section Ring
variable {R C : Type*} [CommRing R] [Fintype C] [DecidableEq C]

def mixedModeDegree (arity : C→ℕ) (choice : C→Bool) : ℕ :=
  ∑ c,if choice c then arity c else 0

def pureModeDegree (arity : C→ℕ) (choice : C→Bool) : ℕ :=
  ∑ c,if choice c then 0 else arity c

lemma modeDegrees_sum (arity : C→ℕ) (choice : C→Bool) :
    pureModeDegree arity choice+mixedModeDegree arity choice=∑ c,arity c := by
  unfold pureModeDegree mixedModeDegree
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c _
  cases choice c <;> simp

lemma modeRate_eq (lam mu : R) (arity : C→ℕ) (choice : C→Bool) :
    (∏ c,if choice c then mu^(arity c) else lam^(arity c))=
      lam^(pureModeDegree arity choice)*mu^(mixedModeDegree arity choice) := by
  classical
  calc
    _ = ∏ c,lam^(if choice c then 0 else arity c)*mu^(if choice c then arity c else 0) := by
      apply Finset.prod_congr rfl
      intro c _
      cases choice c <;> simp
    _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,Finset.prod_pow_eq_pow_sum]; rfl

/-- Expanding the actual two-term component kernels uses all finite mode assignments;
no positivity, generic roots, or asymptotic truncation is assumed. -/
theorem finiteMode_expansion (lam mu : R) (arity : C→ℕ) (A B : C→R) (k : ℕ) :
    (∏ c,(A c*(lam^(arity c))^k+B c*(mu^(arity c))^k))=
      ∑ choice : C→Bool,
        (∏ c,if choice c then B c else A c)*
        (lam^(pureModeDegree arity choice)*mu^(mixedModeDegree arity choice))^k := by
  classical
  have hh:=Fintype.prod_sum (fun c (b : Bool) =>
    if b then B c*(mu^(arity c))^k else A c*(lam^(arity c))^k)
  simp only [Fintype.sum_bool,Bool.false_eq_true,ite_true,ite_false] at hh
  rw [show (∏ c,(A c*(lam^(arity c))^k+B c*(mu^(arity c))^k))=
    ∏ c,(B c*(mu^(arity c))^k+A c*(lam^(arity c))^k) by
      apply Finset.prod_congr rfl; intro c _; ring]
  rw [hh]
  apply Finset.sum_congr rfl
  intro choice _
  calc
    _ = ∏ c,(if choice c then B c else A c)*(if choice c then mu^(arity c) else lam^(arity c))^k := by
      apply Finset.prod_congr rfl
      intro c _
      cases choice c <;> rfl
    _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_pow,modeRate_eq]

/-- The spectral exponent j is an actual sum of component increments. -/
theorem modeRate_source_index (lam mu : R) (arity : C→ℕ) {d : ℕ}
    (hd : (∑ c,arity c)=d) (choice : C→Bool) :
    mixedModeDegree arity choice≤d ∧
      lam^(pureModeDegree arity choice)*mu^(mixedModeDegree arity choice)=
      lam^(d-mixedModeDegree arity choice)*mu^(mixedModeDegree arity choice) := by
  have hh:=modeDegrees_sum arity choice
  rw [hd] at hh
  constructor
  · omega
  · congr 2
    omega

/-- Apply the factored shift polynomial to a sequence. -/
def applyAnnihilator : List R→(ℕ→R)→ℕ→R
  | [],f,n => f n
  | a::as,f,n => applyAnnihilator as f (n+1)-a*applyAnnihilator as f n

lemma applyAnnihilator_exp (roots : List R) (a rate : R) (n : ℕ) :
    applyAnnihilator roots (fun k => a*rate^k) n=
      a*(roots.map (fun x => rate-x)).prod*rate^n := by
  induction roots generalizing n with
  | nil => simp [applyAnnihilator]
  | cons x xs ih =>
    rw [applyAnnihilator,ih,ih]
    simp only [List.map_cons,List.prod_cons,pow_succ]
    ring

lemma applyAnnihilator_sum {I : Type*} [Fintype I] (roots : List R) (f : I→ℕ→R) (n : ℕ) :
    applyAnnihilator roots (fun k => ∑ i,f i k) n=∑ i,applyAnnihilator roots (f i) n := by
  induction roots generalizing n with
  | nil => rfl
  | cons x xs ih =>
    rw [applyAnnihilator,ih,ih,Finset.mul_sum,← Finset.sum_sub_distrib]
    rfl

/-- Repeated roots cause no issue: one actual factor kills each exponential. -/
theorem annihilator_finite_exponentials {I : Type*} [Fintype I] (roots : List R)
    (A rate : I→R) (hroot : ∀ i,rate i∈roots) (n : ℕ) :
    applyAnnihilator roots (fun k => ∑ i,A i*(rate i)^k) n=0 := by
  rw [applyAnnihilator_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [applyAnnihilator_exp]
  have hz : (roots.map (fun x => rate i-x)).prod=0 := by
    apply List.prod_eq_zero
    exact List.mem_map.mpr ⟨rate i,hroot i,sub_self _⟩
  rw [hz,mul_zero,zero_mul]

end Ring
end SubmittedGenus.FixedPivot
