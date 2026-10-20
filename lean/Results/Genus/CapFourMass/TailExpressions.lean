import Results.Genus.CapFourMass.ParitySum
import Results.Genus.CapFourMass.PivotCoordinates
import Results.Genus.CapFourMass.Normalization
import Results.Genus.CapFourMass.ThreeEvaluation
import Results.Genus.CapFourMass.EndpointBounds
import Results.Genus.CapFourMass.PureMultiplicity

/-! Original rational omitted-tail expressions with convergent source sums. -/
noncomputable section
open scoped BigOperators
namespace SubmittedGenus.CapFourMass

abbrev ParityPair := Fin 2 × Fin 2
abbrev TailIndex := ParityPair × (ℕ×ℕ)

def Htail (P : ℕ) (u v : Fin 2) (A B : ℝ) : ℝ :=
  omittedParityRational A B sigma P (u.val+1) (v.val+1) (parityOffset u v)

def Gtail (P : ℕ) (x : ℝ) : ℝ :=
  ∑ uv : ParityPair, lambdaBound^(2*(uv.2.val+1))*x^((uv.2.val:ℤ)-(uv.1.val:ℤ))*
    Htail P uv.1 uv.2 (mixedA x) (mixedB x)

def GtailTerm (P : ℕ) (x : ℝ) (i : TailIndex) : ℝ :=
  lambdaBound^(2*(i.1.2.val+1))*x^((i.1.2.val:ℤ)-(i.1.1.val:ℤ))*
    omittedParityTerm (mixedA x) (mixedB x) sigma P (i.1.1.val+1) (i.1.2.val+1)
      (parityOffset i.1.1 i.1.2) i.2

lemma GtailTerm_nonneg (P : ℕ) {x : ℝ} (hx : 0 < x) (i : TailIndex) : 0 ≤ GtailTerm P x i := by
  have hA : 0 ≤ mixedA x := div_nonneg eta_bounds.1.le (sq_nonneg _)
  have hB : 0 ≤ mixedB x := by
    unfold mixedB
    exact mul_nonneg (mul_nonneg eta_bounds.1.le (pow_nonneg lambdaBound_pos.le _)) (sq_nonneg _)
  unfold GtailTerm
  exact mul_nonneg (mul_nonneg (pow_nonneg lambdaBound_pos.le _) (zpow_pos hx _).le)
    (omittedParity_nonneg hA hB sigma_bounds.1.le _ _ _ _ _)

lemma Gtail_row_hasSum (P : ℕ) {x : ℝ} (hconv : convergenceDomain (mixedA x) (mixedB x))
    (uv : ParityPair) :
    HasSum (fun q : ℕ×ℕ => GtailTerm P x (uv,q))
      (lambdaBound^(2*(uv.2.val+1))*x^((uv.2.val:ℤ)-(uv.1.val:ℤ))*
        Htail P uv.1 uv.2 (mixedA x) (mixedB x)) := by
  exact (omittedParity_hasSum hconv.1 hconv.2.1 sigma_bounds.1.le hconv.2.2.1
    hconv.2.2.2.1 hconv.2.2.2.2.1 hconv.2.2.2.2.2 P (uv.1.val+1) (uv.2.val+1)
    (parityOffset uv.1 uv.2) (parityOffset_le _ _)).mul_left _

/-- The rational G is exactly its nonnegative omitted-pivot series. -/
theorem Gtail_hasSum (P : ℕ) {x : ℝ} (hx : 0 < x)
    (hconv : convergenceDomain (mixedA x) (mixedB x)) :
    HasSum (GtailTerm P x) (Gtail P x) := by
  have hs : Summable (GtailTerm P x) :=
    (summable_prod_of_nonneg (GtailTerm_nonneg P hx)).mpr
      ⟨fun uv => (Gtail_row_hasSum P hconv uv).summable, (hasSum_fintype _).summable⟩
  have he : (∑' i, GtailTerm P x i)=Gtail P x := by
    rw [hs.tsum_prod,tsum_fintype]
    apply Finset.sum_congr rfl
    intro uv _
    exact (Gtail_row_hasSum P hconv uv).tsum_eq
  exact he ▸ hs.hasSum

def shortTailExpression (P : ℕ) : ℝ :=
  radius^8*alphabetMass/(lambdaBound^2*eta*(lambdaBound-1))*
    ∑ uv : ParityPair,
      (lambdaBound^(2*(uv.2.val+1))*Htail P uv.1 uv.2 eta (eta*lambdaBound^4)-
        lambdaBound^(uv.2.val+1)*Htail P uv.1 uv.2 eta (eta*lambdaBound^2))

def mixedTailConstant : ℝ := radius^8*alphabetMass*(1+lambdaBound)*feedbackT/(lambdaBound^2*eta)

def mixedTailExpression (P : ℕ) : ℝ :=
  mixedTailConstant/(1-mixedJ)*
    (Gtail P tBound-Gtail P (tBound*mixedJ)+
      negativeSquare/(1-negativeSquare)*(Gtail P (tBound*mixedJ)-Gtail P (tBound*mixedJ^2)))

def parityMultiplicity (v : Fin 2) : ℝ := if v=0 then pureParityOne else pureParityTwo

def pureTailExpression (P : ℕ) : ℝ :=
  radius^8*alphabetMass*feedbackT*
    ∑ uv : ParityPair,
      feedbackBeta^(-((uv.2.val+1:ℕ):ℤ))*tBound^((uv.2.val:ℤ)-(uv.1.val:ℤ))*
        parityMultiplicity uv.2/(eta*(1-pureJ))*Htail P uv.1 uv.2 pureA pureB

/-- All six parity parameter families in the submitted three omitted tails
satisfy the exact source convergence domain. -/
theorem original_tail_convergence :
    convergenceDomain eta (eta*lambdaBound^2) ∧
    convergenceDomain eta (eta*lambdaBound^4) ∧
    convergenceDomain (mixedA tBound) (mixedB tBound) ∧
    convergenceDomain (mixedA (tBound*mixedJ)) (mixedB (tBound*mixedJ)) ∧
    convergenceDomain (mixedA (tBound*mixedJ^2)) (mixedB (tBound*mixedJ^2)) ∧
    convergenceDomain pureA pureB :=
  ⟨short_convergence_two,short_convergence_four,mixed_convergence_zero,
    mixed_convergence_one,mixed_convergence_two,pure_convergence⟩

end SubmittedGenus.CapFourMass
