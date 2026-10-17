import Results.Genus.CapFourMass.IntervalParity
import Results.Genus.CapFourMass.IntervalClosed
import Results.Genus.CapFourMass.TailExpressions

open scoped BigOperators
namespace SubmittedGenus.CapFourMass.Interval
namespace TailSyntax

open Expr

def z : Expr := rational 1247 2000
def L : Expr := rational 101778011 100000000
def w : Expr := rational 70651823329321825 72057594037927936
def t : Expr := rational 252061464497 250000000000
def a : Expr := z
def b : Expr := z^2+z^3
def s : Expr := a+b
def eps : Expr := a*b*z^3/(s*(a*b+s^2))
def beta : Expr := 1-eps
def gamma : Expr := 1-eps/(1+z)^2
def T : Expr := gamma/beta
def etaE : Expr := rational 23389 25000/L
def sigmaE : Expr := rational 72789 100000/rational 23389 25000
def J : Expr := (w*L)^2
def J0 : Expr := L^2*beta
def q : Expr := (rational 39 100)^2
def mass : Expr := z+z^2+z^3+z^4

def invPower (e : Expr) (n : ℕ) : Expr := 1/e^n
def parityPower (e : Expr) (u v : Fin 2) : Expr := if u.val≤v.val then e^(v.val-u.val) else 1/e^(u.val-v.val)
def sumParity (f : Fin 2 → Fin 2 → Expr) : Expr :=
  (f 0 0+f 0 1)+(f 1 0+f 1 1)
def H (P : ℕ) (u v : Fin 2) (A B : Expr) : Expr :=
  parityTail A B sigmaE P (u.val+1) (v.val+1) (parityOffset u v)
def mixA (x : Expr) : Expr := etaE/x^2
def mixB (x : Expr) : Expr := etaE*L^4*x^2
def G (P : ℕ) (x : Expr) : Expr :=
  sumParity (fun u v => L^(2*(v.val+1))*parityPower x u v*H P u v (mixA x) (mixB x))

def short (P : ℕ) : Expr :=
  z^8*mass/(L^2*etaE*(L-1))*sumParity (fun u v =>
    L^(2*(v.val+1))*H P u v etaE (etaE*L^4)-L^(v.val+1)*H P u v etaE (etaE*L^2))
def mixedConstant : Expr := z^8*mass*(1+L)*T/(L^2*etaE)
def mixed (P : ℕ) : Expr := mixedConstant/(1-J)*
  (G P t-G P (t*J)+q/(1-q)*(G P (t*J)-G P (t*J^2)))
def pureAExpr : Expr := etaE/t^2
def pureBExpr : Expr := etaE*J0*invPower beta 2*t^2
def parityMult (v : Fin 2) : Expr := if v=0 then invPower L 2*J0+invPower L 1
  else (invPower L 2+invPower L 1)*J0
def pure (P : ℕ) : Expr := z^8*mass*T*sumParity (fun u v =>
  invPower beta (v.val+1)*parityPower t u v*parityMult v/(etaE*(1-J0))*
    H P u v pureAExpr pureBExpr)

@[simp] theorem z_real (xs : ℕ → ℝ) : z.real xs=radius := by norm_num [z,radius]
@[simp] theorem L_real (xs : ℕ → ℝ) : L.real xs=lambdaBound := by norm_num [L,lambdaBound]
@[simp] theorem w_real (xs : ℕ → ℝ) : w.real xs=normalizer := by norm_num [w,normalizer]
@[simp] theorem t_real (xs : ℕ → ℝ) : t.real xs=tBound := by norm_num [t,tBound]
@[simp] theorem beta_real (xs : ℕ → ℝ) : beta.real xs=feedbackBeta := by
  simp [beta,eps,s,a,b,feedbackBeta,LocalWeights.epsilon,LocalWeights.s,LocalWeights.a,LocalWeights.b]
@[simp] theorem gamma_real (xs : ℕ → ℝ) : gamma.real xs=feedbackGamma := by
  simp [gamma,eps,s,a,b,feedbackGamma,LocalWeights.delta,LocalWeights.epsilon,
    LocalWeights.s,LocalWeights.a,LocalWeights.b]
@[simp] theorem T_real (xs : ℕ → ℝ) : T.real xs=feedbackT := by simp [T,feedbackT]
@[simp] theorem eta_real (xs : ℕ → ℝ) : etaE.real xs=eta := by simp [etaE,eta,strongBound]
@[simp] theorem sigma_real (xs : ℕ → ℝ) : sigmaE.real xs=sigma := by
  simp [sigmaE,sigma,restrictedBound,strongBound]
@[simp] theorem J_real (xs : ℕ → ℝ) : J.real xs=mixedJ := by simp [J,mixedJ]
@[simp] theorem J0_real (xs : ℕ → ℝ) : J0.real xs=pureJ := by simp [J0,pureJ]
@[simp] theorem q_real (xs : ℕ → ℝ) : q.real xs=negativeSquare := by simp [q,negativeSquare]
@[simp] theorem mass_real (xs : ℕ → ℝ) : mass.real xs=alphabetMass := by
  simp [mass,alphabetMass,State,Fin.sum_univ_succ ]
  ring
@[simp] theorem invPower_real (xs : ℕ → ℝ) (e : Expr) (n : ℕ) :
    (invPower e n).real xs=e.real xs^(-(n:ℤ)) := by simp [invPower,zpow_neg,zpow_natCast]
@[simp] theorem parityPower_real (xs : ℕ → ℝ) (e : Expr) (u v : Fin 2) :
    (parityPower e u v).real xs=e.real xs^((v.val:ℤ)-(u.val:ℤ)) := by
  fin_cases u <;> fin_cases v <;> simp [parityPower]
@[simp] theorem sumParity_real (xs : ℕ → ℝ) (f : Fin 2 → Fin 2 → Expr) :
    (sumParity f).real xs=∑uv : ParityPair,(f uv.1 uv.2).real xs := by
  simp [sumParity,Fintype.sum_prod_type,Fin.sum_univ_two]

@[simp] theorem mixA_real (xs : ℕ → ℝ) (x : Expr) :
    (mixA x).real xs=mixedA (x.real xs) := by simp [mixA,mixedA]
@[simp] theorem mixB_real (xs : ℕ → ℝ) (x : Expr) :
    (mixB x).real xs=mixedB (x.real xs) := by simp [mixB,mixedB]
@[simp] theorem pureA_real (xs : ℕ → ℝ) : pureAExpr.real xs=pureA := by simp [pureAExpr,pureA]
@[simp] theorem pureB_real (xs : ℕ → ℝ) : pureBExpr.real xs=pureB := by simp [pureBExpr,pureB]
@[simp] theorem parityMult_real (xs : ℕ → ℝ) (v : Fin 2) :
    (parityMult v).real xs=parityMultiplicity v := by
  fin_cases v <;> simp [parityMult,parityMultiplicity,pureParityOne,pureParityTwo]

/-- Every input domain premise comes from a proved original convergence domain. -/
theorem H_real (xs : ℕ → ℝ) (P : ℕ) (u v : Fin 2) (A B : Expr)
    (hc : convergenceDomain (A.real xs) (B.real xs)) :
    (H P u v A B).real xs=Htail P u v (A.real xs) (B.real xs) := by
  unfold H Htail
  have hb := hc.2.2.2.2.2
  have hbs : B.real xs*sigmaE.real xs≠1 := by
    rw [sigma_real]
    exact ne_of_lt hc.2.2.2.2.1
  rw [parityTail_real xs A B sigmaE hb hbs _ _ _ _ (parityOffset_le u v),sigma_real]

theorem G_real (xs : ℕ → ℝ) (P : ℕ) (x : Expr)
    (hc : convergenceDomain (mixedA (x.real xs)) (mixedB (x.real xs))) :
    (G P x).real xs=Gtail P (x.real xs) := by
  unfold G Gtail
  rw [sumParity_real]
  apply Finset.sum_congr rfl
  intro uv _
  simp only [real_mul,real_pow,L_real,parityPower_real]
  rw [H_real xs P uv.1 uv.2 (mixA x) (mixB x) (by simpa using hc)]
  simp only [mixA_real,mixB_real]

theorem short_real (xs : ℕ → ℝ) (P : ℕ) : (short P).real xs=shortTailExpression P := by
  unfold short shortTailExpression
  simp only [real_mul,real_pow,z_real,mass_real,real_div,L_real,eta_real,real_sub,real_one]
  congr 1
  rw [sumParity_real]
  apply Finset.sum_congr rfl
  intro uv _
  simp only [real_sub,real_mul,real_pow,L_real]
  rw [H_real xs P uv.1 uv.2 etaE (etaE*L^4) (by simpa using short_convergence_four),
    H_real xs P uv.1 uv.2 etaE (etaE*L^2) (by simpa using short_convergence_two)]
  simp

theorem mixed_real (xs : ℕ → ℝ) (P : ℕ) : (mixed P).real xs=mixedTailExpression P := by
  unfold mixed mixedTailExpression
  simp only [real_mul,real_div,real_sub,real_add,real_one,J_real,q_real]
  rw [G_real xs P t (by simpa using mixed_convergence_zero),
    G_real xs P (t*J) (by simpa using mixed_convergence_one),
    G_real xs P (t*J^2) (by simpa using mixed_convergence_two)]
  simp [mixedConstant,mixedTailConstant]

theorem pure_real (xs : ℕ → ℝ) (P : ℕ) : (pure P).real xs=pureTailExpression P := by
  unfold pure pureTailExpression
  simp only [real_mul,real_pow,z_real,mass_real,T_real]
  congr 1
  rw [sumParity_real]
  apply Finset.sum_congr rfl
  intro uv _
  simp only [real_mul,real_div,real_sub,real_one,invPower_real,beta_real,parityPower_real,
    t_real,parityMult_real,eta_real,J0_real]
  rw [H_real xs P uv.1 uv.2 pureAExpr pureBExpr (by simpa using pure_convergence)]
  simp

end TailSyntax
end SubmittedGenus.CapFourMass.Interval
