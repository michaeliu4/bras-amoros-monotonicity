import Results.Genus.CapFourMass.IntervalPower

namespace SubmittedGenus.CapFourMass.Interval

/-- Arithmetic syntax, with explicit input intervals rather than trusted outputs. -/
inductive Expr where
  | integer : ℤ → Expr
  | input : ℕ → Expr
  | add : Expr → Expr → Expr
  | sub : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  | div : Expr → Expr → Expr
  | abs : Expr → Expr
  | pow : Expr → ℕ → Expr
  deriving Repr

noncomputable def Expr.real (xs : ℕ → ℝ) : Expr → ℝ
  | .integer n => n
  | .input i => xs i
  | .add a b => a.real xs + b.real xs
  | .sub a b => a.real xs - b.real xs
  | .mul a b => a.real xs * b.real xs
  | .div a b => a.real xs / b.real xs
  | .abs a => |a.real xs|
  | .pow a n => a.real xs ^ n

def Expr.eval (bs : ℕ → Box) : Expr → Option Box
  | .integer n => some (point n)
  | .input i => some (bs i)
  | .add a b => do return Interval.add (← a.eval bs) (← b.eval bs)
  | .sub a b => do return Interval.sub (← a.eval bs) (← b.eval bs)
  | .mul a b => do return Interval.mul (← a.eval bs) (← b.eval bs)
  | .div a b => do divide (← a.eval bs) (← b.eval bs)
  | .abs a => do return absolute (← a.eval bs)
  | .pow a n => do return fastPower (← a.eval bs) n

theorem Expr.eval_sound (e : Expr) {bs : ℕ → Box} {xs : ℕ → ℝ}
    (hi : ∀ i, Contains (bs i) (xs i)) {b : Box} (he : e.eval bs=some b) :
    Contains b (e.real xs) := by
  induction e generalizing b with
  | integer n =>
    simp only [Expr.eval,Option.some.injEq] at he
    subst b
    exact point_contains n
  | input i =>
    simp only [Expr.eval,Option.some.injEq] at he
    subst b
    exact hi i
  | add a c iha ihc =>
    cases ha : a.eval bs <;> cases hc : c.eval bs <;> simp [Expr.eval,ha,hc] at he
    subst b
    exact add_contains (iha ha) (ihc hc)
  | sub a c iha ihc =>
    cases ha : a.eval bs <;> cases hc : c.eval bs <;> simp [Expr.eval,ha,hc] at he
    subst b
    exact sub_contains (iha ha) (ihc hc)
  | mul a c iha ihc =>
    cases ha : a.eval bs <;> cases hc : c.eval bs <;> simp [Expr.eval,ha,hc] at he
    subst b
    exact mul_contains (iha ha) (ihc hc)
  | div a c iha ihc =>
    cases ha : a.eval bs <;> cases hc : c.eval bs <;> simp [Expr.eval,ha,hc] at he
    exact divide_sound (iha ha) (ihc hc) he
  | abs a ih =>
    cases ha : a.eval bs <;> simp [Expr.eval,ha] at he
    subst b
    exact absolute_contains (ih ha)
  | pow a n ih =>
    cases ha : a.eval bs <;> simp [Expr.eval,ha] at he
    subst b
    exact fastPower_contains (ih ha) n

/-- Division is deliberately kept in syntax, so a zero-crossing rejects. -/
def Expr.rational (n d : ℤ) : Expr := .div (.integer n) (.integer d)

@[simp] theorem Expr.rational_real (xs : ℕ → ℝ) (n d : ℤ) :
    (Expr.rational n d).real xs=(n:ℝ)/(d:ℝ) := rfl

end SubmittedGenus.CapFourMass.Interval
