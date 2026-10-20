import Results.Genus.CapFourMass.IntervalExpression

namespace SubmittedGenus.CapFourMass.Interval

def closedEval (e : Expr) : Option Box := e.eval (fun _ => point 0)
noncomputable def closedReal (e : Expr) : ℝ := e.real (fun _ => 0)

theorem closedEval_sound (e : Expr) {b : Box} (he : closedEval e=some b) :
    Contains b (closedReal e) :=
  Expr.eval_sound e (fun _ => by simpa using point_contains 0) he

/-- An accepting comparison comes after successful evaluation of every input operation. -/
def acceptsUpper (e : Expr) (n d : ℤ) : Bool :=
  match closedEval e with
  | none => false
  | some b => decide (0<d ∧ b.hi*d≤n*unit)

theorem acceptsUpper_sound {e : Expr} {n d : ℤ} (h : acceptsUpper e n d=true) :
    closedReal e≤(n:ℝ)/(d:ℝ) := by
  unfold acceptsUpper at h
  cases he : closedEval e with
  | none => simp [he] at h
  | some b =>
    simp only [he,decide_eq_true_eq] at h
    have hd : (0:ℝ)<d := by exact_mod_cast h.1
    have hi : (b.hi:ℝ)*(d:ℝ)≤(n:ℝ)*(unit:ℝ) := by exact_mod_cast h.2
    have hh := (closedEval_sound e he).2
    apply (le_div_iff₀ hd).mpr
    have hm := mul_le_mul_of_nonneg_right hh hd.le
    nlinarith only [hm,hi,unit_pos]

namespace Expr
instance : Add Expr := ⟨Expr.add⟩
instance : Sub Expr := ⟨Expr.sub⟩
instance : Mul Expr := ⟨Expr.mul⟩
instance : Div Expr := ⟨Expr.div⟩
instance : Pow Expr ℕ := ⟨Expr.pow⟩
instance (n : ℕ) : OfNat Expr n := ⟨Expr.integer n⟩

@[simp] theorem real_add (xs : ℕ → ℝ) (a b : Expr) : (a+b).real xs=a.real xs+b.real xs := rfl
@[simp] theorem real_sub (xs : ℕ → ℝ) (a b : Expr) : (a-b).real xs=a.real xs-b.real xs := rfl
@[simp] theorem real_mul (xs : ℕ → ℝ) (a b : Expr) : (a*b).real xs=a.real xs*b.real xs := rfl
@[simp] theorem real_div (xs : ℕ → ℝ) (a b : Expr) : (a/b).real xs=a.real xs/b.real xs := rfl
@[simp] theorem real_pow (xs : ℕ → ℝ) (a : Expr) (n : ℕ) : (a^n).real xs=a.real xs^n := rfl
@[simp] theorem real_nat (xs : ℕ → ℝ) (n : ℕ) :
    (OfNat.ofNat n : Expr).real xs=(n:ℝ) := by simp [real]

@[simp] theorem real_zero (xs : ℕ → ℝ) : (0 : Expr).real xs=0 := by norm_num [real]
@[simp] theorem real_one (xs : ℕ → ℝ) : (1 : Expr).real xs=1 := by norm_num [real]

end Expr
end SubmittedGenus.CapFourMass.Interval
