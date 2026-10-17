import Results.Genus.CapFourMass.IntervalClosed

namespace SubmittedGenus.CapFourMass.Interval

def acceptsUpperIn (bs : ℕ → Box) (e : Expr) (n d : ℤ) : Bool :=
  match e.eval bs with
  | none => false
  | some b => decide (0<d ∧ b.hi*d≤n*unit)

theorem acceptsUpperIn_sound {bs : ℕ → Box} {xs : ℕ → ℝ} {e : Expr} {n d : ℤ}
    (hi : ∀i,Contains (bs i) (xs i)) (h : acceptsUpperIn bs e n d=true) :
    e.real xs≤(n:ℝ)/(d:ℝ) := by
  unfold acceptsUpperIn at h
  cases he : e.eval bs with
  | none => simp [he] at h
  | some b =>
    simp only [he,decide_eq_true_eq] at h
    have hd : (0:ℝ)<d := by exact_mod_cast h.1
    have hc : (b.hi:ℝ)*(d:ℝ)≤(n:ℝ)*(unit:ℝ) := by exact_mod_cast h.2
    have hh := (Expr.eval_sound e hi he).2
    apply (le_div_iff₀ hd).mpr
    have hm := mul_le_mul_of_nonneg_right hh hd.le
    nlinarith only [hm,hc,unit_pos]

end SubmittedGenus.CapFourMass.Interval
