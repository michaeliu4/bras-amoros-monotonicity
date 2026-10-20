import Results.Genus.FixedPivot.QuadraticModes

/-! Exact two-mode expansion of the source carry transfer over its rational quadratic algebra. -/
namespace SubmittedGenus.FixedPivot
section Ring
variable {R : Type*} [CommRing R]

lemma carryStep_add (z : R) (v w : Fin 3 → R) :
    carryStep z (fun i => v i+w i)=fun i => carryStep z v i+carryStep z w i := by
  funext i
  fin_cases i <;> simp [carryStep] <;> ring

lemma carryStep_scale (z a : R) (v : Fin 3 → R) :
    carryStep z (fun i => a*v i)=fun i => a*carryStep z v i := by
  funext i
  fin_cases i <;> simp [carryStep] <;> ring

lemma carryStep_sub (z : R) (v w : Fin 3 → R) :
    carryStep z (fun i => v i-w i)=fun i => carryStep z v i-carryStep z w i := by
  funext i
  fin_cases i <;> simp [carryStep] <;> ring

/-- The lambda amplitude on the nonzero invariant subspace. -/
def modeLeft (z mu di : R) (v : Fin 3 → R) : Fin 3 → R :=
  fun i => di*(carryStep z v i-mu*v i)

/-- The mu amplitude on the same subspace. -/
def modeRight (z lam di : R) (v : Fin 3 → R) : Fin 3 → R :=
  fun i => di*(lam*v i-carryStep z v i)

lemma mode_sum (z lam mu di : R) (hdi : (lam-mu)*di=1) (v : Fin 3 → R) :
    (fun i => modeLeft z mu di v i+modeRight z lam di v i)=v := by
  funext i
  unfold modeLeft modeRight
  calc
    _ = ((lam-mu)*di)*v i := by ring
    _ = _ := by rw [hdi,one_mul]

lemma modeLeft_eigen (z lam mu di : R) (hb : lam+mu=carryB z)
    (hc : lam*mu=carryC z) (v : Fin 3 → R) (hv : v 2=v 1) :
    carryStep z (modeLeft z mu di v)=fun i => lam*modeLeft z mu di v i := by
  unfold modeLeft
  rw [carryStep_scale,carryStep_sub,carryStep_scale,carryStep_second_order z v hv]
  funext i
  simp only
  rw [← hb,← hc]
  ring

lemma modeRight_eigen (z lam mu di : R) (hb : lam+mu=carryB z)
    (hc : lam*mu=carryC z) (v : Fin 3 → R) (hv : v 2=v 1) :
    carryStep z (modeRight z lam di v)=fun i => mu*modeRight z lam di v i := by
  unfold modeRight
  rw [carryStep_scale,carryStep_sub,carryStep_scale,carryStep_second_order z v hv]
  funext i
  simp only
  rw [← hb,← hc]
  ring

/-- Exact source kernel expansion on the free/loop boundary subspace at every length. -/
theorem carryPower_modes (z lam mu di : R) (hb : lam+mu=carryB z)
    (hc : lam*mu=carryC z) (hdi : (lam-mu)*di=1)
    (n : ℕ) (v : Fin 3 → R) (hv : v 2=v 1) :
    carryPower z n v=fun i => lam^n*modeLeft z mu di v i+mu^n*modeRight z lam di v i := by
  induction n with
  | zero =>
    simp only [carryPower,pow_zero,one_mul]
    exact (mode_sum z lam mu di hdi v).symm
  | succ n ih =>
    rw [carryPower,ih,carryStep_add,carryStep_scale,carryStep_scale,
      modeLeft_eigen z lam mu di hb hc v hv,modeRight_eigen z lam mu di hb hc v hv]
    funext i
    simp only [pow_succ]
    ring

lemma carryPower_shift (z : R) (n : ℕ) (v : Fin 3 → R) :
    carryPower z (n+1) v=carryPower z n (carryStep z v) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change carryStep z (carryPower z (n+1) v)=carryStep z (carryPower z n (carryStep z v))
    rw [ih]

/-- Every arbitrary port kernel has the same exact two modes from one edge onward. -/
theorem carryPower_positive_modes (z lam mu di : R) (hb : lam+mu=carryB z)
    (hc : lam*mu=carryC z) (hdi : (lam-mu)*di=1) (n : ℕ) (v : Fin 3 → R) :
    carryPower z (n+1) v=fun i =>
      lam^n*modeLeft z mu di (carryStep z v) i+
      mu^n*modeRight z lam di (carryStep z v) i := by
  rw [carryPower_shift]
  exact carryPower_modes z lam mu di hb hc hdi n (carryStep z v) (carryStep_rows z v)

/-- The zero-edge loop boundary uses the full two-mode decomposition. -/
theorem loopTerminal_modes (z lam mu di : R) (hb : lam+mu=carryB z)
    (hc : lam*mu=carryC z) (hdi : (lam-mu)*di=1) (n : ℕ) :
    carryPower z n loopTerminal=fun i =>
      lam^n*modeLeft z mu di loopTerminal i+mu^n*modeRight z lam di loopTerminal i :=
  carryPower_modes z lam mu di hb hc hdi n loopTerminal rfl

end Ring
end SubmittedGenus.FixedPivot
