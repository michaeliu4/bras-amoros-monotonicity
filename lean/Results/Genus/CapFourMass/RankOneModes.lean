import Results.Genus.CapFourMass.SourcePorts

/-! Exact labelled carry-edge projectors and every positive run power. -/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFourMass

lemma modeVector_dot (i j : Mode) :
    modeVector i ⬝ᵥ modeVector j=if i=j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [modeVector,qplus_self,qminus_self,qplus_qminus,qminus_qplus]

def modeProjector (j : Mode) : Matrix State State ℝ :=
  fun a b => modeVector j a*modeVector j b

lemma modeProjector_mul (i j : Mode) :
    modeProjector i*modeProjector j=if i=j then modeProjector i else 0 := by
  ext a b
  have he : (modeProjector i*modeProjector j) a b=
      modeVector i a*(modeVector i ⬝ᵥ modeVector j)*modeVector j b := by
    simp only [modeProjector,Matrix.mul_apply,dotProduct,Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he,modeVector_dot]
  by_cases hij : i=j
  · subst j
    simp [modeProjector]
  · simp [hij]

lemma modeProjector_square (j : Mode) : modeProjector j*modeProjector j=modeProjector j := by
  simp only [modeProjector_mul,if_true]

lemma scaled_modeProjector_power (a : ℝ) (j : Mode) (n : ℕ) (hn : 1≤n) :
    (a • modeProjector j)^n=a^n • modeProjector j := by
  obtain ⟨k,rfl⟩ : ∃ k,n=k+1 := ⟨n-1,by omega⟩
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ,ih (by omega),smul_mul_smul,modeProjector_square]
    simp only [pow_succ]

lemma carry_mode_power (j : Mode) (n : ℕ) (hn : 1≤n) :
    (modeRoot j • modeProjector j)^n=modeRoot j^n • modeProjector j :=
  scaled_modeProjector_power _ _ _ hn

end SubmittedGenus.CapFourMass
