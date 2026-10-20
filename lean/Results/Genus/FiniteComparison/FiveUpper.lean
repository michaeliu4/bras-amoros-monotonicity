import Results.Genus.FiniteComparison.Tables
import Results.Genus.CapFiveMass.MassBound

namespace SubmittedGenus.FiniteComparison

/-- The original rational floor bounds the genuine B coefficient. This does
not assert the same estimate for the larger raw two-pivot population. -/
theorem genuineFive_le_rational_floor (g : ℕ) :
    CapFiveMass.count g ≤ 113*1000^g/633^g := by
  have hm := CapFiveMass.mass_five
  have ht := hm.1.le_tsum g (fun n _ =>
    mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num : (0:ℝ)≤633/1000) _))
  have hh : (CapFiveMass.count g:ℝ)*((633:ℝ)/1000)^g < 113 := ht.trans_lt hm.2
  rw [div_pow,←mul_div_assoc] at hh
  have hp : (0:ℝ)<1000^g := by positivity
  have hi := (div_lt_iff₀ hp).mp hh
  have hn : CapFiveMass.count g*633^g < 113*1000^g := by exact_mod_cast hi
  exact (Nat.le_div_iff_mul_le (by positivity : 0<633^g)).mpr hn.le

/-- The mass branch of literal V is unconditional for every genus≥301. -/
theorem genuineFive_le_upperFive (g : ℕ) (hg : 301≤g) :
    CapFiveMass.count g≤upperFive g := by
  simpa only [upperFive,if_neg (show ¬g≤300 by omega)] using genuineFive_le_rational_floor g

#print axioms genuineFive_le_rational_floor
#print axioms genuineFive_le_upperFive
end SubmittedGenus.FiniteComparison
