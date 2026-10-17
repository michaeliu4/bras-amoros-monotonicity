import Results.Genus.CapFourMass.IntervalCore

namespace SubmittedGenus.CapFourMass.Interval

/-- The final integer comparison is independently checked after source enclosure. -/
theorem upper_of_contains {b : Box} {x : ℝ} {n d : ℤ}
    (hb : Contains b x) (hd : 0<d) (hhi : b.hi*d≤n*unit) : x≤(n:ℝ)/(d:ℝ) := by
  have hd' : (0:ℝ)<d := by exact_mod_cast hd
  have hc : (b.hi:ℝ)*(d:ℝ)≤(n:ℝ)*(unit:ℝ) := by exact_mod_cast hhi
  apply (le_div_iff₀ hd').mpr
  have hm:=mul_le_mul_of_nonneg_right hb.2 hd'.le
  nlinarith only [hm,hc,unit_pos]

end SubmittedGenus.CapFourMass.Interval
