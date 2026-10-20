import Results.Genus.CapFourMass.IntervalCompute

namespace SubmittedGenus.CapFourMass.Interval

/-- Binary exponentiation rounds outward after every multiplication. -/
def fastPower (a : Box) (n : ℕ) : Box :=
  if n=0 then point 1 else
    let b := fastPower a (n/2)
    let c := mul b b
    if n%2=0 then c else mul c a
termination_by n

theorem fastPower_contains {a : Box} {x : ℝ} (ha : Contains a x) (n : ℕ) :
    Contains (fastPower a n) (x^n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [fastPower]
    split_ifs with hn hp
    · subst n
      simpa only [pow_zero,Int.cast_one] using point_contains 1
    · have hh := ih (n/2) (by omega)
      have hsq := mul_contains hh hh
      have he : n/2+n/2=n := by omega
      simpa only [←pow_add,he] using hsq
    · have hh := ih (n/2) (by omega)
      have hcube := mul_contains (mul_contains hh hh) ha
      have he : n/2+n/2+1=n := by omega
      simpa only [←pow_add,←pow_succ,he] using hcube

end SubmittedGenus.CapFourMass.Interval
