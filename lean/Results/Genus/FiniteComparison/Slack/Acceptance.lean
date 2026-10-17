import Results.Genus.FiniteComparison.Slack.Chunk00
import Results.Genus.FiniteComparison.Slack.Chunk01
import Results.Genus.FiniteComparison.Slack.Chunk02
import Results.Genus.FiniteComparison.Slack.Chunk03
import Results.Genus.FiniteComparison.Slack.Chunk04
import Results.Genus.FiniteComparison.Slack.Chunk05
import Results.Genus.FiniteComparison.Slack.Chunk06
import Results.Genus.FiniteComparison.Slack.Chunk07
import Results.Genus.FiniteComparison.Slack.Chunk08
import Results.Genus.FiniteComparison.Slack.Chunk09
import Results.Genus.FiniteComparison.Slack.Chunk10
import Results.Genus.FiniteComparison.Slack.Chunk11
import Results.Genus.FiniteComparison.Slack.Chunk12
import Results.Genus.FiniteComparison.Slack.Chunk13
namespace SubmittedGenus.FiniteComparison.Slack
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
open FiniteArithmetic.Reservoir
theorem all_rows (g:ℕ) (hg:1≤g) (hg':g≤836) : Row g := by
  by_cases h0 : g<65
  · exact checkedRange_apply checked_00 (by omega) h0
  by_cases h1 : g<129
  · exact checkedRange_apply checked_01 (by omega) h1
  by_cases h2 : g<193
  · exact checkedRange_apply checked_02 (by omega) h2
  by_cases h3 : g<257
  · exact checkedRange_apply checked_03 (by omega) h3
  by_cases h4 : g<321
  · exact checkedRange_apply checked_04 (by omega) h4
  by_cases h5 : g<385
  · exact checkedRange_apply checked_05 (by omega) h5
  by_cases h6 : g<449
  · exact checkedRange_apply checked_06 (by omega) h6
  by_cases h7 : g<513
  · exact checkedRange_apply checked_07 (by omega) h7
  by_cases h8 : g<577
  · exact checkedRange_apply checked_08 (by omega) h8
  by_cases h9 : g<641
  · exact checkedRange_apply checked_09 (by omega) h9
  by_cases h10 : g<705
  · exact checkedRange_apply checked_10 (by omega) h10
  by_cases h11 : g<769
  · exact checkedRange_apply checked_11 (by omega) h11
  by_cases h12 : g<833
  · exact checkedRange_apply checked_12 (by omega) h12
  exact checkedRange_apply checked_13 (by omega) (by omega)

theorem integer_minimum_attained : delta 1=1 ∧ delta 2=1 := by decide
theorem integer_minimum (g:ℕ) (hg:1≤g) (hg':g≤836) : 1≤delta g :=
  (all_rows g hg hg').1
theorem integer_minimum_only (g:ℕ) (hg:1≤g) (hg':g≤836) :
    delta g=1 ↔ g=1 ∨ g=2 := by
  constructor
  · intro h
    by_contra hn
    push Not at hn
    have hh := (all_rows g hg hg').2.2.2 hn.1 hn.2
    omega
  · rintro (rfl|rfl)
    · exact integer_minimum_attained.1
    · exact integer_minimum_attained.2

theorem ratio_lower_of_cross (a c:ℤ) (b d:ℕ) (hb:0<b) (hd:0<d)
    (h:a*(d:ℤ)≤c*(b:ℤ)) : (a:ℚ)/(b:ℚ)≤(c:ℚ)/(d:ℚ) := by
  apply (div_le_div_iff₀ (by exact_mod_cast hb) (by exact_mod_cast hd)).mpr
  exact_mod_cast h

theorem fibonacci_minimum (g:ℕ) (hg:1≤g) (hg':g≤836) :
    (15028705:ℚ)/33489287≤(delta g:ℚ)/(Nat.fib g:ℚ) := by
  have h := (all_rows g hg hg').2.1
  rw [Nat.fastFib_eq] at h
  exact ratio_lower_of_cross 15028705 (delta g) 33489287 (Nat.fib g)
    (by norm_num) (Nat.fib_pos.mpr (by omega)) (by simpa [mul_comm] using h)

theorem fibonacci_minimum_attained :
    (delta 42:ℚ)/(Nat.fib 42:ℚ)=(15028705:ℚ)/33489287 := by
  have hd : delta 42=120229640 := by decide
  have hf : Nat.fastFib 42=267914296 := by decide
  rw [Nat.fastFib_eq] at hf
  rw [hd,hf]
  norm_num

theorem fibonacci_minimum_decimal : (448761:ℚ)/1000000<(15028705:ℚ)/33489287 := by norm_num

theorem capacity_minimum_attained_values :
    delta 605=minimumCapacityNumerator ∧ capacityLookup837 605=minimumCapacityDenominator := by decide

theorem capacity_minimum (g:ℕ) (hg:1≤g) (hg':g≤836) :
    (minimumCapacityNumerator:ℚ)/(minimumCapacityDenominator:ℚ)≤
      (delta g:ℚ)/(originalCapacity g:ℚ) := by
  have h := (all_rows g hg hg').2.2.1
  have hd := (all_rows g hg hg').1
  have he := (all_comparisons g hg hg').1
  have hc : 0<capacityLookup837 g := by unfold delta at hd; omega
  have hr := ratio_lower_of_cross minimumCapacityNumerator (delta g)
    minimumCapacityDenominator (capacityLookup837 g) (by decide) hc (by simpa [mul_comm] using h)
  rwa [capacityLookup837_correct g (by omega)] at hr

theorem capacity_minimum_attained :
    (delta 605:ℚ)/(originalCapacity 605:ℚ)=
      (minimumCapacityNumerator:ℚ)/(minimumCapacityDenominator:ℚ) := by
  rw [←capacityLookup837_correct 605 (by omega),capacity_minimum_attained_values.1,
    capacity_minimum_attained_values.2]

theorem capacity_minimum_decimal :
    (179861:ℚ)/1000000<(minimumCapacityNumerator:ℚ)/(minimumCapacityDenominator:ℚ) := by
  norm_num [minimumCapacityNumerator,minimumCapacityDenominator]

#print axioms integer_minimum
#print axioms fibonacci_minimum
#print axioms capacity_minimum
end SubmittedGenus.FiniteComparison.Slack
