import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! The submitted quadratic-geometric tail identity, isolated from every
source graph, spectral matrix, and numerical certificate. -/
namespace SubmittedGenus.QuadraticGeometric
open scoped BigOperators Topology
open Filter
noncomputable section

def tail (x : ℝ) (K : ℕ) (a b c : ℝ) : ℝ :=
  x^K*((a*(K:ℝ)^2+b*K+c)/(1-x)+(2*a*K+b)*x/(1-x)^2+a*x*(1+x)/(1-x)^3)

lemma tail_step (x : ℝ) (K : ℕ) (a b c : ℝ) (hx : x≠1) :
    tail x K a b c=(a*(K:ℝ)^2+b*K+c)*x^K+tail x (K+1) a b c := by
  have hd : 1-x≠0 := sub_ne_zero.mpr (Ne.symm hx)
  unfold tail
  rw [pow_succ]
  push_cast
  field_simp
  ring

lemma tail_partial_sum (x : ℝ) (K M : ℕ) (a b c : ℝ) (hx : x≠1) :
    (∑ k∈Finset.range M,(a*((K+k:ℕ):ℝ)^2+b*((K+k:ℕ):ℝ)+c)*x^(K+k))+
      tail x (K+M) a b c=tail x K a b c := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ]
    have hs:=tail_step x (K+M) a b c hx
    rw [Nat.add_succ]
    calc
      _=(∑ k∈Finset.range M,(a*((K+k:ℕ):ℝ)^2+b*((K+k:ℕ):ℝ)+c)*x^(K+k))+
          ((a*((K+M:ℕ):ℝ)^2+b*((K+M:ℕ):ℝ)+c)*x^(K+M)+tail x (K+M+1) a b c) := by ring
      _=_ := by rw [← hs]; exact ih

lemma tail_tendsto_zero (x a b c : ℝ) (hx : |x|<1) :
    Tendsto (fun M : ℕ=>tail x M a b c) atTop (𝓝 0) := by
  have h2:=tendsto_pow_const_mul_const_pow_of_abs_lt_one 2 hx
  have h1:=tendsto_pow_const_mul_const_pow_of_abs_lt_one 1 hx
  have h0:=tendsto_pow_const_mul_const_pow_of_abs_lt_one 0 hx
  have hh:=((h2.const_mul (a/(1-x))).add
    (h1.const_mul (b/(1-x)+2*a*x/(1-x)^2))).add
    (h0.const_mul (c/(1-x)+b*x/(1-x)^2+a*x*(1+x)/(1-x)^3))
  convert hh using 1
  · funext M
    simp only [tail,pow_one,pow_zero,one_mul,div_eq_mul_inv]
    ring
  · simp

lemma summable (x a b c : ℝ) (hx : |x|<1) :
    Summable (fun k : ℕ=>(a*(k:ℝ)^2+b*k+c)*x^k) := by
  have hx' : ‖x‖<1 := hx
  have h2:=(summable_pow_mul_geometric_of_norm_lt_one 2 hx').mul_left a
  have h1:=(summable_pow_mul_geometric_of_norm_lt_one 1 hx').mul_left b
  have h0:=(summable_pow_mul_geometric_of_norm_lt_one 0 hx').mul_left c
  simpa only [pow_one,pow_zero,one_mul,add_mul,mul_assoc] using (h2.add h1).add h0

/-- Exact quadratic-geometric tail, with arbitrary real coefficients. -/
theorem hasSum_tail (x : ℝ) (K : ℕ) (a b c : ℝ) (hx : |x|<1) :
    HasSum (fun k : ℕ=>(a*((K+k:ℕ):ℝ)^2+b*((K+k:ℕ):ℝ)+c)*x^(K+k))
      (tail x K a b c) := by
  have hs : Summable (fun k : ℕ=>(a*((K+k:ℕ):ℝ)^2+b*((K+k:ℕ):ℝ)+c)*x^(K+k)) := by
    simpa only [Nat.add_comm] using (summable_nat_add_iff K).mpr (summable x a b c hx)
  have habs : Summable (fun k : ℕ=>‖(a*((K+k:ℕ):ℝ)^2+b*((K+k:ℕ):ℝ)+c)*x^(K+k)‖) := by
    simpa only [Real.norm_eq_abs] using hs.abs
  apply (hasSum_iff_tendsto_nat_of_summable_norm habs).mpr
  have ht:=(tail_tendsto_zero x a b c hx).comp (tendsto_add_atTop_nat K)
  have hl:=(tendsto_const_nhds : Tendsto (fun _ : ℕ=>tail x K a b c) atTop
    (𝓝 (tail x K a b c))).sub ht
  convert hl using 1
  · funext M
    have hne : x≠1 := by intro h; simp [h] at hx
    dsimp only [Function.comp_apply]
    rw [Nat.add_comm M K]
    exact (eq_sub_iff_add_eq).mpr (tail_partial_sum x K M a b c hne)
  · simp

theorem tsum_tail (x : ℝ) (K : ℕ) (a b c : ℝ) (hx : |x|<1) :
    (∑' k : ℕ,(a*((K+k:ℕ):ℝ)^2+b*((K+k:ℕ):ℝ)+c)*x^(K+k))=tail x K a b c :=
  (hasSum_tail x K a b c hx).tsum_eq

end
end SubmittedGenus.QuadraticGeometric
