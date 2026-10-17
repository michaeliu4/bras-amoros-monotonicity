import Results.Genus.GoldenTail.QuadraticTail
import Results.Genus.QuadraticGeometric

/-! Exact infinite-series interpretation of the submitted quadratic tail formula. -/
namespace SubmittedGenus.GoldenTail
open scoped BigOperators Topology
open Filter
noncomputable section

lemma quadraticTailReal_eq_general (x : ℝ) (K : ℕ) (a b c : ℝ) :
    quadraticTailReal x K a b c=QuadraticGeometric.tail x K a b c := rfl

lemma quadraticTailReal_tendsto_zero (x a b c : ℝ) (hx : |x|<1) :
    Tendsto (fun M : ℕ=>quadraticTailReal x M a b c) atTop (𝓝 0) :=
  QuadraticGeometric.tail_tendsto_zero x a b c hx

lemma quadraticGeometric_summable (x a b c : ℝ) (hx : |x|<1) :
    Summable (fun k : ℕ=>(a*(k:ℝ)^2+b*k+c)*x^k) :=
  QuadraticGeometric.summable x a b c hx

/-- Exact submitted display, including arbitrary real quadratic coefficients. -/
theorem quadraticTailReal_hasSum (x : ℝ) (K : ℕ) (a b c : ℝ) (hx : |x|<1) :
    HasSum (fun k : ℕ=>(a*((K+k:ℕ):ℝ)^2+b*((K+k:ℕ):ℝ)+c)*x^(K+k))
      (quadraticTailReal x K a b c) := QuadraticGeometric.hasSum_tail x K a b c hx

theorem quadraticTailReal_tsum (x : ℝ) (K : ℕ) (a b c : ℝ) (hx : |x|<1) :
    (∑' k : ℕ,(a*((K+k:ℕ):ℝ)^2+b*((K+k:ℕ):ℝ)+c)*x^(K+k))=
      quadraticTailReal x K a b c := (quadraticTailReal_hasSum x K a b c hx).tsum_eq

/-- Exact equality for the rational closed formula used by the B_K certificate. -/
theorem quadraticTail_hasSum (x : ℚ) (K : ℕ) (a b c : ℚ) (hx : |x|<1) :
    HasSum (fun k : ℕ=>((a:ℝ)*((K+k:ℕ):ℝ)^2+(b:ℝ)*((K+k:ℕ):ℝ)+(c:ℝ))*(x:ℝ)^(K+k))
      ((quadraticTail x K a b c : ℚ) : ℝ) := by
  rw [quadraticTail_cast]
  apply quadraticTailReal_hasSum
  exact_mod_cast hx

end
end SubmittedGenus.GoldenTail
