import Results.Genus.InverseCertificates.Data
import Results.Genus.GoldenSpectral.RankProducts

/-!
# Exact omitted-pivot B150 arithmetic from the submitted manuscript

Source: submitted-manuscript-e04fb276.tex, lines1534–1572. These definitions
are the displayed rational expression, with no source-graph estimate assumed.
The separate structural summation theorem must identify this expression as its
majorant. All numerical acceptance below is kernel-checked rational arithmetic.
-/
namespace SubmittedGenus.GoldenTail

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2000

def R : ℚ := 917 / 1000
def k0 : ℚ := 10003 / 10000
def chi : ℚ := 47597 / 50000
def t : ℚ := 95761 / 100000

def X : ℚ := R * t * chi
def Y : ℚ := R * t^2
def U : ℚ := 1 - R^2 * chi / t
def V : ℚ := t / chi - 1

/-- Closed quadratic geometric tail, manuscript equation raw:geometric-tail. -/
def quadraticTail (x : ℚ) (K : ℕ) (a b c : ℚ) : ℚ :=
  x^K * ((a*(K:ℚ)^2 + b*K + c)/(1-x) +
    (2*a*K+b)*x/(1-x)^2 + a*x*(1+x)/(1-x)^3)

/-- The sum s4 evaluated at the submitted rational upper endpoint qPlus. -/
def s4Upper : ℚ := InverseCertificates.qUpper + InverseCertificates.qUpper^2 +
  InverseCertificates.qUpper^3 + InverseCertificates.qUpper^4

/-- Exactly the original explicit tail expression, including chi^(-16). -/
def B (K : ℕ) : ℚ :=
  945 * InverseCertificates.qUpper^8 * s4Upper * k0^3 / chi^16 / (R*t^2) *
    (quadraticTail X K (12*chi+12*chi^2) (26*chi+38*chi^2) (16*chi+32*chi^2) / U +
     quadraticTail Y K (12*t+12*t^2) (26*t+38*t^2) (16*t+32*t^2) / V)

lemma R_pos : 0 < R := by norm_num [R]
lemma k0_pos : 0 < k0 := by norm_num [k0]
lemma chi_pos : 0 < chi := by norm_num [chi]
lemma t_pos : 0 < t := by norm_num [t]
lemma X_pos : 0 < X := by norm_num [X,R,t,chi]
lemma X_lt_Y : X < Y := by norm_num [X,Y,R,t,chi]
lemma Y_lt_one : Y < 1 := by norm_num [Y,R,t]
lemma U_pos : 0 < U := by norm_num [U,R,chi,t]
lemma V_pos : 0 < V := by norm_num [V,chi,t]

/-- The rational constants agree with the independently proved spectral ones. -/
lemma R_cast : (R:ℝ) = GoldenSpectral.strongBound := by
  norm_num [R,GoldenSpectral.strongBound]
lemma k0_cast : (k0:ℝ) = GoldenSpectral.pathInflation := by
  norm_num [k0,GoldenSpectral.pathInflation]
lemma chi_cast : (chi:ℝ) = GoldenSpectral.gapDecay := by
  norm_num [chi,GoldenSpectral.gapDecay]
lemma t_cast : (t:ℝ) = GoldenSpectral.tiltBound := by
  norm_num [t,GoldenSpectral.tiltBound]

/-- Original paper's sharper rational endpoint, not a replacement bound. -/
theorem B150_lt_first : B 150 < 221714122 / 10^9 := by
  norm_num [B,quadraticTail,X,Y,U,V,R,t,chi,k0,s4Upper,InverseCertificates.qUpper]

theorem original_endpoints_lt : (221714122 / 10^9 : ℚ) < 221715 / 10^6 := by
  norm_num

/-- The exact original 221715/1e6 coefficient multiplier. -/
theorem B150_lt : B 150 < 221715 / 10^6 :=
  B150_lt_first.trans original_endpoints_lt

theorem B150_cast_lt_first : ((B 150:ℚ):ℝ) < 221714122 / 10^9 := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow] using
    (Rat.cast_lt (K := ℝ)).mpr B150_lt_first

theorem B150_cast_lt : ((B 150:ℚ):ℝ) < 221715 / 10^6 := by
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow] using
    (Rat.cast_lt (K := ℝ)).mpr B150_lt

end SubmittedGenus.GoldenTail
