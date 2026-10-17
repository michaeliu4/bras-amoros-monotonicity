import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! Sound signed dyadic interval certificates at the refined scale 2^112.
Integer endpoints are untrusted until the local arithmetic check is proved.
No floating-point operation or native-evaluation axiom is used. -/
namespace SubmittedGenus.CapFourMass.Interval

abbrev unit : ℤ := 5192296858534827628530496329220096
lemma unit_pos : (0:ℝ)<unit := by norm_num
lemma unit_int_pos : (0:ℤ)<unit := by norm_num

structure Box where
  lo : ℤ
  hi : ℤ
  deriving DecidableEq, Repr

def Contains (a : Box) (x : ℝ) : Prop :=
  (a.lo:ℝ)≤(unit:ℝ)*x ∧ (unit:ℝ)*x≤(a.hi:ℝ)

def point (n : ℤ) : Box := ⟨n*unit,n*unit⟩
def add (a b : Box) : Box := ⟨a.lo+b.lo,a.hi+b.hi⟩
def neg (a : Box) : Box := ⟨-a.hi,-a.lo⟩
def sub (a b : Box) : Box := add a (neg b)
def endpt (a : Box) (i : Bool) : ℤ := if i then a.hi else a.lo
@[simp] lemma endpt_false (a : Box) : endpt a false=a.lo := rfl
@[simp] lemma endpt_true (a : Box) : endpt a true=a.hi := rfl

theorem point_contains (n : ℤ) : Contains (point n) n := by
  simp [Contains,point,mul_comm]

theorem add_contains {a b : Box} {x y : ℝ} (ha : Contains a x) (hb : Contains b y) :
    Contains (add a b) (x+y) := by
  constructor
  · change ((a.lo+b.lo:ℤ):ℝ)≤(unit:ℝ)*(x+y)
    rw [Int.cast_add,mul_add]
    exact add_le_add ha.1 hb.1
  · change (unit:ℝ)*(x+y)≤((a.hi+b.hi:ℤ):ℝ)
    rw [Int.cast_add,mul_add]
    exact add_le_add ha.2 hb.2

theorem neg_contains {a : Box} {x : ℝ} (ha : Contains a x) : Contains (neg a) (-x) := by
  constructor
  · change ((-a.hi:ℤ):ℝ)≤(unit:ℝ)*(-x)
    rw [Int.cast_neg,mul_neg]
    exact neg_le_neg ha.2
  · change (unit:ℝ)*(-x)≤((-a.lo:ℤ):ℝ)
    rw [Int.cast_neg,mul_neg]
    exact neg_le_neg ha.1

theorem sub_contains {a b : Box} {x y : ℝ} (ha : Contains a x) (hb : Contains b y) :
    Contains (sub a b) (x-y) := by
  change Contains (add a (neg b)) (x + -y)
  exact add_contains ha (neg_contains hb)

lemma scalar_lower {l u x c b : ℝ} (hl : l≤x) (hu : x≤u)
    (h0 : b≤l*c) (h1 : b≤u*c) : b≤x*c := by
  by_cases hc : 0≤c
  · exact h0.trans (mul_le_mul_of_nonneg_right hl hc)
  · exact h1.trans (mul_le_mul_of_nonpos_right hu (le_of_not_ge hc))

lemma scalar_upper {l u x c b : ℝ} (hl : l≤x) (hu : x≤u)
    (h0 : l*c≤b) (h1 : u*c≤b) : x*c≤b := by
  by_cases hc : 0≤c
  · exact (mul_le_mul_of_nonneg_right hu hc).trans h1
  · exact (mul_le_mul_of_nonpos_right hl (le_of_not_ge hc)).trans h0

lemma product_lower {l u v w x y b : ℝ} (hx : l≤x ∧ x≤u) (hy : v≤y ∧ y≤w)
    (h00 : b≤l*v) (h01 : b≤l*w) (h10 : b≤u*v) (h11 : b≤u*w) : b≤x*y := by
  have h0 := scalar_lower hx.1 hx.2 h00 h10
  have h1 := scalar_lower hx.1 hx.2 h01 h11
  have hh : b≤y*x := scalar_lower hy.1 hy.2 (by nlinarith only [h0]) (by nlinarith only [h1])
  nlinarith only [hh]

lemma product_upper {l u v w x y b : ℝ} (hx : l≤x ∧ x≤u) (hy : v≤y ∧ y≤w)
    (h00 : l*v≤b) (h01 : l*w≤b) (h10 : u*v≤b) (h11 : u*w≤b) : x*y≤b := by
  have h0 := scalar_upper hx.1 hx.2 h00 h10
  have h1 := scalar_upper hx.1 hx.2 h01 h11
  have hh : y*x≤b := scalar_upper hy.1 hy.2 (by nlinarith only [h0]) (by nlinarith only [h1])
  nlinarith only [hh]

/-- Eight exact integer comparisons certify a signed interval product. -/
def MulCertificate (a b c : Box) : Prop := ∀ i j : Bool,
  c.lo*unit≤endpt a i*endpt b j ∧ endpt a i*endpt b j≤c.hi*unit
instance (a b c : Box) : Decidable (MulCertificate a b c) := by
  unfold MulCertificate; infer_instance

theorem mul_certificate_sound {a b c : Box} {x y : ℝ}
    (ha : Contains a x) (hb : Contains b y) (h : MulCertificate a b c) :
    Contains c (x*y) := by
  have hc (i j : Bool) : (c.lo:ℝ)*(unit:ℝ)≤(endpt a i:ℝ)*(endpt b j:ℝ) ∧
      (endpt a i:ℝ)*(endpt b j:ℝ)≤(c.hi:ℝ)*(unit:ℝ) := by
    exact_mod_cast h i j
  have hl := product_lower ha hb (hc false false).1 (hc false true).1
    (hc true false).1 (hc true true).1
  have hu := product_upper ha hb (hc false false).2 (hc false true).2
    (hc true false).2 (hc true true).2
  have he : ((unit:ℝ)*x)*((unit:ℝ)*y)=((unit:ℝ)*(x*y))*(unit:ℝ) := by ring
  rw [he] at hl hu
  exact ⟨(mul_le_mul_iff_left₀ unit_pos).mp hl,(mul_le_mul_iff_left₀ unit_pos).mp hu⟩

/-- Positive-denominator division is checked in integers, including signs. -/
def DivCertificate (a b c : Box) : Prop := 0<b.lo ∧ ∀ i j : Bool,
  c.lo*endpt b j≤unit*endpt a i ∧ unit*endpt a i≤c.hi*endpt b j
instance (a b c : Box) : Decidable (DivCertificate a b c) := by
  unfold DivCertificate; infer_instance

theorem div_certificate_sound {a b c : Box} {x y : ℝ}
    (ha : Contains a x) (hb : Contains b y) (h : DivCertificate a b c) :
    Contains c (x/y) := by
  have hp : (0:ℝ)<b.lo := by exact_mod_cast h.1
  have hy : 0<y := by have hh := hb.1; nlinarith only [hp,hh,unit_pos]
  have hc (i j : Bool) : (c.lo:ℝ)*(endpt b j:ℝ)≤(unit:ℝ)*(endpt a i:ℝ) ∧
      (unit:ℝ)*(endpt a i:ℝ)≤(c.hi:ℝ)*(endpt b j:ℝ) := by
    exact_mod_cast h.2 i j
  have h00 := hc false false
  have h01 := hc false true
  have h10 := hc true false
  have h11 := hc true true
  simp only [endpt_false,endpt_true] at h00 h01 h10 h11
  have hl : (c.lo:ℝ)*((unit:ℝ)*y)≤(unit:ℝ)*(a.lo:ℝ) := by
    have hh : ((unit:ℝ)*y)*(c.lo:ℝ)≤(unit:ℝ)*(a.lo:ℝ) :=
      scalar_upper hb.1 hb.2 (by nlinarith only [h00.1]) (by nlinarith only [h01.1])
    nlinarith only [hh]
  have hu : (unit:ℝ)*(a.hi:ℝ)≤(c.hi:ℝ)*((unit:ℝ)*y) := by
    have hh : (unit:ℝ)*(a.hi:ℝ)≤((unit:ℝ)*y)*(c.hi:ℝ) :=
      scalar_lower hb.1 hb.2 (by nlinarith only [h10.2]) (by nlinarith only [h11.2])
    nlinarith only [hh]
  have hlx := hl.trans (mul_le_mul_of_nonneg_left ha.1 unit_pos.le)
  have hux := (mul_le_mul_of_nonneg_left ha.2 unit_pos.le).trans hu
  have hl' : (c.lo:ℝ)*y≤(unit:ℝ)*x := by
    apply (mul_le_mul_iff_left₀ unit_pos).mp
    convert hlx using 1 <;> ring
  have hu' : (unit:ℝ)*x≤(c.hi:ℝ)*y := by
    apply (mul_le_mul_iff_left₀ unit_pos).mp
    convert hux using 1 <;> ring
  constructor
  · simpa only [mul_div_assoc] using (le_div_iff₀ hy).mpr hl'
  · simpa only [mul_div_assoc] using (div_le_iff₀ hy).mpr hu'

def AbsCertificate (a b : Box) : Prop :=
  b.lo≤0 ∧ -a.lo≤b.hi ∧ a.hi≤b.hi
instance (a b : Box) : Decidable (AbsCertificate a b) := by
  unfold AbsCertificate; infer_instance

theorem abs_certificate_sound {a b : Box} {x : ℝ}
    (ha : Contains a x) (h : AbsCertificate a b) : Contains b |x| := by
  have h0 : (b.lo:ℝ)≤0 := by exact_mod_cast h.1
  have hl : -(a.lo:ℝ)≤(b.hi:ℝ) := by exact_mod_cast h.2.1
  have hu : (a.hi:ℝ)≤(b.hi:ℝ) := by exact_mod_cast h.2.2
  refine ⟨h0.trans (mul_nonneg unit_pos.le (abs_nonneg _)),?_⟩
  rw [←abs_of_pos unit_pos,←abs_mul]
  exact abs_le.mpr ⟨by linarith [ha.1],ha.2.trans hu⟩

end SubmittedGenus.CapFourMass.Interval
