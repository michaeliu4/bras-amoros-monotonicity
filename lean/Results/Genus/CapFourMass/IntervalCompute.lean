import Results.Genus.CapFourMass.IntervalCore

/-! Unbounded-integer implementation of original outward dyadic arithmetic.
Every arithmetic operation has a kernel-proved real enclosure theorem. -/
namespace SubmittedGenus.CapFourMass.Interval

def ceilDiv (n d : ℤ) : ℤ := -((-n)/d)
def min4 (a b c d : ℤ) : ℤ := min (min a b) (min c d)
def max4 (a b c d : ℤ) : ℤ := max (max a b) (max c d)

lemma floor_mul_le (n d : ℤ) (hd : 0<d) : (n/d)*d≤n :=
  Int.ediv_mul_le n (ne_of_gt hd)
lemma le_ceil_mul (n d : ℤ) (hd : 0<d) : n≤ceilDiv n d*d := by
  have h := floor_mul_le (-n) d hd
  unfold ceilDiv
  nlinarith only [h]

def mul (a b : Box) : Box :=
  ⟨min4 (a.lo*b.lo/unit) (a.lo*b.hi/unit) (a.hi*b.lo/unit) (a.hi*b.hi/unit),
   max4 (ceilDiv (a.lo*b.lo) unit) (ceilDiv (a.lo*b.hi) unit)
     (ceilDiv (a.hi*b.lo) unit) (ceilDiv (a.hi*b.hi) unit)⟩

lemma mul_lower_corner (a b : Box) (i j : Bool) :
    (mul a b).lo≤endpt a i*endpt b j/unit := by
  cases i <;> cases j <;> simp only [endpt_false,endpt_true,mul,min4] <;> omega
lemma mul_upper_corner (a b : Box) (i j : Bool) :
    ceilDiv (endpt a i*endpt b j) unit≤(mul a b).hi := by
  cases i <;> cases j <;> simp only [endpt_false,endpt_true,mul,max4] <;> omega

theorem mul_certificate (a b : Box) : MulCertificate a b (mul a b) := by
  intro i j
  constructor
  · exact (mul_le_mul_of_nonneg_right (mul_lower_corner a b i j) unit_int_pos.le).trans
      (floor_mul_le _ _ unit_int_pos)
  · exact (le_ceil_mul _ _ unit_int_pos).trans
      (mul_le_mul_of_nonneg_right (mul_upper_corner a b i j) unit_int_pos.le)

theorem mul_contains {a b : Box} {x y : ℝ} (ha : Contains a x) (hb : Contains b y) :
    Contains (mul a b) (x*y) := mul_certificate_sound ha hb (mul_certificate a b)

/-- This branch is used only with a positive denominator interval. -/
def divPos (a b : Box) : Box :=
  ⟨min4 (a.lo*unit/b.lo) (a.lo*unit/b.hi) (a.hi*unit/b.lo) (a.hi*unit/b.hi),
   max4 (ceilDiv (a.lo*unit) b.lo) (ceilDiv (a.lo*unit) b.hi)
     (ceilDiv (a.hi*unit) b.lo) (ceilDiv (a.hi*unit) b.hi)⟩

lemma div_lower_corner (a b : Box) (i j : Bool) :
    (divPos a b).lo≤endpt a i*unit/endpt b j := by
  cases i <;> cases j <;> simp only [endpt_false,endpt_true,divPos,min4] <;> omega
lemma div_upper_corner (a b : Box) (i j : Bool) :
    ceilDiv (endpt a i*unit) (endpt b j)≤(divPos a b).hi := by
  cases i <;> cases j <;> simp only [endpt_false,endpt_true,divPos,max4] <;> omega

theorem div_certificate (a b : Box) (hb : 0<b.lo) (horder : b.lo≤b.hi) :
    DivCertificate a b (divPos a b) := by
  refine ⟨hb,?_⟩
  intro i j
  have hd : 0<endpt b j := by cases j <;> simp only [endpt_false,endpt_true] <;> omega
  constructor
  · have h := (mul_le_mul_of_nonneg_right (div_lower_corner a b i j) hd.le).trans
      (floor_mul_le _ _ hd)
    nlinarith only [h]
  · have h := (le_ceil_mul _ _ hd).trans
      (mul_le_mul_of_nonneg_right (div_upper_corner a b i j) hd.le)
    nlinarith only [h]

theorem contains_order {a : Box} {x : ℝ} (ha : Contains a x) : a.lo≤a.hi := by
  exact_mod_cast ha.1.trans ha.2

theorem divPos_contains {a b : Box} {x y : ℝ} (ha : Contains a x) (hb : Contains b y)
    (hpos : 0<b.lo) : Contains (divPos a b) (x/y) :=
  div_certificate_sound ha hb (div_certificate a b hpos (contains_order hb))

/-- Negative denominator intervals are normalized; zero-crossing is rejected. -/
def divide (a b : Box) : Option Box :=
  if 0<b.lo then some (divPos a b)
  else if b.hi<0 then some (divPos (neg a) (neg b)) else none

theorem divide_sound {a b c : Box} {x y : ℝ} (ha : Contains a x) (hb : Contains b y)
    (hc : divide a b=some c) : Contains c (x/y) := by
  unfold divide at hc
  split_ifs at hc with hp hn
  · cases hc
    exact divPos_contains ha hb hp
  · cases hc
    have hn' : 0<(neg b).lo := by change 0< -b.hi; omega
    simpa only [neg_div_neg_eq] using divPos_contains (neg_contains ha) (neg_contains hb) hn'

def absolute (a : Box) : Box :=
  if 0≤a.lo then a else if a.hi≤0 then neg a else ⟨0,max (-a.lo) a.hi⟩

theorem absolute_contains {a : Box} {x : ℝ} (ha : Contains a x) :
    Contains (absolute a) |x| := by
  unfold absolute
  split_ifs with hp hn
  · have h0 : (0:ℝ)≤a.lo := by exact_mod_cast hp
    have hx : 0≤x := by nlinarith only [h0,ha.1,unit_pos]
    simpa only [abs_of_nonneg hx] using ha
  · have h0 : (a.hi:ℝ)≤0 := by exact_mod_cast hn
    have hx : x≤0 := by nlinarith only [h0,ha.2,unit_pos]
    simpa only [abs_of_nonpos hx] using neg_contains ha
  · apply abs_certificate_sound ha
    constructor
    · rfl
    · exact ⟨le_max_left _ _,le_max_right _ _⟩

/-- Linear power is the simple reference evaluator; fast powers are separate. -/
def power (a : Box) : ℕ→Box
  | 0 => point 1
  | n+1 => mul (power a n) a

theorem power_contains {a : Box} {x : ℝ} (ha : Contains a x) (n : ℕ) :
    Contains (power a n) (x^n) := by
  induction n with
  | zero => simpa only [power,pow_zero,Int.cast_one] using point_contains 1
  | succ n ih => simpa only [power,pow_succ] using mul_contains ih ha

end SubmittedGenus.CapFourMass.Interval
