import Results.Genus.CapFourMass.IntervalCompute

/-! A two-corner specialization for nonnegative interval endpoints. The signed
four-corner checker remains available whenever either input can be negative. -/
namespace SubmittedGenus.CapFourMass.Interval

def nonnegativeMul (a b : Box) : Box :=
  ⟨a.lo*b.lo/unit,ceilDiv (a.hi*b.hi) unit⟩

theorem nonnegativeMul_certificate (a b : Box) (ha : 0≤a.lo) (hb : 0≤b.lo)
    (hao : a.lo≤a.hi) (hbo : b.lo≤b.hi) : MulCertificate a b (nonnegativeMul a b) := by
  intro i j
  have hai : a.lo≤endpt a i := by cases i <;> simp [endpt,hao]
  have hbi : b.lo≤endpt b j := by cases j <;> simp [endpt,hbo]
  have hia : endpt a i≤a.hi := by cases i <;> simp [endpt,hao]
  have hib : endpt b j≤b.hi := by cases j <;> simp [endpt,hbo]
  constructor
  · exact (floor_mul_le _ _ unit_int_pos).trans
      (mul_le_mul hai hbi hb (ha.trans hai))
  · exact (mul_le_mul hia hib (hb.trans hbi) (ha.trans hao)).trans
      (le_ceil_mul _ _ unit_int_pos)

theorem nonnegativeMul_contains {a b : Box} {x y : ℝ}
    (ha : Contains a x) (hb : Contains b y) (ha0 : 0≤a.lo) (hb0 : 0≤b.lo) :
    Contains (nonnegativeMul a b) (x*y) :=
  mul_certificate_sound ha hb
    (nonnegativeMul_certificate a b ha0 hb0 (contains_order ha) (contains_order hb))

end SubmittedGenus.CapFourMass.Interval
