import Results.Genus.CapFourMass.IntervalExpression
import Results.Genus.CapFourMass.FiniteStrip

open scoped BigOperators
namespace SubmittedGenus.CapFourMass.Interval

namespace Expr

def rangeSum (f : ℕ → Expr) : ℕ → Expr
  | 0 => .integer 0
  | n+1 => .add (rangeSum f n) (f n)

theorem rangeSum_real (xs : ℕ → ℝ) (f : ℕ → Expr) (n : ℕ) :
    (rangeSum f n).real xs = ∑ j ∈ Finset.range n, (f j).real xs := by
  induction n with
  | zero => simp [rangeSum,real]
  | succ n ih => simp only [rangeSum,real,ih,Finset.sum_range_succ]

def geometric (B : Expr) (k : ℕ) : Expr :=
  .div (.sub (.integer 1) (.pow B k)) (.sub (.integer 1) B)

def strip (B s : Expr) (n k : ℕ) : Expr :=
  .add (geometric B (min k (n+1)))
    (.mul (.mul (.pow B (n+1)) s) (geometric (.mul B s) (k-(n+1))))

def parityRow (A B s : Expr) (u h a k : ℕ) : Expr :=
  .mul (.mul (.pow B h) (.pow (.mul A B) a)) (strip B s (a+u-h) k)

def parityFull (A B s : Expr) (u h : ℕ) : Expr :=
  .add
    (.sub
      (.div (.pow B h) (.mul (.sub (.integer 1) B) (.sub (.integer 1) (.mul A B))))
      (.div (.pow B (u+1)) (.mul (.sub (.integer 1) B)
        (.sub (.integer 1) (.mul A (.pow B 2))))))
    (.div (.mul (.pow B (u+1)) s)
      (.mul (.sub (.integer 1) (.mul B s)) (.sub (.integer 1) (.mul A (.pow B 2)))))

/-- Exactly the original omitted two-index parity sum, via its proved row rewrite. -/
def parityTail (A B s : Expr) (P u v h : ℕ) : Expr :=
  .sub (parityFull A B s u h)
    (rangeSum (fun a => parityRow A B s u h a (parityRowCut P v h a)) (P+1))

@[simp] theorem geometric_real (xs : ℕ → ℝ) (B : Expr) (k : ℕ) :
    (geometric B k).real xs = geometricPrefix (B.real xs) k := by
  simp [geometric,real,geometricPrefix]
@[simp] theorem strip_real (xs : ℕ → ℝ) (B s : Expr) (n k : ℕ) :
    (strip B s n k).real xs = stripPrefix (B.real xs) (s.real xs) n k := by
  simp [strip,real,stripPrefix]
@[simp] theorem parityRow_real (xs : ℕ → ℝ) (A B s : Expr) (u h a k : ℕ) :
    (parityRow A B s u h a k).real xs =
      parityRowPrefix (A.real xs) (B.real xs) (s.real xs) u h a k := by
  simp [parityRow,real,parityRowPrefix]
@[simp] theorem parityFull_real (xs : ℕ → ℝ) (A B s : Expr) (u h : ℕ) :
    (parityFull A B s u h).real xs =
      parityRational (A.real xs) (B.real xs) (s.real xs) u h := by
  simp [parityFull,real,parityRational]

theorem parityTail_real (xs : ℕ → ℝ) (A B s : Expr)
    (hB : B.real xs≠1) (hBs : B.real xs*s.real xs≠1)
    (P u v h : ℕ) (hhu : h≤u) :
    (parityTail A B s P u v h).real xs =
      omittedParityRational (A.real xs) (B.real xs) (s.real xs) P u v h := by
  rw [omittedParityRational_rows _ _ _ hB hBs P u v h hhu]
  simp only [parityTail,real,parityFull_real,rangeSum_real,parityRow_real]

end Expr

/-- A successful integer computation encloses the actual omitted source sum. -/
theorem parityTail_sound (A B s : Expr) {bs : ℕ → Box} {xs : ℕ → ℝ}
    (hi : ∀ i, Contains (bs i) (xs i)) (hB : B.real xs≠1)
    (hBs : B.real xs*s.real xs≠1) (P u v h : ℕ) (hhu : h≤u)
    {b : Box} (he : (Expr.parityTail A B s P u v h).eval bs=some b) :
    Contains b (omittedParityRational (A.real xs) (B.real xs) (s.real xs) P u v h) := by
  rw [←Expr.parityTail_real xs A B s hB hBs P u v h hhu]
  exact Expr.eval_sound _ hi he

end SubmittedGenus.CapFourMass.Interval
