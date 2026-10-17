import Mathlib.Tactic

/-! Exact parity coordinates of every original pivot pair 1≤r<p. -/
namespace SubmittedGenus.CapFourMass

abbrev PositivePivot := {q : ℕ×ℕ // 1 ≤ q.1 ∧ q.1 < q.2}

structure ParityPivot where
  u : Fin 2
  v : Fin 2
  a : ℕ
  j : ℕ
  deriving DecidableEq

def parityOffset (u v : Fin 2) : ℕ := if u.val < v.val then 0 else 1

def ParityPivot.b (q : ParityPivot) : ℕ := q.a+parityOffset q.u q.v+q.j
def ParityPivot.r (q : ParityPivot) : ℕ := 2*q.a+(q.u.val+1)
def ParityPivot.p (q : ParityPivot) : ℕ := 2*q.b+(q.v.val+1)

lemma parityOffset_le (u v : Fin 2) : parityOffset u v ≤ u.val+1 := by
  unfold parityOffset
  split_ifs <;> omega

lemma parity_order_iff (u v : Fin 2) (a b : ℕ) :
    2*a+(u.val+1) < 2*b+(v.val+1) ↔ a+parityOffset u v ≤ b := by
  have hu := u.isLt
  have hv := v.isLt
  unfold parityOffset
  split_ifs <;> omega

def ParityPivot.toPivot (q : ParityPivot) : PositivePivot :=
  ⟨(q.r,q.p), by
    constructor
    · unfold ParityPivot.r; omega
    · unfold ParityPivot.r ParityPivot.p
      rw [parity_order_iff]
      unfold ParityPivot.b
      omega⟩

lemma parity_toPivot_injective : Function.Injective ParityPivot.toPivot := by
  intro x y he
  have hr := congrArg (fun q : PositivePivot => q.val.1) he
  have hp := congrArg (fun q : PositivePivot => q.val.2) he
  change x.r=y.r at hr
  change x.p=y.p at hp
  have hxu := x.u.isLt
  have hyu := y.u.isLt
  have hxv := x.v.isLt
  have hyv := y.v.isLt
  have hu : x.u=y.u := by
    apply Fin.ext
    dsimp [ParityPivot.r] at hr
    omega
  have ha : x.a=y.a := by
    dsimp [ParityPivot.r] at hr
    omega
  have hv : x.v=y.v := by
    apply Fin.ext
    dsimp [ParityPivot.p] at hp
    omega
  have hj : x.j=y.j := by
    dsimp [ParityPivot.p,ParityPivot.b] at hp
    rw [hu,hv,ha] at hp
    omega
  cases x
  cases y
  simp_all

lemma parity_toPivot_surjective : Function.Surjective ParityPivot.toPivot := by
  intro q
  let u : Fin 2 := ⟨(q.val.1-1)%2, Nat.mod_lt _ (by decide)⟩
  let v : Fin 2 := ⟨(q.val.2-1)%2, Nat.mod_lt _ (by decide)⟩
  let a := (q.val.1-1)/2
  let b := (q.val.2-1)/2
  have hr : 2*a+(u.val+1)=q.val.1 := by
    have hq := q.property.1
    dsimp [a,u]
    omega
  have hp : 2*b+(v.val+1)=q.val.2 := by
    have hq := q.property
    dsimp [b,v]
    omega
  have hab : a+parityOffset u v ≤ b := by
    apply (parity_order_iff u v a b).mp
    rw [hr,hp]
    exact q.property.2
  refine ⟨⟨u,v,a,b-(a+parityOffset u v)⟩, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · exact hr
  · change 2*(a+parityOffset u v+(b-(a+parityOffset u v)))+(v.val+1)=q.val.2
    rw [Nat.add_sub_of_le hab]
    exact hp

/-- Exact coverage and unique ownership of all pivot pairs by parity rows. -/
noncomputable def parityPivotEquiv : ParityPivot ≃ PositivePivot :=
  Equiv.ofBijective ParityPivot.toPivot ⟨parity_toPivot_injective,parity_toPivot_surjective⟩

lemma parity_gap (q : ParityPivot) :
    q.p-q.r = 2*(q.b-q.a)+q.v.val-q.u.val := by
  have h := q.toPivot.property.2
  dsimp [ParityPivot.toPivot,ParityPivot.r,ParityPivot.p,ParityPivot.b] at *
  unfold parityOffset at *
  split_ifs at * <;> have hu := q.u.isLt <;> have hv := q.v.isLt <;> omega

end SubmittedGenus.CapFourMass
