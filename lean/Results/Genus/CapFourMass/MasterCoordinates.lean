import Results.Genus.CapFourMass.GenuineSource
import Results.Genus.CapFourMass.ShortOmittedSource

/-! Exact parity-and-multiplicity coordinates of every genuine-source master
parameter. The short/long partition is a literal split of the final Nat index. -/
noncomputable section
open scoped BigOperators
namespace SubmittedGenus.CapFourMass
open GenuineSource

def tailParityEquiv : TailIndex ≃ ParityPivot where
  toFun := TailIndex.pivot
  invFun q := ((q.u,q.v),(q.a,q.j))
  left_inv i := by rcases i with ⟨⟨u,v⟩,a,j⟩; rfl
  right_inv q := by cases q; rfl

def tailPivotEquiv : TailIndex ≃ PositivePivot := tailParityEquiv.trans parityPivotEquiv

def indexedParameters (ij : TailIndex×ℕ) : PivotParameters :=
  ⟨ij.1.pivot.p+1+ij.2,ij.1.pivot.r,ij.1.pivot.p,
    parity_parameters ij.1.pivot _ (by omega)⟩

def parameterPivot (q : PivotParameters) : PositivePivot :=
  ⟨(q.r,q.p),q.valid.1,q.valid.2.1⟩

/-- Every valid triple occurs once, with m=p+1+j. -/
def masterEquiv : (TailIndex×ℕ) ≃ PivotParameters where
  toFun := indexedParameters
  invFun q := (tailPivotEquiv.symm (parameterPivot q),q.m-q.p-1)
  left_inv ij := by
    rcases ij with ⟨i,j⟩
    apply Prod.ext
    · change tailPivotEquiv.symm (tailPivotEquiv i)=i
      exact tailPivotEquiv.symm_apply_apply i
    · change (i.pivot.p+1+j)-i.pivot.p-1=j
      omega
  right_inv q := by
    have he:=tailPivotEquiv.apply_symm_apply (parameterPivot q)
    have hr:=congrArg (fun a : PositivePivot => a.val.1) he
    have hp:=congrArg (fun a : PositivePivot => a.val.2) he
    apply PivotParameters.ext
    · change (tailPivotEquiv.symm (parameterPivot q)).pivot.p+1+(q.m-q.p-1)=q.m
      change (tailPivotEquiv.symm (parameterPivot q)).pivot.p=q.p at hp
      have hm:=q.valid.2.2.1
      rw [hp]
      omega
    · exact hr
    · exact hp

lemma masterEquiv_m (i : TailIndex) (j : ℕ) : (masterEquiv (i,j)).m=i.pivot.p+1+j := rfl
lemma masterEquiv_r (i : TailIndex) (j : ℕ) : (masterEquiv (i,j)).r=i.pivot.r := rfl
lemma masterEquiv_p (i : TailIndex) (j : ℕ) : (masterEquiv (i,j)).p=i.pivot.p := rfl

lemma masterEquiv_short_iff (i : TailIndex) (j : ℕ) :
    (masterEquiv (i,j)).m≤2*(masterEquiv (i,j)).p ↔ j < i.pivot.p := by
  rw [masterEquiv_m,masterEquiv_p]
  omega
lemma masterEquiv_long_iff (i : TailIndex) (j : ℕ) :
    2*(masterEquiv (i,j)).p<(masterEquiv (i,j)).m ↔ i.pivot.p ≤ j := by
  rw [masterEquiv_m,masterEquiv_p]
  omega

lemma master_summable_iff (f : PivotParameters→ℝ) :
    Summable (fun ij : TailIndex×ℕ => f (masterEquiv ij)) ↔ Summable f :=
  masterEquiv.summable_iff

lemma master_tsum_eq (f : PivotParameters→ℝ) :
    (∑' ij : TailIndex×ℕ,f (masterEquiv ij))=∑' q : PivotParameters,f q :=
  masterEquiv.tsum_eq f

end SubmittedGenus.CapFourMass
