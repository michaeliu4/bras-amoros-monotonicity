import Results.Genus.CapFourMass.SourceSymmetric
import Results.Genus.FixedPivot.CanonicalEndpoints

/-! Exact symmetric port factors for each signed source mode. -/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFourMass
open FixedPivot

lemma modeVector_eigen (j : Mode) : carryMatrix *ᵥ modeVector j=fun i => modeRoot j*modeVector j i := by
  fin_cases j
  · simpa [modeVector,modeRoot] using qplus_eigen
  · simpa [modeVector,modeRoot] using qminus_eigen

lemma sourceHalf_carry_row (i : Fin 3) (k : State) :
    halfWeight i.castSucc*sourceHalf (fun j : Fin 3 => if 3≤(i.val+1)+(j.val+1) then 1 else 0) k=
      carryMatrix i.castSucc k := by
  fin_cases i <;> fin_cases k <;>
    norm_num [sourceHalf,embedCarry,halfScale,carryMatrix,transfer,gate,Fin.castSucc,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] <;> ring

/-- The carry edge at a surviving port contributes exactly one eigenvalue;
the half-weight is removed only after the actual source identity is proved. -/
lemma source_port_mode (i : Fin 3) (j : Mode) :
    halfWeight i.castSucc*
      (sourceHalf (fun k : Fin 3 => if 3≤(i.val+1)+(k.val+1) then 1 else 0) ⬝ᵥ modeVector j)=
      modeRoot j*modeVector j i.castSucc := by
  have he:=congrFun (modeVector_eigen j) i.castSucc
  rw [← he]
  unfold dotProduct Matrix.mulVec
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [← mul_assoc,sourceHalf_carry_row]

lemma sourceHalf_free : sourceHalf (fun _ : Fin 3 => (1:ℝ))=freeBoundary := by
  rfl
lemma sourceHalf_loop : sourceHalf (fun v : Fin 3 => if 2≤v.val+1 then (1:ℝ) else 0)=loopBoundary := by
  funext i
  fin_cases i <;> norm_num [sourceHalf,embedCarry,halfScale,loopBoundary]

/-- The removed pivot leaves the manuscript's free endpoint; every other
actual port is the exact eigenvector factor at its physical core value. -/
theorem canonical_port_mode {r d : ℕ} (hd : 0<d) (x : Fin (r+d)→Fin 5)
    (hx : StableCoreAllowed r (r+d) x) (a : Fin d) (j : Mode) :
    sourceHalf (fun v : Fin 3 => if canonicalPortAllowed x a (v.val+1) then 1 else 0) ⬝ᵥ modeVector j=
      if a=pivotPort d hd then freeBoundary ⬝ᵥ modeVector j else
        modeRoot j*modeVector j (canonicalPortState x a).castSucc/halfWeight (canonicalPortState x a).castSucc := by
  by_cases ha : a.val+1=d
  · simp only [canonicalPortAllowed,ha,true_or,if_true,if_pos ((eq_pivotPort_iff hd a).mpr ha),sourceHalf_free]
  · rw [if_neg (fun h => ha ((eq_pivotPort_iff hd a).mp h))]
    have hfun : (fun v : Fin 3 => if canonicalPortAllowed x a (v.val+1) then (1:ℝ) else 0)=
        fun v : Fin 3 => if 3≤((canonicalPortState x a).val+1)+(v.val+1) then 1 else 0 := by
      funext v
      simp only [canonicalPortAllowed,ha,false_or,canonicalPortState_value x hx a ha]
    rw [hfun]
    apply (eq_div_iff (ne_of_gt (halfWeight_pos _))).mpr
    simpa only [mul_comm] using source_port_mode (canonicalPortState x a) j

end SubmittedGenus.CapFourMass
