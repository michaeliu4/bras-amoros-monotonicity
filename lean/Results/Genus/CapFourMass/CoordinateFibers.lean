import Results.Genus.CapFourMass.FiberComparison

namespace SubmittedGenus.CapFourMass.CoordinateFibers
open scoped BigOperators
noncomputable section

variable {V S : Type*} [Fintype V] [Fintype S] [DecidableEq V]
variable (inside : V → Prop) [DecidablePred inside]

abbrev Inner := {v : V // inside v} → S
abbrev Outer := {v : V // ¬inside v} → S

def join (g : Inner (S := S) inside) (e : Outer (S := S) inside) : V → S :=
  (Equiv.piEquivPiSubtypeProd inside (fun _ => S)).symm (g,e)

omit [Fintype V] [Fintype S] [DecidableEq V] in
@[simp] theorem join_inside (g : Inner (S := S) inside) (e : Outer (S := S) inside)
    (v : V) (hv : inside v) : join inside g e v = g ⟨v,hv⟩ := by
  simp [join, Equiv.piEquivPiSubtypeProd, hv]

omit [Fintype V] [Fintype S] [DecidableEq V] in
@[simp] theorem join_outside (g : Inner (S := S) inside) (e : Outer (S := S) inside)
    (v : V) (hv : ¬inside v) : join inside g e v = e ⟨v,hv⟩ := by
  simp [join, Equiv.piEquivPiSubtypeProd, hv]

/-- Each physical coordinate contributes exactly one weight, on the inside
or the exterior, under the genuine function-space equivalence. -/
theorem weight_split (w : V → S → ℝ) (g : Inner (S := S) inside) (e : Outer (S := S) inside) :
    (∏ v, w v (join inside g e v)) =
      (∏ v : {v // ¬inside v}, w v (e v)) *
      (∏ v : {v // inside v}, w v (g v)) := by
  calc
    (∏ v, w v (join inside g e v)) =
        (∏ v : {v // inside v}, w v (join inside g e v)) *
        (∏ v : {v // ¬inside v}, w v (join inside g e v)) :=
      (Fintype.prod_subtype_mul_prod_subtype inside
        (fun v => w v (join inside g e v))).symm
    _ = _ := by
      have hgi : (∏ v : {v // inside v}, w v (join inside g e v)) =
          ∏ v : {v // inside v}, w v (g v) := by
        apply Finset.prod_congr rfl
        intro v hv
        rw [join_inside inside g e v.val v.property]
      have hge : (∏ v : {v // ¬inside v}, w v (join inside g e v)) =
          ∏ v : {v // ¬inside v}, w v (e v) := by
        apply Finset.prod_congr rfl
        intro v hv
        rw [join_outside inside g e v.val v.property]
      rw [hgi,hge]
      exact mul_comm _ _

/-- Exact exterior-slice decomposition of any finite weighted word population. -/
theorem partition_split (w : V → S → ℝ) (P : (V → S) → Prop) [DecidablePred P] :
    (∑ x : V → S, if P x then ∏ v, w v (x v) else 0) =
    ∑ e : Outer (S := S) inside, (∏ v : {v // ¬inside v}, w v (e v)) *
      (∑ g : Inner (S := S) inside, if P (join inside g e) then
        ∏ v : {v // inside v}, w v (g v) else 0) := by
  classical
  let q := Equiv.piEquivPiSubtypeProd inside (fun _ => S)
  have h := Fintype.sum_equiv q
    (fun x : V → S => if P x then ∏ v, w v (x v) else 0)
    (fun ge : Inner (S := S) inside × Outer (S := S) inside =>
      if P (join inside ge.1 ge.2) then
        (∏ v : {v // ¬inside v}, w v (ge.2 v)) *
        (∏ v : {v // inside v}, w v (ge.1 v)) else 0) ?_
  · rw [h, Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e he
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro g hg
    split_ifs <;> simp
  · intro x
    have hj : join inside (q x).1 (q x).2 = x := q.symm_apply_apply x
    have hw := weight_split inside w (q x).1 (q x).2
    rw [hj] at hw
    rw [hj]
    split_ifs
    · exact hw
    · rfl

end
end SubmittedGenus.CapFourMass.CoordinateFibers
