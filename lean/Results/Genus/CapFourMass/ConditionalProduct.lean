import Results.Genus.CapFourMass.LocalWeights

namespace SubmittedGenus.CapFourMass.ConditionalProduct
open scoped BigOperators
noncomputable section

variable {Ω : Type*}

def mass (w : Ω → ℝ) (A : Finset Ω) := ∑ x ∈ A, w x

def survivors (A : Finset Ω) (F : ℕ → Ω → Prop) [∀ n, DecidablePred (F n)]
    (n : ℕ) : Finset Ω := A.filter (fun x => ∀ i < n, ¬ F i x)

@[simp] theorem survivors_zero (A : Finset Ω) (F : ℕ → Ω → Prop)
    [∀ n, DecidablePred (F n)] : survivors A F 0 = A := by simp [survivors]

theorem survivors_succ (A : Finset Ω) (F : ℕ → Ω → Prop)
    [∀ n, DecidablePred (F n)] (n : ℕ) :
    survivors A F (n+1) = (survivors A F n).filter (fun x => ¬ F n x) := by
  ext x
  simp only [survivors, Finset.mem_filter]
  constructor
  · rintro ⟨hx,h⟩
    exact ⟨⟨hx,fun i hi => h i (by omega)⟩,h n (by omega)⟩
  · rintro ⟨⟨hx,h⟩,hn⟩
    refine ⟨hx,fun i hi => ?_⟩
    by_cases he : i = n
    · simpa [he] using hn
    · exact h i (by omega)

theorem mass_nonneg (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (A : Finset Ω) :
    0 ≤ mass w A := Finset.sum_nonneg (fun x _ => hw x)

/-- A failure lower bound gives the survivor bound without division, so zero
conditioning mass is included. -/
theorem survivor_step (w : Ω → ℝ) (A : Finset Ω) (F : Ω → Prop)
    [DecidablePred F] (e : ℝ) (he : e*mass w A ≤ mass w (A.filter F)) :
    mass w (A.filter (fun x => ¬ F x)) ≤ (1-e)*mass w A := by
  have hpart := Finset.sum_filter_add_sum_filter_not A F w
  change mass w (A.filter F) + mass w (A.filter (fun x => ¬ F x)) = mass w A at hpart
  nlinarith only [he,hpart]

/-- Conditional survival bounds multiply along the actual preceding avoidance
sets. No measurability-outside-gadget premise is introduced. -/
theorem survivor_product (w : Ω → ℝ) (A : Finset Ω) (F : ℕ → Ω → Prop)
    [∀ n, DecidablePred (F n)] (e : ℕ → ℝ) (N : ℕ)
    (hrate : ∀ n < N, 0 ≤ 1-e n)
    (hfailure : ∀ n < N,
      e n * mass w (survivors A F n) ≤
        mass w ((survivors A F n).filter (F n))) :
    mass w (survivors A F N) ≤ (∏ n ∈ Finset.range N, (1-e n))*mass w A := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hprev := ih (fun n hn => hrate n (by omega))
      (fun n hn => hfailure n (by omega))
    have hstep := survivor_step w (survivors A F N) (F N) (e N)
      (hfailure N (by omega))
    rw [survivors_succ]
    calc
      mass w ((survivors A F N).filter (fun x => ¬F N x)) ≤
          (1-e N)*mass w (survivors A F N) := hstep
      _ ≤ (1-e N)*((∏ n ∈ Finset.range N, (1-e n))*mass w A) :=
        mul_le_mul_of_nonneg_left hprev (hrate N (by omega))
      _ = (∏ n ∈ Finset.range (N+1), (1-e n))*mass w A := by
        rw [Finset.prod_range_succ]
        ring

theorem two_rate_product (P : Finset ℕ) (N : ℕ) (hP : P ⊆ Finset.range N)
    (beta gamma : ℝ) :
    (∏ n ∈ Finset.range N, if n ∈ P then gamma else beta) =
      beta^(N-P.card)*gamma^P.card := by
  rw [Finset.prod_ite]
  have hp : (Finset.range N).filter (fun n => n ∈ P) = P := by
    ext n
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2,fun h => ⟨hP h,h⟩⟩
  have hn : (Finset.range N).filter (fun n => n ∉ P) = Finset.range N \ P := by
    ext n
    simp
  rw [hp, hn, Finset.prod_const, Finset.prod_const,
    Finset.card_sdiff_of_subset hP, Finset.card_range]
  exact mul_comm _ _

theorem two_rate_bound (P : Finset ℕ) (N K : ℕ) (hP : P ⊆ Finset.range N)
    (hK : P.card ≤ K) (beta gamma : ℝ) (hb : 0 < beta) (hbg : beta ≤ gamma) :
    (∏ n ∈ Finset.range N, if n ∈ P then gamma else beta) ≤
      beta^N*(gamma/beta)^K := by
  rw [two_rate_product P N hP]
  have hf : P.card ≤ N := by simpa using Finset.card_le_card hP
  have hratio : 1 ≤ gamma/beta := (le_div_iff₀ hb).mpr (by simpa using hbg)
  have heq : beta^(N-P.card)*gamma^P.card = beta^N*(gamma/beta)^P.card := by
    calc
      beta^(N-P.card)*gamma^P.card =
          beta^(N-P.card)*(beta*(gamma/beta))^P.card := by
            rw [mul_div_cancel₀ _ (ne_of_gt hb)]
      _ = beta^N*(gamma/beta)^P.card := by
        rw [mul_pow, ←mul_assoc, ←pow_add, Nat.sub_add_cancel hf]
  rw [heq]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hratio hK) (by positivity)

/-- The exact feedback-set exponent in the submitted contraction argument,
conditional only on the actual preceding-slice failure bounds and a bounded
postponed set. Zero-mass prefixes are handled without dividing by mass. -/
theorem feedback_product (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x)
    (A : Finset Ω) (F : ℕ → Ω → Prop) [∀ n, DecidablePred (F n)]
    (P : Finset ℕ) (N K : ℕ) (hP : P ⊆ Finset.range N) (hK : P.card ≤ K)
    (eps del : ℝ) (_hdel : 0 ≤ del) (hde : del ≤ eps) (he : eps < 1)
    (hfailure : ∀ n < N,
      (if n ∈ P then del else eps)*mass w (survivors A F n) ≤
        mass w ((survivors A F n).filter (F n))) :
    mass w (survivors A F N) ≤
      (1-eps)^N*((1-del)/(1-eps))^K*mass w A := by
  have hrate : ∀ n < N, 0 ≤ 1-(if n ∈ P then del else eps) := by
    intro n hn
    split_ifs <;> linarith
  have hh := survivor_product w A F (fun n => if n ∈ P then del else eps) N
    hrate hfailure
  have heq : (∏ n ∈ Finset.range N, (1-(if n ∈ P then del else eps))) =
      ∏ n ∈ Finset.range N, if n ∈ P then 1-del else 1-eps := by
    apply Finset.prod_congr rfl
    intro n hn
    split_ifs <;> rfl
  rw [heq] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right
    (two_rate_bound P N K hP hK (1-eps) (1-del) (by linarith) (by linarith))
    (mass_nonneg w hw A))

end
end SubmittedGenus.CapFourMass.ConditionalProduct
