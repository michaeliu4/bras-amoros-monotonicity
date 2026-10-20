import Results.Genus.FiniteArithmetic.BoundedReflection

namespace SubmittedGenus.FiniteArithmetic.Reflection

/-- Weakening reflection constraints enlarges the source language. -/
theorem Language.mono {P Q : ℕ → ℕ → Prop} {C D : ℕ → Prop}
    (hP : ∀ a b, P a b → Q a b) (hC : ∀ a, C a → D a)
    {w : List ℕ} (h : Language P C w) : Language Q D w := by
  induction h with
  | nil => exact Language.nil
  | singleton a ha => exact Language.singleton a (hC a ha)
  | pair a b w hab hw ih => exact Language.pair a b w (hP a b hab) ih

theorem Language.forall_letters {P : ℕ → ℕ → Prop} {C Q : ℕ → Prop}
    (hP : ∀ a b, P a b → Q a ∧ Q b) (hC : ∀ a, C a → Q a)
    {w : List ℕ} (h : Language P C w) : ∀ a ∈ w, Q a := by
  induction h with
  | nil => simp
  | singleton a ha => simpa using hC a ha
  | pair a b w hab hw ih =>
    have hp := hP a b hab
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false]
    intro x hx
    rcases hx with rfl | hx | rfl
    · exact hp.1
    · exact ih x hx
    · exact hp.2

theorem bounded_language_letters {threshold cap : ℕ} {w : List ℕ}
    (h : Language (boundedSystem threshold cap).pairAllowed
      (boundedSystem threshold cap).centerAllowed w) : ∀ a ∈ w, 1 ≤ a ∧ a ≤ cap :=
  h.forall_letters (fun _ _ hp => ⟨⟨hp.1, hp.2.1⟩, ⟨hp.2.2.1, hp.2.2.2.1⟩⟩)
    (fun _ hc => ⟨hc.1, hc.2.1⟩)

/-- Physical mirrored-coordinate inequalities imply the actual recursive
reflection language, with central self-pairs included. -/
theorem ofFn_bounded_language (threshold cap n : ℕ) (f : Fin n → ℕ)
    (hb : ∀ i, 1 ≤ f i ∧ f i ≤ cap)
    (hp : ∀ i j, i.val + j.val + 1 = n → threshold ≤ f i + f j) :
    Language (boundedSystem threshold cap).pairAllowed
      (boundedSystem threshold cap).centerAllowed (List.ofFn f) := by
  induction n using Nat.twoStepInduction with
  | zero => simpa using (Language.nil (P := (boundedSystem threshold cap).pairAllowed)
      (C := (boundedSystem threshold cap).centerAllowed))
  | one =>
    have h0 := hb 0
    have hs := hp 0 0 (by decide)
    have hc : (boundedSystem threshold cap).centerAllowed (f 0) := by
      change 1 ≤ f 0 ∧ f 0 ≤ cap ∧ threshold ≤ 2 * f 0
      omega
    simpa [List.ofFn_succ] using Language.singleton (f 0) hc
  | more n ih _ =>
    let g : Fin n → ℕ := fun i => f i.castSucc.succ
    have hg : Language (boundedSystem threshold cap).pairAllowed
        (boundedSystem threshold cap).centerAllowed (List.ofFn g) := by
      apply ih g
      · intro i
        exact hb i.castSucc.succ
      · intro i j hij
        apply hp i.castSucc.succ j.castSucc.succ
        dsimp at hij ⊢
        omega
    have h0 := hb 0
    have he := hb (Fin.last (n + 1))
    have hp' := hp 0 (Fin.last (n + 1)) (by simp)
    have hout : (boundedSystem threshold cap).pairAllowed (f 0) (f (Fin.last (n + 1))) := by
      change 1 ≤ f 0 ∧ f 0 ≤ cap ∧ 1 ≤ f (Fin.last (n + 1)) ∧
        f (Fin.last (n + 1)) ≤ cap ∧ threshold ≤ f 0 + f (Fin.last (n + 1))
      exact ⟨h0.1, h0.2, he.1, he.2, hp'⟩
    have h := Language.pair (f 0) (f (Fin.last (n + 1))) (List.ofFn g) hout hg
    rw [List.ofFn_succ, List.ofFn_succ']
    simpa [g] using h

theorem Language.sum_pos_of_nonempty {P : ℕ → ℕ → Prop} {C : ℕ → Prop}
    (hP : ∀ a b, P a b → 0 < a) (hC : ∀ a, C a → 0 < a)
    {w : List ℕ} (h : Language P C w) (hne : w ≠ []) : 0 < w.sum := by
  cases h with
  | nil => exact (hne rfl).elim
  | singleton a ha => simpa using hC a ha
  | pair a b w hab hw =>
    have := hP a b hab
    simp only [List.sum_cons, List.sum_append, List.sum_nil]
    omega

#print axioms ofFn_bounded_language

end SubmittedGenus.FiniteArithmetic.Reflection
