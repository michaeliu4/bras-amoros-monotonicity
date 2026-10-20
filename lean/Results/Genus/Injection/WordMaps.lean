import Results.Genus.Kunz
import Mathlib.Tactic

/-!
# The submitted elementary word maps

The append maps here are the original low-depth append-1/append-2 maps in
`cmb:elementary-maps`. Their output is proved Kunz-valid at the changed
multiplicity. Genus is subsequently transported through the genuine
semigroup/weight equivalence; this file does not replace that equivalence.
-/

namespace SubmittedGenus.KunzWord

/-- Append one positive letter, increasing multiplicity from `m` to `m+1`. -/
def append {m : ℕ} (x : KunzWord m) (a : ℕ) : KunzWord (m + 1) :=
  fun i => if h : i.val < m - 1 then x ⟨i.val, h⟩ else a

@[simp] theorem coord_append_old {m i a : ℕ} (x : KunzWord m)
    (hi0 : 0 < i) (him : i < m) :
    coord (append x a) i = coord x i := by
  have hinew : i < m + 1 := by omega
  have hind : i - 1 < m - 1 := by omega
  simp [coord, hi0, him, hinew, append, hind]

@[simp] theorem coord_append_last {m a : ℕ} (x : KunzWord m) (hm : 0 < m) :
    coord (append x a) m = a := by
  simp [coord, hm, append]

/-- A uniform bound on letters also bounds the zero-extended coordinates. -/
theorem coord_le_of_bound {m k : ℕ} {x : KunzWord m}
    (hbound : ∀ i, x i ≤ k) (j : ℕ) : coord x j ≤ k := by
  unfold coord
  split_ifs with h
  · exact hbound _
  · omega

theorem append_bounded {m k a : ℕ} {x : KunzWord m}
    (hbound : ∀ i, x i ≤ k) (ha : a ≤ k) : ∀ i, append x a i ≤ k := by
  intro i
  unfold append
  split_ifs with h
  · exact hbound _
  · exact ha

/-- The validity argument explicitly accounts for the changed modulus. -/
theorem Valid.append_low_depth {m a : ℕ} {x : KunzWord m}
    (hx : Valid x) (hm : 0 < m) (hdepth : ∀ i, x i ≤ 3)
    (ha0 : 0 < a) (ha2 : a ≤ 2) : Valid (append x a) where
  positive := by
    intro i
    unfold append
    split_ifs with h
    · exact hx.positive _
    · exact ha0
  noncarry := by
    intro i j hi0 him hj0 hjm hij
    have hiold : i < m := by omega
    have hjold : j < m := by omega
    rw [coord_append_old x hi0 hiold, coord_append_old x hj0 hjold]
    by_cases hsum : i + j < m
    · rw [coord_append_old x (by omega) hsum]
      exact hx.noncarry i j hi0 hiold hj0 hjold hsum
    · have heq : i + j = m := by omega
      rw [heq, coord_append_last x hm]
      have hpi := hx.coord_pos hi0 hiold
      have hpj := hx.coord_pos hj0 hjold
      omega
  carry := by
    intro i j hi0 him hj0 hjm hij
    have hpos : ∀ k, 0 < append x a k := by
      intro k
      unfold append
      split_ifs with h
      · exact hx.positive _
      · exact ha0
    have hpi : 0 < coord (append x a) i := by
      simp only [coord, dif_pos (show 0 < i ∧ i < m + 1 from ⟨hi0, him⟩)]
      exact hpos _
    have hpj : 0 < coord (append x a) j := by
      simp only [coord, dif_pos (show 0 < j ∧ j < m + 1 from ⟨hj0, hjm⟩)]
      exact hpos _
    have htarget := coord_le_of_bound (append_bounded hdepth (by omega : a ≤ 3))
      (i + j - (m + 1))
    omega

/-- The original word is recoverable without knowing its appended letter. -/
theorem append_injective {m a : ℕ} :
    Function.Injective (fun x : KunzWord m => append x a) := by
  intro x y h
  funext i
  have hj : i.val < m := by omega
  have hv := congrFun h (⟨i.val, by omega⟩ : Fin ((m + 1) - 1))
  simpa [append, i.isLt] using hv

/-- The first two elementary image sectors are distinguished by their final
letter, even when their old words have different letter values. -/
theorem append_ne_of_last_ne {m a b : ℕ} {x y : KunzWord m}
    (hm : 0 < m) (hab : a ≠ b) : append x a ≠ append y b := by
  intro h
  have hv := congrArg (fun w : KunzWord (m + 1) => coord w m) h
  simp only [coord_append_last _ hm] at hv
  exact hab hv

/-- Appending a letter raises the word weight by that letter exactly. -/
theorem weight_append {m a : ℕ} (x : KunzWord m) (hm : 0 < m) :
    weight (append x a) = weight x + a := by
  cases m with
  | zero => omega
  | succ n =>
    change (∑ i : Fin (n + 1), append x a i) = (∑ i : Fin n, x i) + a
    rw [Fin.sum_univ_castSucc]
    simp [append]

/-- Binary words satisfy every Kunz inequality, including self-pairs. -/
theorem valid_of_binary {m : ℕ} {x : KunzWord m}
    (hbinary : ∀ i, x i = 1 ∨ x i = 2) : Valid x := by
  have hpositive : ∀ i, 0 < x i := by
    intro i
    rcases hbinary i with h | h <;> omega
  have hbound : ∀ i, x i ≤ 2 := by
    intro i
    rcases hbinary i with h | h <;> omega
  have hcoordpos : ∀ i, 0 < i → i < m → 0 < coord x i := by
    intro i hi0 him
    simp only [coord, dif_pos (show 0 < i ∧ i < m from ⟨hi0, him⟩)]
    exact hpositive _
  refine ⟨hpositive, ?_, ?_⟩
  · intro i j hi0 him hj0 hjm hij
    have hi := hcoordpos i hi0 him
    have hj := hcoordpos j hj0 hjm
    have ht := coord_le_of_bound hbound (i + j)
    omega
  · intro i j hi0 him hj0 hjm hij
    have hi := hcoordpos i hi0 him
    have hj := hcoordpos j hj0 hjm
    have ht := coord_le_of_bound hbound (i + j - m)
    omega

end SubmittedGenus.KunzWord
