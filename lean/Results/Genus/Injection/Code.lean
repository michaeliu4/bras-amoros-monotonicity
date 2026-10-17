import Mathlib.Data.List.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic

/-!
# The submitted final-one binary code

This is the exact block map `2 ↦ 11`, `3 ↦ 21`, `4 ↦ 22` from
`cmb:code`, followed by a final `2`. The proofs below establish its
literal inverse, binary range, and weight increase relative to the source
word ending in `1`. Validity as a genuine semigroup is separately provided
by the binary-word Kunz theorem.
-/

namespace SubmittedGenus.BinaryCode

/-- Domain alphabet of the prefix before the sole final `1`. -/
def Prefix (w : List ℕ) : Prop := ∀ a ∈ w, a = 2 ∨ a = 3 ∨ a = 4

def letter (a : ℕ) : List ℕ :=
  if a = 2 then [1, 1] else if a = 3 then [2, 1] else [2, 2]

def encode : List ℕ → List ℕ
  | [] => []
  | a :: w => letter a ++ encode w

/-- Pairwise decoding; invalid blocks are immaterial to the left inverse. -/
def decode : List ℕ → List ℕ
  | 1 :: 1 :: w => 2 :: decode w
  | 2 :: 1 :: w => 3 :: decode w
  | 2 :: 2 :: w => 4 :: decode w
  | _ => []

def target (w : List ℕ) : List ℕ := encode w ++ [2]

theorem decode_encode {w : List ℕ} (hw : Prefix w) : decode (encode w) = w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    have ha := hw a (by simp)
    have htail : Prefix w := fun b hb => hw b (by simp [hb])
    rcases ha with rfl | rfl | rfl <;>
      simp [encode, letter, decode, ih htail]

theorem encode_injective_on_prefix {w v : List ℕ} (hw : Prefix w) (hv : Prefix v)
    (h : encode w = encode v) : w = v := by
  rw [← decode_encode hw, ← decode_encode hv, h]

/-- Appending the fixed final `2` does not lose the decoding information. -/
theorem target_injective_on_prefix {w v : List ℕ} (hw : Prefix w) (hv : Prefix v)
    (h : target w = target v) : w = v := by
  exact encode_injective_on_prefix hw hv (List.append_cancel_right h)

theorem sum_letter {a : ℕ} (ha : a = 2 ∨ a = 3 ∨ a = 4) : (letter a).sum = a := by
  rcases ha with rfl | rfl | rfl <;> decide

theorem sum_encode {w : List ℕ} (hw : Prefix w) : (encode w).sum = w.sum := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    have ha := hw a (by simp)
    have htail : Prefix w := fun b hb => hw b (by simp [hb])
    simp only [encode, List.sum_append, List.sum_cons, sum_letter ha, ih htail]

/-- Every block has two letters, making the inverse's alignment intrinsic. -/
theorem length_encode (w : List ℕ) : (encode w).length = 2 * w.length := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    have hl : (letter a).length = 2 := by
      unfold letter
      split_ifs <;> rfl
    simp only [encode, List.length_append, List.length_cons, hl, ih]
    omega

theorem letter_binary (a b : ℕ) (hb : b ∈ letter a) : b = 1 ∨ b = 2 := by
  unfold letter at hb
  split_ifs at hb <;> simp_all <;> tauto

theorem encode_binary (w : List ℕ) : ∀ b ∈ encode w, b = 1 ∨ b = 2 := by
  induction w with
  | nil => simp [encode]
  | cons a w ih =>
    intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact letter_binary a b hb
    · exact ih b hb

/-- The code image is binary, including its appended final `2`. -/
theorem target_binary (w : List ℕ) : ∀ b ∈ target w, b = 1 ∨ b = 2 := by
  intro b hb
  rcases List.mem_append.mp hb with hb | hb
  · exact encode_binary w b hb
  · simp_all

/-- Replacing the source's final `1` by the target's final `2` raises weight
by exactly one; all earlier blocks preserve weight. -/
theorem target_weight {w : List ℕ} (hw : Prefix w) :
    (target w).sum = (w ++ [1]).sum + 1 := by
  simp [target, sum_encode hw, Nat.add_assoc]

end SubmittedGenus.BinaryCode
