import Results.Genus.Injection
import Results.Genus.Injection.WordMaps

/-!
# Frobenius restoration in Kunz coordinates

This connects `cmb:parent`'s genuine-semigroup operation to decrementing the
rightmost maximal coordinate. The low-parent characterization is stated as
bounds on the actual Kunz letters, with all multiplicity conditions explicit.
-/

namespace SubmittedGenus.KunzWord

def lowerAt {m : ℕ} (x : KunzWord m) (p : Fin (m - 1)) : KunzWord m :=
  fun i => if i = p then x p - 1 else x i

@[simp] theorem lowerAt_self {m : ℕ} (x : KunzWord m) (p : Fin (m - 1)) :
    lowerAt x p p = x p - 1 := by simp [lowerAt]

@[simp] theorem lowerAt_other {m : ℕ} (x : KunzWord m) (p i : Fin (m - 1))
    (hi : i ≠ p) : lowerAt x p i = x i := by simp [lowerAt, hi]

theorem coord_lowerAt {m : ℕ} (x : KunzWord m) (p : Fin (m - 1)) (n : ℕ) :
    coord (lowerAt x p) n = if n = p.val + 1 then x p - 1 else coord x n := by
  by_cases hnp : n = p.val + 1
  · subst n
    simp only [coord_index, lowerAt_self, ↓reduceIte]
  · by_cases hn : 0 < n ∧ n < m
    · have hip : (⟨n - 1, by omega⟩ : Fin (m - 1)) ≠ p := by
        intro h
        have he := congrArg Fin.val h
        simp only at he
        omega
      simp [coord, hn, lowerAt, hip, hnp]
    · simp [coord, hn, hnp]

theorem coord_lowerAt_le {m : ℕ} (x : KunzWord m) (p : Fin (m - 1)) (n : ℕ) :
    coord (lowerAt x p) n ≤ coord x n := by
  rw [coord_lowerAt]
  split_ifs with h
  · subst n
    rw [coord_index]
    exact Nat.sub_le _ _
  · exact le_rfl

theorem lowerAt_positive {m : ℕ} {x : KunzWord m} (hx : Valid x)
    {p : Fin (m - 1)} (hp : 2 ≤ x p) : ∀ i, 0 < lowerAt x p i := by
  intro i
  by_cases hi : i = p
  · subst i
    simp only [lowerAt_self]
    omega
  · simpa [lowerAt, hi] using hx.positive i

theorem coord_lowerAt_pos {m : ℕ} {x : KunzWord m} (hx : Valid x)
    {p : Fin (m - 1)} (hp : 2 ≤ x p) {i : ℕ} (hi0 : 0 < i) (him : i < m) :
    0 < coord (lowerAt x p) i := by
  simp only [coord, dif_pos (show 0 < i ∧ i < m from ⟨hi0, him⟩)]
  exact lowerAt_positive hx hp _

/-- Lowering a maximal coordinate at least two preserves Kunz validity. -/
theorem Valid.lowerMaximum {m : ℕ} {x : KunzWord m} (hx : Valid x)
    {p : Fin (m - 1)} (hp : 2 ≤ x p) (hmax : ∀ i, x i ≤ x p) :
    Valid (lowerAt x p) := by
  have hbound (n : ℕ) : coord (lowerAt x p) n ≤ x p :=
    (coord_lowerAt_le x p n).trans (coord_le_of_bound hmax n)
  refine ⟨lowerAt_positive hx hp, ?_, ?_⟩
  · intro i j hi0 him hj0 hjm hij
    by_cases hi : i = p.val + 1
    · have htarget := hbound (i + j)
      have hjpos := coord_lowerAt_pos hx hp hj0 hjm
      rw [coord_lowerAt x p i, if_pos hi]
      omega
    · by_cases hj : j = p.val + 1
      · have htarget := hbound (i + j)
        have hipos := coord_lowerAt_pos hx hp hi0 him
        rw [coord_lowerAt x p j, if_pos hj]
        omega
      · rw [coord_lowerAt x p i, if_neg hi, coord_lowerAt x p j, if_neg hj]
        exact (coord_lowerAt_le x p (i + j)).trans
          (hx.noncarry i j hi0 him hj0 hjm hij)
  · intro i j hi0 him hj0 hjm hij
    by_cases hi : i = p.val + 1
    · have htarget := hbound (i + j - m)
      have hjpos := coord_lowerAt_pos hx hp hj0 hjm
      rw [coord_lowerAt x p i, if_pos hi]
      omega
    · by_cases hj : j = p.val + 1
      · have htarget := hbound (i + j - m)
        have hipos := coord_lowerAt_pos hx hp hi0 him
        rw [coord_lowerAt x p j, if_pos hj]
        omega
      · rw [coord_lowerAt x p i, if_neg hi, coord_lowerAt x p j, if_neg hj]
        exact (coord_lowerAt_le x p (i + j - m)).trans
          (hx.carry i j hi0 him hj0 hjm hij)

/-- Lowering one coordinate adds exactly the last omitted member of its
residue tail; there is no hidden change elsewhere in the semigroup. -/
theorem tailMem_lowerAt {m : ℕ} (x : KunzWord m) (hm : 0 < m)
    (p : Fin (m - 1)) (hp : 0 < x p) (n : ℕ) :
    TailMem (lowerAt x p) n ↔
      TailMem x n ∨ n = p.val + 1 + m * (x p - 1) := by
  have hpm : p.val + 1 < m := by omega
  by_cases hr : n % m = p.val + 1
  · have hnew : coord (lowerAt x p) (n % m) = x p - 1 := by
      rw [coord_lowerAt, if_pos hr]
    have hold : coord x (n % m) = x p := by rw [hr, coord_index]
    change coord (lowerAt x p) (n % m) ≤ n / m ↔
      coord x (n % m) ≤ n / m ∨ n = p.val + 1 + m * (x p - 1)
    rw [hnew, hold]
    constructor
    · intro h
      by_cases hq : x p ≤ n / m
      · exact Or.inl hq
      · right
        have heq : n / m = x p - 1 := by omega
        have hn := Nat.mod_add_div n m
        rw [hr, heq] at hn
        exact hn.symm
    · rintro (h | h)
      · omega
      · subst n
        rw [Nat.add_mul_div_left _ _ hm, Nat.div_eq_of_lt hpm]
        omega
  · have hnew : coord (lowerAt x p) (n % m) = coord x (n % m) := by
      rw [coord_lowerAt, if_neg hr]
    change coord (lowerAt x p) (n % m) ≤ n / m ↔
      coord x (n % m) ≤ n / m ∨ n = p.val + 1 + m * (x p - 1)
    rw [hnew]
    constructor
    · exact Or.inl
    · rintro (h | h)
      · exact h
      · subst n
        have hmod : (p.val + 1 + m * (x p - 1)) % m = p.val + 1 := by
          simp [Nat.add_mod, Nat.mod_eq_of_lt hpm]
        exact (hr hmod).elim

/-- At high depth, the lowered word has depth at most three precisely when
the old word has one `4` and every other coordinate is at most three. -/
theorem lowerAt_lowDepth_iff {m : ℕ} (x : KunzWord m) (p : Fin (m - 1))
    (hp : 4 ≤ x p) :
    (∀ i, lowerAt x p i ≤ 3) ↔ x p = 4 ∧ ∀ i, i ≠ p → x i ≤ 3 := by
  constructor
  · intro h
    have hself := h p
    simp only [lowerAt_self] at hself
    refine ⟨by omega, ?_⟩
    intro i hi
    simpa [lowerAt, hi] using h i
  · rintro ⟨hself, hother⟩ i
    by_cases hi : i = p
    · subst i
      simp [hself]
    · simpa [lowerAt, hi] using hother i hi

/-- The last omitted number in the selected residue. -/
def lastGap {m : ℕ} (x : KunzWord m) (p : Fin (m - 1)) : ℕ :=
  p.val + 1 + m * (x p - 1)

/-- A rightmost maximum supplies the genuine semigroup Frobenius. -/
theorem isFrobenius_lastGap {m : ℕ} (x : KunzWord m) (hm : 0 < m)
    (hx : Valid x) (p : Fin (m - 1)) (hmax : ∀ i, x i ≤ x p)
    (hright : ∀ i : ℕ, p.val + 1 < i → i < m → coord x i < x p) :
    (toSemigroup x hm hx).IsFrobenius (lastGap x p) := by
  have hp0 : 0 < p.val + 1 := by omega
  have hpm : p.val + 1 < m := by omega
  have hF := frobenius_toSemigroup x hm hx hp0 hpm (coord_index x p)
    (fun i _ => coord_le_of_bound hmax i) hright
  have hFeq : (toSemigroup x hm hx).frobenius = (lastGap x p : ℤ) := by
    simpa [lastGap, Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hF
  constructor
  · rw [mem_toSemigroup]
    change ¬ TailMem x (p.val + 1 + m * (x p - 1))
    rw [tailMem_residue x hm hpm, coord_index]
    have := hx.positive p
    omega
  · intro n hn
    have h := (toSemigroup x hm hx).gap_le_frobenius hn
    rw [hFeq] at h
    exact_mod_cast h

/-- The abstract genuine parent operation is precisely the coordinate
operation, so its multiplicity really remains `m`. -/
theorem restoreFrobenius_eq_lowerAt {m : ℕ} (x : KunzWord m) (hm : 0 < m)
    (hx : Valid x) (p : Fin (m - 1)) (hp : 2 ≤ x p)
    (hmax : ∀ i, x i ≤ x p)
    (hright : ∀ i : ℕ, p.val + 1 < i → i < m → coord x i < x p) :
    (toSemigroup x hm hx).restoreFrobenius (lastGap x p)
      (isFrobenius_lastGap x hm hx p hmax hright) =
      toSemigroup (lowerAt x p) hm (hx.lowerMaximum hp hmax) := by
  ext n
  simp only [NumericalSemigroup.mem_restoreFrobenius, mem_toSemigroup]
  exact (tailMem_lowerAt x hm p (by omega) n).symm

/-- The lowered word is an actual ordinary parent, not just a valid word
of the right weight. -/
theorem lowerAt_isOrdinaryParent {m : ℕ} (x : KunzWord m) (hm : 0 < m)
    (hx : Valid x) (p : Fin (m - 1)) (hp : 2 ≤ x p)
    (hmax : ∀ i, x i ≤ x p)
    (hright : ∀ i : ℕ, p.val + 1 < i → i < m → coord x i < x p) :
    (toSemigroup (lowerAt x p) hm (hx.lowerMaximum hp hmax)).IsOrdinaryChild
      (toSemigroup x hm hx) := by
  rw [← restoreFrobenius_eq_lowerAt x hm hx p hp hmax hright]
  exact NumericalSemigroup.isOrdinaryChild_restoreFrobenius
    (isFrobenius_lastGap x hm hx p hmax hright)

/-- The low-depth-parent criterion as a statement about the canonical word
depth: the source's maximal letter is `4` and occurs once. -/
theorem lowerAt_depth_le_three_iff {m : ℕ} (x : KunzWord m) (p : Fin (m - 1))
    (hp : 4 ≤ x p) :
    depth (lowerAt x p) ≤ 3 ↔ x p = 4 ∧ ∀ i, i ≠ p → x i ≤ 3 := by
  rw [depth_le_iff]
  exact lowerAt_lowDepth_iff x p hp

end SubmittedGenus.KunzWord
