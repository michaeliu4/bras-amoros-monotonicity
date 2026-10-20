import Results.Genus.Semigroup
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

/-!
# Positive Kunz coordinates

Coordinates are indexed by `Fin (m - 1)`; coordinate `i` has physical residue
`i.val + 1`. The empty word at multiplicity one is retained explicitly.
-/

namespace SubmittedGenus

abbrev KunzWord (m : ℕ) := Fin (m - 1) → ℕ

namespace KunzWord

/-- Physical indexing, extended by zero outside the nonzero residues. -/
def coord {m : ℕ} (x : KunzWord m) (i : ℕ) : ℕ :=
  if h : 0 < i ∧ i < m then x ⟨i - 1, by omega⟩ else 0

@[simp] theorem coord_zero {m : ℕ} (x : KunzWord m) : coord x 0 = 0 := by
  simp [coord]

@[simp] theorem coord_of_ge {m i : ℕ} (x : KunzWord m) (hi : m ≤ i) :
    coord x i = 0 := by simp [coord, Nat.not_lt.mpr hi]

@[simp] theorem coord_index {m : ℕ} (x : KunzWord m) (i : Fin (m - 1)) :
    coord x (i.val + 1) = x i := by
  have hi : i.val + 1 < m := by omega
  simp [coord, hi]

theorem coord_le_sum {m : ℕ} (x : KunzWord m) (i : ℕ) :
    coord x i ≤ ∑ j, x j := by
  unfold coord
  split_ifs with h
  · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
  · exact Nat.zero_le _

/-- The exact positive-word conditions of Lemma `cmb:kunz`, self-pairs included. -/
structure Valid {m : ℕ} (x : KunzWord m) : Prop where
  positive : ∀ i, 0 < x i
  noncarry : ∀ i j : ℕ, 0 < i → i < m → 0 < j → j < m → i + j < m →
    coord x (i + j) ≤ coord x i + coord x j
  carry : ∀ i j : ℕ, 0 < i → i < m → 0 < j → j < m → m < i + j →
    coord x (i + j - m) ≤ coord x i + coord x j + 1

theorem Valid.coord_pos {m : ℕ} {x : KunzWord m} (hx : Valid x)
    {i : ℕ} (h0 : 0 < i) (hm : i < m) : 0 < coord x i := by
  rw [coord, dif_pos (show 0 < i ∧ i < m from ⟨h0, hm⟩)]
  exact hx.positive _

/-- Combining ordinary, carried, and residue-zero pairs. -/
theorem Valid.mod_inequality {m : ℕ} {x : KunzWord m} (hx : Valid x)
    (hm : 0 < m) {i j : ℕ} (hi : i < m) (hj : j < m) :
    coord x ((i + j) % m) ≤ coord x i + coord x j +
      if m ≤ i + j then 1 else 0 := by
  by_cases hi0 : i = 0
  · subst i
    simp [Nat.mod_eq_of_lt hj, Nat.not_le.mpr hj]
  by_cases hj0 : j = 0
  · subst j
    simp [Nat.mod_eq_of_lt hi, Nat.not_le.mpr hi]
  by_cases hlt : i + j < m
  · simpa [Nat.mod_eq_of_lt hlt, Nat.not_le.mpr hlt] using
      hx.noncarry i j (by omega) hi (by omega) hj hlt
  by_cases heq : i + j = m
  · simp [heq]
  have hgt : m < i + j := by omega
  have hrem : (i + j) % m = i + j - m := by
    rw [Nat.mod_eq_sub_mod (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  simpa [hrem, Nat.le_of_lt hgt] using
    hx.carry i j (by omega) hi (by omega) hj hgt

/-- The union of the residue tails prescribed by a word. -/
def TailMem {m : ℕ} (x : KunzWord m) (n : ℕ) : Prop := coord x (n % m) ≤ n / m

@[simp] theorem tailMem_zero {m : ℕ} (x : KunzWord m) : TailMem x 0 := by
  simp [TailMem]

theorem Valid.tailMem_add {m : ℕ} {x : KunzWord m} (hx : Valid x) (hm : 0 < m)
    {a b : ℕ} (ha : TailMem x a) (hb : TailMem x b) : TailMem x (a + b) := by
  have h := hx.mod_inequality hm (Nat.mod_lt a hm) (Nat.mod_lt b hm)
  unfold TailMem at *
  rw [Nat.add_mod, Nat.add_div hm]
  omega

theorem tailMem_of_large {m : ℕ} (x : KunzWord m) (hm : 0 < m) {n : ℕ}
    (hn : m * (∑ i, x i) ≤ n) : TailMem x n := by
  apply (coord_le_sum x _).trans
  exact (Nat.le_div_iff_mul_le hm).mpr (by simpa [Nat.mul_comm] using hn)

/-- Construct the genuine numerical semigroup of a valid positive word. -/
def toSemigroup {m : ℕ} (x : KunzWord m) (hm : 0 < m) (hx : Valid x) :
    NumericalSemigroup where
  toAddSubmonoid :=
    { carrier := {n | TailMem x n}
      zero_mem' := tailMem_zero x
      add_mem' := hx.tailMem_add hm }
  finite_compl := by
    apply (Finset.finite_toSet (Finset.range (m * ∑ i, x i))).subset
    intro n hn
    change ¬ TailMem x n at hn
    exact Finset.mem_range.mpr (lt_of_not_ge (fun h => hn (tailMem_of_large x hm h)))

@[simp] theorem mem_toSemigroup {m n : ℕ} (x : KunzWord m) (hm : 0 < m) (hx : Valid x) :
    n ∈ toSemigroup x hm hx ↔ TailMem x n := Iff.rfl

theorem tailMem_residue {m : ℕ} (x : KunzWord m) (hm : 0 < m)
    {r k : ℕ} (hr : r < m) : TailMem x (r + m * k) ↔ coord x r ≤ k := by
  simp [TailMem, Nat.add_mod, Nat.mod_eq_of_lt hr, Nat.add_mul_div_left _ _ hm,
    Nat.div_eq_of_lt hr]

theorem multiplicity_mem {m : ℕ} (x : KunzWord m) (hm : 0 < m) (hx : Valid x) :
    m ∈ toSemigroup x hm hx := by
  simp [TailMem]

theorem below_multiplicity_not_mem {m : ℕ} (x : KunzWord m) (hm : 0 < m)
    (hx : Valid x) {n : ℕ} (h0 : 0 < n) (hn : n < m) :
    n ∉ toSemigroup x hm hx := by
  have hp := hx.coord_pos h0 hn
  simp [TailMem, Nat.mod_eq_of_lt hn, Nat.div_eq_of_lt hn, Nat.not_le.mpr hp]

theorem isMultiplicity_toSemigroup {m : ℕ} (x : KunzWord m) (hm : 0 < m)
    (hx : Valid x) : (toSemigroup x hm hx).IsMultiplicity m := by
  refine ⟨hm, multiplicity_mem x hm hx, ?_⟩
  intro n hn hnS
  by_contra h
  exact below_multiplicity_not_mem x hm hx hn (by omega) hnS

/-- Extract the least nongap quotient in each nonzero residue. -/
noncomputable def ofSemigroup (S : NumericalSemigroup) {m : ℕ}
    (hm : S.IsMultiplicity m) : KunzWord m :=
  fun i => S.residueLevel hm.1 (i.val + 1)

theorem coord_ofSemigroup (S : NumericalSemigroup) {m : ℕ}
    (hm : S.IsMultiplicity m) {i : ℕ} (hi : i < m) :
    coord (ofSemigroup S hm) i = S.residueLevel hm.1 i := by
  by_cases hz : i = 0
  · subst i
    simp
  · have hip : 0 < i := by omega
    simp [coord, hip, hi, ofSemigroup, Nat.sub_add_cancel hip]

theorem valid_ofSemigroup (S : NumericalSemigroup) {m : ℕ} (hm : S.IsMultiplicity m) :
    Valid (ofSemigroup S hm) where
  positive := by
    intro i
    have hmem := S.residueLevel_mem hm.1 (i.val + 1)
    change 0 < S.residueLevel hm.1 (i.val + 1)
    by_contra h
    have hz : S.residueLevel hm.1 (i.val + 1) = 0 := by omega
    simp only [hz, Nat.mul_zero, Nat.add_zero] at hmem
    have hle := hm.2.2 (i.val + 1) (by omega) hmem
    omega
  noncarry := by
    intro i j hi0 hi hj0 hj hij
    simp only [coord_ofSemigroup S hm hi, coord_ofSemigroup S hm hj,
      coord_ofSemigroup S hm hij]
    apply S.residueLevel_le hm.1
    have h := S.add_mem (S.residueLevel_mem hm.1 i) (S.residueLevel_mem hm.1 j)
    convert h using 1 <;> ring
  carry := by
    intro i j hi0 hi hj0 hj hij
    have hr : i + j - m < m := by omega
    simp only [coord_ofSemigroup S hm hi, coord_ofSemigroup S hm hj,
      coord_ofSemigroup S hm hr]
    apply S.residueLevel_le hm.1
    have h := S.add_mem (S.residueLevel_mem hm.1 i) (S.residueLevel_mem hm.1 j)
    convert h using 1
    simp only [Nat.mul_add, Nat.mul_one]
    omega

/-- The extracted positive word reconstructs the original submonoid exactly. -/
theorem toSemigroup_ofSemigroup (S : NumericalSemigroup) {m : ℕ}
    (hm : S.IsMultiplicity m) :
    toSemigroup (ofSemigroup S hm) hm.1 (valid_ofSemigroup S hm) = S := by
  apply NumericalSemigroup.ext
  intro n
  rw [mem_toSemigroup]
  unfold TailMem
  rw [coord_ofSemigroup S hm (Nat.mod_lt _ hm.1)]
  rw [← S.residue_mem_iff hm.1 hm.2.1]
  rw [Nat.mod_add_div]

/-- Every numerical semigroup, including `ℕ`, has positive Kunz coordinates. -/
theorem exists_kunzWord (S : NumericalSemigroup) :
    ∃ (m : ℕ) (hm : 0 < m) (x : KunzWord m) (hx : Valid x), toSemigroup x hm hx = S :=
  ⟨S.multiplicity, S.isMultiplicity_multiplicity.1,
    ofSemigroup S S.isMultiplicity_multiplicity,
    valid_ofSemigroup S S.isMultiplicity_multiplicity,
    toSemigroup_ofSemigroup S S.isMultiplicity_multiplicity⟩

/-- Weight is the sum of the positive coordinates, including zero for the empty word. -/
def weight {m : ℕ} (x : KunzWord m) : ℕ := ∑ i, x i

/-- Depth, with value zero for the empty word. -/
def depth {m : ℕ} (x : KunzWord m) : ℕ := Finset.univ.sup x

theorem Valid.length_le_weight {m : ℕ} {x : KunzWord m} (hx : Valid x) :
    m - 1 ≤ weight x := by
  calc
    m - 1 = ∑ _i : Fin (m - 1), 1 := by simp
    _ ≤ ∑ i, x i := Finset.sum_le_sum (fun i _ => hx.positive i)

theorem Valid.multiplicity_le_weight_succ {m : ℕ} {x : KunzWord m} (hx : Valid x) :
    m ≤ weight x + 1 := by have := hx.length_le_weight; omega

theorem le_depth {m : ℕ} (x : KunzWord m) (i : Fin (m - 1)) : x i ≤ depth x :=
  Finset.le_sup (Finset.mem_univ i)

theorem coord_le_depth {m : ℕ} (x : KunzWord m) (i : ℕ) : coord x i ≤ depth x := by
  unfold coord
  split_ifs with h
  · exact le_depth x _
  · exact Nat.zero_le _

theorem depth_le_iff {m a : ℕ} (x : KunzWord m) : depth x ≤ a ↔ ∀ i, x i ≤ a := by
  simp [depth, Finset.sup_le_iff]

theorem depth_le_weight {m : ℕ} (x : KunzWord m) : depth x ≤ weight x := by
  apply (depth_le_iff x).mpr
  intro i
  simpa only [coord_index, weight] using coord_le_sum x (i.val + 1)

theorem exists_eq_depth {m : ℕ} (x : KunzWord m) (hm : 1 < m) :
    ∃ i : Fin (m - 1), x i = depth x := by
  have hne : (Finset.univ : Finset (Fin (m - 1))).Nonempty :=
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup Finset.univ hne x
  exact ⟨i, hi.symm⟩

def maxima {m : ℕ} (x : KunzWord m) : Finset (Fin (m - 1)) :=
  Finset.univ.filter (fun i => x i = depth x)

/-- The physical index of the rightmost maximum, or zero for the empty word. -/
def rightmostMaximum {m : ℕ} (x : KunzWord m) : ℕ :=
  (maxima x).sup (fun i => i.val + 1)

theorem maxima_nonempty {m : ℕ} (x : KunzWord m) (hm : 1 < m) : (maxima x).Nonempty := by
  obtain ⟨i, hi⟩ := exists_eq_depth x hm
  exact ⟨i, by simp [maxima, hi]⟩

theorem rightmostMaximum_spec {m : ℕ} (x : KunzWord m) (hm : 1 < m) :
    0 < rightmostMaximum x ∧ rightmostMaximum x < m ∧
      coord x (rightmostMaximum x) = depth x := by
  obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_sup (maxima x) (maxima_nonempty x hm)
    (fun i => i.val + 1)
  have hx : x i = depth x := (Finset.mem_filter.mp hi).2
  change rightmostMaximum x = i.val + 1 at he
  rw [he, coord_index]
  exact ⟨by omega, by omega, hx⟩

theorem coord_lt_depth_after_rightmost {m i : ℕ} (x : KunzWord m)
    (hi : rightmostMaximum x < i) (him : i < m) : coord x i < depth x := by
  have hi0 : 0 < i := by omega
  let j : Fin (m - 1) := ⟨i - 1, by omega⟩
  have hj : j.val + 1 = i := by dsimp [j]; omega
  have hcoord : coord x i = x j := by rw [← hj, coord_index]
  have hbound := coord_le_depth x i
  by_contra hn
  have heq : x j = depth x := by omega
  have hjmem : j ∈ maxima x := by simp [maxima, heq]
  have hle : j.val + 1 ≤ rightmostMaximum x :=
    Finset.le_sup (f := fun i => i.val + 1) hjmem
  omega

/-- The gap at level `k` in physical residue `i+1`. -/
def indexedGap {m : ℕ} (x : KunzWord m) (hm : 0 < m) (hx : Valid x)
    (p : Σ i : Fin (m - 1), Fin (x i)) : {n // n ∈ (toSemigroup x hm hx).gaps} :=
  ⟨p.1.val + 1 + m * p.2.val, by
    rw [NumericalSemigroup.mem_gaps, mem_toSemigroup,
      tailMem_residue x hm (by have := p.1.isLt; omega), coord_index]
    exact Nat.not_le.mpr p.2.isLt⟩

theorem indexedGap_injective {m : ℕ} (x : KunzWord m) (hm : 0 < m) (hx : Valid x) :
    Function.Injective (indexedGap x hm hx) := by
  rintro ⟨i, k⟩ ⟨j, l⟩ h
  have he : i.val + 1 + m * k.val = j.val + 1 + m * l.val :=
    congrArg Subtype.val h
  have hi : i.val + 1 < m := by omega
  have hj : j.val + 1 < m := by omega
  have hr := congrArg (fun n => n % m) he
  simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hr
  have hij : i = j := Fin.ext (by omega)
  subst j
  have hq := congrArg (fun n => n / m) he
  simp only [Nat.add_mul_div_left _ _ hm, Nat.div_eq_of_lt hi, Nat.zero_add] at hq
  have hkl : k = l := Fin.ext hq
  subst l
  rfl

theorem indexedGap_surjective {m : ℕ} (x : KunzWord m) (hm : 0 < m) (hx : Valid x) :
    Function.Surjective (indexedGap x hm hx) := by
  intro n
  have hn : n.val / m < coord x (n.val % m) := by
    have h := (NumericalSemigroup.mem_gaps _ _).mp n.property
    simpa only [mem_toSemigroup, TailMem, Nat.not_le] using h
  have hr : n.val % m < m := Nat.mod_lt _ hm
  have hr0 : 0 < n.val % m := by
    by_contra h
    have hz : n.val % m = 0 := by omega
    simp [hz] at hn
  let i : Fin (m - 1) := ⟨n.val % m - 1, by omega⟩
  have hi : i.val + 1 = n.val % m := by dsimp [i]; omega
  have hcoord : coord x (n.val % m) = x i := by rw [← hi, coord_index]
  let k : Fin (x i) := ⟨n.val / m, by simpa only [hcoord] using hn⟩
  refine ⟨⟨i, k⟩, Subtype.ext ?_⟩
  change i.val + 1 + m * (n.val / m) = n.val
  rw [hi]
  exact Nat.mod_add_div _ _

/-- The genus is exactly the coordinate sum, by an explicit bijection of gaps. -/
theorem genus_toSemigroup {m : ℕ} (x : KunzWord m) (hm : 0 < m) (hx : Valid x) :
    (toSemigroup x hm hx).genus = weight x := by
  classical
  have hc := Fintype.card_congr (Equiv.ofBijective (indexedGap x hm hx)
    ⟨indexedGap_injective x hm hx, indexedGap_surjective x hm hx⟩)
  simpa [NumericalSemigroup.genus, weight, Fintype.card_sigma] using hc.symm

/-- Distinct positive words at the same multiplicity give distinct actual semigroups. -/
theorem toSemigroup_injective {m : ℕ} (hm : 0 < m) {x y : KunzWord m}
    (hx : Valid x) (hy : Valid y) (h : toSemigroup x hm hx = toSemigroup y hm hy) : x = y := by
  funext i
  have hi : i.val + 1 < m := by omega
  have hxmem : i.val + 1 + m * x i ∈ toSemigroup x hm hx := by
    rw [mem_toSemigroup, tailMem_residue x hm hi, coord_index]
  have hymem : i.val + 1 + m * y i ∈ toSemigroup y hm hy := by
    rw [mem_toSemigroup, tailMem_residue y hm hi, coord_index]
  rw [h, mem_toSemigroup, tailMem_residue y hm hi, coord_index] at hxmem
  rw [← h, mem_toSemigroup, tailMem_residue x hm hi, coord_index] at hymem
  exact Nat.le_antisymm hymem hxmem

@[simp] theorem ofSemigroup_toSemigroup {m : ℕ} (x : KunzWord m) (hm : 0 < m)
    (hx : Valid x) :
    ofSemigroup (toSemigroup x hm hx) (isMultiplicity_toSemigroup x hm hx) = x := by
  apply toSemigroup_injective hm
    (valid_ofSemigroup _ (isMultiplicity_toSemigroup x hm hx)) hx
  exact toSemigroup_ofSemigroup _ _

/-- The Frobenius formula at the rightmost maximal coordinate. The hypotheses
say exactly that `a` is the depth and `p` is its rightmost occurrence. -/
theorem frobenius_toSemigroup {m : ℕ} (x : KunzWord m) (hm : 0 < m) (hx : Valid x)
    {a p : ℕ} (hp0 : 0 < p) (hp : p < m) (hpa : coord x p = a)
    (hmax : ∀ i : ℕ, i < m → coord x i ≤ a)
    (hright : ∀ i : ℕ, p < i → i < m → coord x i < a) :
    (toSemigroup x hm hx).frobenius = (((a - 1) * m + p : ℕ) : ℤ) := by
  have ha : 0 < a := hpa ▸ hx.coord_pos hp0 hp
  apply NumericalSemigroup.frobenius_eq_of_greatest_gap
  · rw [mem_toSemigroup]
    have he : (a - 1) * m + p = p + m * (a - 1) := by ac_rfl
    rw [he, tailMem_residue x hm hp, hpa]
    omega
  · intro n hn
    have hgap : n / m < coord x (n % m) := by
      simpa only [mem_toSemigroup, TailMem, Nat.not_le] using hn
    have hr : n % m < m := Nat.mod_lt n hm
    have hnexp := Nat.mod_add_div n m
    have hmcomm : (a - 1) * m = m * (a - 1) := Nat.mul_comm _ _
    by_cases hle : n % m ≤ p
    · have hlevel : n / m ≤ a - 1 := by have := hmax (n % m) hr; omega
      have hmul := Nat.mul_le_mul_left m hlevel
      omega
    · have hstrict := hright (n % m) (by omega) hr
      have hlevel : n / m + 1 ≤ a - 1 := by omega
      have hmul := Nat.mul_le_mul_left m hlevel
      simp only [Nat.mul_add, Nat.mul_one] at hmul
      omega

/-- The coordinate sum also computes genus when coordinates are extracted. -/
theorem genus_eq_weight_ofSemigroup (S : NumericalSemigroup) {m : ℕ}
    (hm : S.IsMultiplicity m) : S.genus = weight (ofSemigroup S hm) := by
  have h := genus_toSemigroup (ofSemigroup S hm) hm.1 (valid_ofSemigroup S hm)
  simpa only [toSemigroup_ofSemigroup] using h

theorem frobenius_eq_depth_rightmost {m : ℕ} (x : KunzWord m) (hm : 1 < m)
    (hx : Valid x) :
    (toSemigroup x (by omega) hx).frobenius =
      (((depth x - 1) * m + rightmostMaximum x : ℕ) : ℤ) := by
  have hs := rightmostMaximum_spec x hm
  exact frobenius_toSemigroup x (by omega) hx hs.1 hs.2.1 hs.2.2
    (fun i _ => coord_le_depth x i) (fun i hi him => coord_lt_depth_after_rightmost x hi him)

def empty : KunzWord 1 := Fin.elim0

@[simp] theorem weight_empty : weight empty = 0 := by simp [weight]

@[simp] theorem depth_empty : depth empty = 0 := by simp [depth]

@[simp] theorem rightmostMaximum_empty : rightmostMaximum empty = 0 := by
  simp [rightmostMaximum, maxima]

theorem valid_empty : Valid empty where
  positive := by intro i; exact Fin.elim0 i
  noncarry := by intros; omega
  carry := by intros; omega

@[simp] theorem toSemigroup_empty : toSemigroup empty (by decide) valid_empty =
    NumericalSemigroup.full := by
  apply NumericalSemigroup.ext
  intro n
  simp [TailMem, Nat.mod_one]

end KunzWord

abbrev KunzValid {m : ℕ} (x : KunzWord m) := KunzWord.Valid x

/-- A positive multiplicity together with a valid positive word; `m=1`
contains precisely the empty word. -/
abbrev KunzData := Σ m : {m : ℕ // 0 < m}, {x : KunzWord m.val // KunzValid x}

namespace KunzData

def toSemigroup (d : KunzData) : NumericalSemigroup :=
  KunzWord.toSemigroup d.2.val d.1.property d.2.property

def weight (d : KunzData) : ℕ := KunzWord.weight d.2.val

def depth (d : KunzData) : ℕ := KunzWord.depth d.2.val

@[simp] theorem genus_toSemigroup (d : KunzData) : d.toSemigroup.genus = d.weight :=
  KunzWord.genus_toSemigroup _ _ _

theorem toSemigroup_injective : Function.Injective toSemigroup := by
  rintro ⟨⟨m, hm⟩, ⟨x, hx⟩⟩ ⟨⟨n, hn⟩, ⟨y, hy⟩⟩ h
  change KunzWord.toSemigroup x hm hx = KunzWord.toSemigroup y hn hy at h
  have hxmult := KunzWord.isMultiplicity_toSemigroup x hm hx
  have hymult := KunzWord.isMultiplicity_toSemigroup y hn hy
  have hmn : m = n := hxmult.unique (h ▸ hymult)
  subst n
  have hxy := KunzWord.toSemigroup_injective hm hx hy h
  subst y
  rfl

theorem toSemigroup_surjective : Function.Surjective toSemigroup := by
  intro S
  obtain ⟨m, hm, x, hx, h⟩ := KunzWord.exists_kunzWord S
  exact ⟨⟨⟨m, hm⟩, ⟨x, hx⟩⟩, h⟩

/-- The complete positive-Kunz-word correspondence, including the empty case. -/
noncomputable def equivNumericalSemigroup : KunzData ≃ NumericalSemigroup :=
  Equiv.ofBijective toSemigroup ⟨toSemigroup_injective, toSemigroup_surjective⟩

/-- Words of weight `g`, across every multiplicity. -/
def WeightFibre (g : ℕ) := {d : KunzData // d.weight = g}

def toGenusFibre (g : ℕ) (d : WeightFibre g) : NumericalSemigroup.GenusFibre g :=
  ⟨d.val.toSemigroup, by rw [genus_toSemigroup]; exact d.property⟩

theorem toGenusFibre_injective (g : ℕ) : Function.Injective (toGenusFibre g) := by
  intro x y h
  apply Subtype.ext
  apply toSemigroup_injective
  exact congrArg Subtype.val h

theorem toGenusFibre_surjective (g : ℕ) : Function.Surjective (toGenusFibre g) := by
  intro S
  obtain ⟨d, hd⟩ := toSemigroup_surjective S.val
  have hw : d.weight = g := by rw [← genus_toSemigroup, hd]; exact S.property
  exact ⟨⟨d, hw⟩, Subtype.ext hd⟩

/-- The source-correct count bridge: genuine genus and word weight fibres are equivalent. -/
noncomputable def equivGenusFibre (g : ℕ) : WeightFibre g ≃ NumericalSemigroup.GenusFibre g :=
  Equiv.ofBijective (toGenusFibre g) ⟨toGenusFibre_injective g, toGenusFibre_surjective g⟩

noncomputable instance (g : ℕ) : Fintype (WeightFibre g) :=
  Fintype.ofEquiv (NumericalSemigroup.GenusFibre g) (equivGenusFibre g).symm

theorem count_eq_card_weightFibre (g : ℕ) :
    NumericalSemigroup.count g = Fintype.card (WeightFibre g) :=
  (Fintype.card_congr (equivGenusFibre g)).symm

end KunzData

end SubmittedGenus
