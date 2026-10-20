import Results.Genus.RawGraph.PackedAcceptance.ReflectionCachedNatural
import Results.Genus.RawGraph.PackedAcceptance.SourceValuePrunedChunks
import Results.Genus.RawGraph.PackedAcceptance.ReflectionOriginalLayout

/-! Native-evaluation shards of the packed range acceptance (PI-chosen trust
model: compiled evaluation).

Executable part (no Finset, no Classical, no noncomputable): `rowNat`, `sliceNat`,
`shardNat`, `shardMod` -- natural-number sums of `ReflectionCachedNatural.residue`
over the retained rows (support gate `2*H < (a-1)*m+p+1` prunes a row to 0).

Soundness part: `sliceNat_cast`, `shardNat_cast`, and `rangeAccepts_of_shards`,
which turns a list of shard literals (checked by `native_decide` in separate
modules) into `RangeAccepts M P a H layouts coeffs`. -/
namespace SubmittedGenus.RawGraph.PackedAcceptance.ArrayNative
open LayoutCompiler Packing
open scoped BigOperators

/-! ### Executable part -/

/-- `∑_{i<n} f i` as a plain loop. -/
def sumTo (n : ℕ) (f : ℕ → ℕ) : ℕ := Nat.fold n (fun i _ acc => acc + f i) 0

/-- Residue of the source row `(m,p,r)`; rows violating `r<p<m` contribute 0 (never used). -/
def rowNat (a H m p r : ℕ) : ℕ :=
  if h : r < p ∧ p < m then ReflectionCachedNatural.residue m r p a H h.1 h.2 else 0

/-- The multiplicity slice `m = mi+3`: pivots `p = 2..min P (m-1)`, `r = 1..p-1`,
omitting rows pruned by the support gate. Natural number, not reduced. -/
def sliceNat (a H P mi : ℕ) : ℕ :=
  sumTo (min P (mi+2) - 1) fun pi =>
    if 2*H < (a-1)*(mi+3)+(pi+2)+1 then 0 else
      sumTo (pi+1) fun ri => rowNat a H (mi+3) (pi+2) (ri+1)

/-- Sum of the slices `lo ≤ mi < hi` (a shard of consecutive multiplicities). -/
def shardNat (a H P lo hi : ℕ) : ℕ := sumTo (hi-lo) fun i => sliceNat a H P (lo+i)

/-- Shard value reduced modulo `modulus H` (this is what the literals record). -/
def shardMod (a H P lo hi : ℕ) : ℕ := shardNat a H P lo hi % modulus H

/-! ### Shard bookkeeping -/

/-- Consecutive cover check of `[start, stop)` by the ranges of a shard list. -/
def coverB : ℕ → List (ℕ × ℕ × ℕ) → ℕ → Bool
  | start, [], stop => decide (start = stop)
  | start, (lo,hi,_) :: t, stop => decide (lo = start) && decide (lo ≤ hi) && coverB hi t stop

/-- Every shard `(lo,hi,lit)` satisfies `shardMod a H P lo hi = lit`. -/
def AllShards (a H P : ℕ) : List (ℕ × ℕ × ℕ) → Prop
  | [] => True
  | (lo,hi,lit) :: t => shardMod a H P lo hi = lit ∧ AllShards a H P t

/-- The literal total of a shard list. -/
def litSum (shards : List (ℕ × ℕ × ℕ)) : ℕ := (shards.map fun s => s.2.2).sum

/-! ### Soundness -/

lemma sumTo_eq_range (n : ℕ) (f : ℕ → ℕ) : sumTo n f = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp [sumTo]
  | succ n ih =>
    rw [Finset.sum_range_succ, ←ih]
    simp only [sumTo, Nat.fold_succ]

/-- The layout used by the native sums (uniform original reflection layout). -/
abbrev layouts (M P a : ℕ) (ha : a=4 ∨ a=5) (t : Triple M P) : Layout t.m :=
  ReflectionOriginalLayout.layout t.m t.r t.p
    (t.parameters ha).2.1 (t.parameters ha).2.2.1

theorem layouts_covers (M P a : ℕ) (ha : a=4 ∨ a=5) (t : Triple M P) :
    Covers (layouts M P a ha t) t.r t.p a :=
  ReflectionOriginalLayout.covers t.m t.r t.p a
    (t.parameters ha).2.1 (t.parameters ha).2.2.1

/-- Row value as an element of the residue ring. -/
def rowVal (M P a H : ℕ) (t : Triple M P) : ZMod (modulus H) :=
  (rowNat a H t.m t.p t.r : ZMod (modulus H))

theorem rowVal_source (M P a H : ℕ) (ha : a=4 ∨ a=5) (t : Triple M P) :
    rowVal M P a H t =
      scalarLayout (layouts M P a ha t) t.r t.p a (digitBase H : ZMod (modulus H)) := by
  have hp := t.parameters ha
  unfold rowVal rowNat
  rw [dif_pos ⟨hp.2.1, hp.2.2.1⟩]
  exact ReflectionCachedNatural.provider_eq_scalar hp H

theorem sliceNat_cast (M P a H : ℕ) (mi : Fin (M-2)) :
    (sliceNat a H P mi.val : ZMod (modulus H)) =
      sourceValuePrunedMultiplicity M P a H (rowVal M P a H) mi := by
  unfold sliceNat sourceValuePrunedMultiplicity
  rw [sumTo_eq_range, Finset.sum_range, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro pi _
  by_cases h : 2*H < (a-1)*(mi.val+3)+(pi.val+2)+1
  · simp only [h, if_true, Nat.cast_zero]
  · simp only [h, if_false]
    rw [sumTo_eq_range, Finset.sum_range, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro ri _
    rfl

theorem shardNat_cast (a H P lo hi : ℕ) :
    (shardNat a H P lo hi : ZMod (modulus H)) =
      ∑ i ∈ Finset.Ico lo hi, (sliceNat a H P i : ZMod (modulus H)) := by
  unfold shardNat
  rw [sumTo_eq_range, Finset.sum_Ico_eq_sum_range, Nat.cast_sum]

lemma coverB_le : ∀ (shards : List (ℕ × ℕ × ℕ)) (start stop : ℕ),
    coverB start shards stop = true → start ≤ stop := by
  intro shards
  induction shards with
  | nil => intro start stop h; simp [coverB] at h; omega
  | cons s t ih =>
    obtain ⟨lo, hi, lit⟩ := s
    intro start stop h
    simp only [coverB, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    have := ih hi stop h3
    omega

lemma sum_cover {G : Type*} [AddCommMonoid G] (g : ℕ → G) :
    ∀ (shards : List (ℕ × ℕ × ℕ)) (start stop : ℕ), coverB start shards stop = true →
      ∑ i ∈ Finset.Ico start stop, g i =
        (shards.map fun s => ∑ i ∈ Finset.Ico s.1 s.2.1, g i).sum := by
  intro shards
  induction shards with
  | nil => intro start stop h; simp [coverB] at h; simp [h]
  | cons s t ih =>
    obtain ⟨lo, hi, lit⟩ := s
    intro start stop h
    simp only [coverB, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    have hle := coverB_le t hi stop h3
    subst h1
    rw [List.map_cons, List.sum_cons, ←ih hi stop h3]
    exact (Finset.sum_Ico_consecutive g h2 hle).symm

lemma shards_cast (P a H : ℕ) :
    ∀ (shards : List (ℕ × ℕ × ℕ)), AllShards a H P shards →
      ((shards.map fun s => ∑ i ∈ Finset.Ico s.1 s.2.1,
          (sliceNat a H P i : ZMod (modulus H))).sum) = (litSum shards : ZMod (modulus H)) := by
  intro shards
  induction shards with
  | nil => intro _; simp [litSum]
  | cons s t ih =>
    obtain ⟨lo, hi, lit⟩ := s
    intro h
    obtain ⟨h1, h2⟩ := h
    have ih' := ih h2
    have hs : (∑ i ∈ Finset.Ico lo hi, (sliceNat a H P i : ZMod (modulus H))) =
        (lit : ZMod (modulus H)) := by
      rw [←shardNat_cast]
      have := (ZMod.natCast_eq_natCast_iff' (shardNat a H P lo hi) lit (modulus H)).mpr
      apply this
      have h1' : shardNat a H P lo hi % modulus H = lit := h1
      rw [h1']
      exact (Nat.mod_eq_of_lt (by
        have : lit = shardNat a H P lo hi % modulus H := h1'.symm
        rw [this]
        exact Nat.mod_lt _ (by unfold modulus digitBase; positivity))).symm
    simp only [List.map_cons, List.sum_cons, hs, ih']
    simp only [litSum, List.map_cons, List.sum_cons, Nat.cast_add]

/-- Main bridge: shard literals (each a `native_decide`-checkable equation) whose
total reduces to a packed coefficient vector give `RangeAccepts`. The shard ranges
must consecutively cover multiplicities `mi = 0, …, M-3` (i.e. `m = 3, …, M`). -/
theorem rangeAccepts_of_shards (M P a H : ℕ) (ha : a=4 ∨ a=5)
    (shards : List (ℕ × ℕ × ℕ)) (hcov : coverB 0 shards (M-2) = true)
    (hshards : AllShards a H P shards)
    (coeffs : Fin (H+1) → ℕ)
    (hsum : litSum shards % modulus H = pack (digitBase H) coeffs)
    (hb : ∀ i, coeffs i < digitBase H) :
    RangeAccepts M P a H (layouts M P a ha) coeffs := by
  have hv : ∀ t, rowVal M P a H t =
      scalarLayout (layouts M P a ha t) t.r t.p a (digitBase H : ZMod (modulus H)) :=
    rowVal_source M P a H ha
  apply accepted_range_of_source_value_pruned_chunks M P a H (layouts M P a ha) ha
    (layouts_covers M P a ha) (rowVal M P a H) hv (fun _ => 1)
    (fun mi _ => (sliceNat a H P mi.val : ZMod (modulus H)))
  · intro mi
    simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_const, Finset.card_singleton,
      one_smul]
    exact (sliceNat_cast M P a H mi).symm
  · refine ⟨?_, hb⟩
    simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_const, Finset.card_singleton,
      one_smul]
    have h1 : (∑ mi : Fin (M-2), (sliceNat a H P mi.val : ZMod (modulus H))) =
        ∑ i ∈ Finset.Ico 0 (M-2), (sliceNat a H P i : ZMod (modulus H)) := by
      rw [←Finset.range_eq_Ico, Finset.sum_range]
    rw [h1, sum_cover _ shards 0 (M-2) hcov, shards_cast P a H shards hshards,
      ZMod.val_natCast]
    exact hsum

/-- Coefficient form. -/
theorem range_coeff_of_shards (M P a H : ℕ) (ha : a=4 ∨ a=5)
    (shards : List (ℕ × ℕ × ℕ)) (hcov : coverB 0 shards (M-2) = true)
    (hshards : AllShards a H P shards)
    (coeffs : Fin (H+1) → ℕ)
    (hsum : litSum shards % modulus H = pack (digitBase H) coeffs)
    (hb : ∀ i, coeffs i < digitBase H) (k : Fin (H+1)) :
    (rangePolynomial M P a).coeff k.val = coeffs k :=
  accepted_range_coeff M P a H (layouts M P a ha) ha (layouts_covers M P a ha) coeffs
    (rangeAccepts_of_shards M P a H ha shards hcov hshards coeffs hsum hb) k

#print axioms sliceNat_cast
#print axioms rangeAccepts_of_shards
#print axioms range_coeff_of_shards
end SubmittedGenus.RawGraph.PackedAcceptance.ArrayNative
