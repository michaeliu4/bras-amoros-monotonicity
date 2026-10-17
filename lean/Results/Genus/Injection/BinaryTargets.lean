import Results.Genus.Injection.CodeMap
import Results.Genus.Injection.Allocation
import Results.Genus.FiniteArithmetic.BinaryWords

namespace SubmittedGenus.OriginalMaps

open OriginalSources FiniteArithmetic

attribute [local instance] Classical.propDecidable

/-- The entire actual genus-`g+1` binary end-`2` target sector. -/
def BinaryEndTwo (g : ℕ) :=
  {d : KunzData.WeightFibre (g + 1) //
    (∀ a ∈ d.val.toList, a = 1 ∨ a = 2) ∧ ∃ w, d.val.toList = w ++ [2]}

noncomputable instance (g : ℕ) : Fintype (BinaryEndTwo g) :=
  inferInstanceAs (Fintype {d : KunzData.WeightFibre (g + 1) //
    (∀ a ∈ d.val.toList, a = 1 ∨ a = 2) ∧ ∃ w, d.val.toList = w ++ [2]})

def binaryValues (w : List (Fin 2)) : List ℕ := w.map (fun a => a.val + 1)

theorem binaryValues_binary (w : List (Fin 2)) :
    ∀ a ∈ binaryValues w, a = 1 ∨ a = 2 := by
  intro a ha
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
  have := b.isLt
  omega

theorem append_two_binary {w : List ℕ} (hw : ∀ a ∈ w, a = 1 ∨ a = 2) :
    ∀ a ∈ w ++ [2], a = 1 ∨ a = 2 := by
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · exact hw a ha
  · simp_all

theorem binaryValues_injective : Function.Injective binaryValues := by
  apply List.map_injective_iff.mpr
  intro a b h
  change a.val + 1 = b.val + 1 at h
  apply Fin.ext
  omega

theorem exists_binaryValues {w : List ℕ} (hw : ∀ a ∈ w, a = 1 ∨ a = 2) :
    ∃ v : List (Fin 2), binaryValues v = w := by
  induction w with
  | nil => exact ⟨[], rfl⟩
  | cons a w ih =>
    obtain ⟨v, hv⟩ := ih (fun b hb => hw b (by simp [hb]))
    rcases hw a (by simp) with rfl | rfl
    · exact ⟨(0 : Fin 2) :: v, by simp [binaryValues, ← hv]⟩
    · exact ⟨(1 : Fin 2) :: v, by simp [binaryValues, ← hv]⟩

/-- Append the required final `2` to a binary composition of weight `n`. -/
def binarySupplyMap (n : ℕ) (w : BinaryWords n) : BinaryEndTwo (n + 1) := by
  let letters := binaryValues w.val ++ [2]
  let hbinary := append_two_binary (binaryValues_binary w.val)
  let d := KunzWord.binaryData letters hbinary
  have hsum : letters.sum = n + 2 := by
    change (binaryValues w.val ++ [2]).sum = n + 2
    rw [List.sum_append]
    change (binaryValues w.val).sum + 2 = n + 2
    exact congrArg (· + 2) w.property
  have hweight : d.weight = (n + 1) + 1 := by
    rw [← KunzData.sum_toList, KunzWord.toList_binaryData]
    omega
  refine ⟨⟨d, hweight⟩, ?_, ?_⟩
  · change ∀ a ∈ (KunzWord.binaryData letters hbinary).toList, a = 1 ∨ a = 2
    rw [KunzWord.toList_binaryData]
    exact hbinary
  · exact ⟨binaryValues w.val, KunzWord.toList_binaryData letters hbinary⟩

theorem binarySupplyMap_injective (n : ℕ) : Function.Injective (binarySupplyMap n) := by
  intro x y h
  have hwords := congrArg (fun d : BinaryEndTwo (n + 1) => d.val.val.toList) h
  simp only [binarySupplyMap, KunzWord.toList_binaryData] at hwords
  exact Subtype.ext (binaryValues_injective (List.append_cancel_right hwords))

theorem binarySupplyMap_surjective (n : ℕ) : Function.Surjective (binarySupplyMap n) := by
  intro d
  obtain ⟨pre, hprefix⟩ := d.property.2
  have hbinary : ∀ a ∈ pre, a = 1 ∨ a = 2 := by
    intro a ha
    apply d.property.1 a
    rw [hprefix]
    exact List.mem_append_left _ ha
  obtain ⟨w, hw⟩ := exists_binaryValues hbinary
  have hsum : (binaryValues w).sum = n := by
    have htotal := d.val.property
    rw [← KunzData.sum_toList, hprefix, List.sum_append] at htotal
    simp only [List.sum_cons, List.sum_nil, Nat.add_zero] at htotal
    rw [hw]
    omega
  let source : BinaryWords n := ⟨w, hsum⟩
  refine ⟨source, ?_⟩
  have hlist : (binarySupplyMap n source).val.val.toList = d.val.val.toList := by
    simp only [binarySupplyMap, KunzWord.toList_binaryData]
    exact (congrArg (· ++ [2]) hw).trans hprefix.symm
  exact Subtype.ext (Subtype.ext (KunzData.toList_injective hlist))

noncomputable def binarySupplyEquiv (n : ℕ) : BinaryWords n ≃ BinaryEndTwo (n + 1) :=
  Equiv.ofBijective (binarySupplyMap n)
    ⟨binarySupplyMap_injective n, binarySupplyMap_surjective n⟩

/-- Exactly `F_g` genuine binary end-`2` targets; `g=1` comes from the empty
composition, so no boundary word is omitted. -/
theorem binaryEndTwo_card {g : ℕ} (hg : 1 ≤ g) :
    Fintype.card (BinaryEndTwo g) = Nat.fib g := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : g ≠ 0)
  exact (Fintype.card_congr (binarySupplyEquiv n)).symm.trans (binaryWords_card n)

/-- The actual reserved code image lies in precisely this supply sector. -/
def BReserved (g : ℕ) (s : SourceClass g .B) : BinaryEndTwo g := by
  have hweight : (BTarget s.val.val).weight = g + 1 := by
    rw [← KunzData.genus_toSemigroup, BTarget_genus s.property, s.val.property]
  refine ⟨⟨BTarget s.val.val, hweight⟩, ?_, ?_⟩
  · simp only [BTarget, KunzWord.toList_binaryData]
    exact BinaryCode.target_binary _
  · exact ⟨BinaryCode.encode s.val.val.prefixList,
      KunzWord.toList_binaryData (BinaryCode.target s.val.val.prefixList)
        (BinaryCode.target_binary _)⟩

theorem BReserved_injective (g : ℕ) : Function.Injective (BReserved g) := by
  intro x y h
  have hdata := congrArg (fun z : BinaryEndTwo g => z.val.val.toSemigroup) h
  exact Subtype.ext (Subtype.ext (BTarget_injective x.property y.property hdata))

end SubmittedGenus.OriginalMaps
