import Results.Genus.Injection.MapProperties

namespace SubmittedGenus.KunzWord

def replaceInitial {m : ℕ} (x : KunzWord m) : KunzWord m :=
  fun i => if i.val = 0 then 2 else x i

def initialFiveTransform {m : ℕ} (x : KunzWord m) : KunzWord (m + 2) :=
  append (append (replaceInitial x) 1) 3

theorem one_lt_multiplicity_of_initialFive {m : ℕ} (x : KunzWord m)
    (hfirst : coord x 1 = 5) : 1 < m := by
  by_contra h
  have hzero := coord_of_ge x (by omega : m ≤ 1)
  omega

theorem coord_replaceInitial {m i : ℕ} (x : KunzWord m) (hi0 : 0 < i) (him : i < m) :
    coord (replaceInitial x) i = if i = 1 then 2 else coord x i := by
  have heq : i - 1 = 0 ↔ i = 1 := by omega
  simp [coord, hi0, him, replaceInitial, heq]

theorem coord_initialFiveTransform_old {m i : ℕ} (x : KunzWord m)
    (hi0 : 0 < i) (him : i < m) :
    coord (initialFiveTransform x) i = if i = 1 then 2 else coord x i := by
  unfold initialFiveTransform
  rw [coord_append_old _ hi0 (by omega), coord_append_old _ hi0 him,
    coord_replaceInitial x hi0 him]

theorem coord_initialFiveTransform_penultimate {m : ℕ} (x : KunzWord m) (hm : 0 < m) :
    coord (initialFiveTransform x) m = 1 := by
  unfold initialFiveTransform
  rw [coord_append_old _ hm (by omega), coord_append_last _ hm]

theorem coord_initialFiveTransform_last {m : ℕ} (x : KunzWord m) :
    coord (initialFiveTransform x) (m + 1) = 3 := by
  exact coord_append_last _ (by omega)

theorem initialFiveTransform_positive {m : ℕ} {x : KunzWord m} (hx : Valid x) :
    ∀ i, 0 < initialFiveTransform x i := by
  intro i
  unfold initialFiveTransform append replaceInitial
  split_ifs <;> try omega
  exact hx.positive _

theorem initialFiveTransform_bounded {m : ℕ} {x : KunzWord m}
    (hrest : ∀ i, 1 ≤ i.val → x i ≤ 3) : ∀ i, initialFiveTransform x i ≤ 3 := by
  apply append_bounded (a := 3) _ le_rfl
  apply append_bounded (a := 1) _ (by omega)
  intro i
  unfold replaceInitial
  split_ifs with h
  · omega
  · exact hrest i (by omega)

theorem initialFiveTransform_coord_pos {m : ℕ} {x : KunzWord m} (hx : Valid x)
    {i : ℕ} (hi0 : 0 < i) (him : i < m + 2) :
    0 < coord (initialFiveTransform x) i := by
  simp only [coord, dif_pos (show 0 < i ∧ i < m + 2 from ⟨hi0, him⟩)]
  exact initialFiveTransform_positive hx _

/-- The literal fourth map `(5,u) ↦ (2,u,1,3)` preserves every Kunz
inequality at the new modulus `m+2`, including self-pairs. -/
theorem Valid.initialFiveTransform {m : ℕ} {x : KunzWord m} (hx : Valid x)
    (hfirst : coord x 1 = 5) (hrest : ∀ i, 1 ≤ i.val → x i ≤ 3) :
    Valid (initialFiveTransform x) := by
  have hm := one_lt_multiplicity_of_initialFive x hfirst
  have hbound := initialFiveTransform_bounded hrest
  refine ⟨initialFiveTransform_positive hx, ?_, ?_⟩
  · intro i j hi0 him hj0 hjm hij
    have ht := coord_le_of_bound hbound (i + j)
    by_cases hi1 : i = 1
    · subst i
      rw [coord_initialFiveTransform_old x (by omega) hm, if_pos rfl]
      have hj := initialFiveTransform_coord_pos hx hj0 hjm
      omega
    · by_cases hj1 : j = 1
      · subst j
        rw [coord_initialFiveTransform_old x (by omega) hm, if_pos rfl]
        have hi := initialFiveTransform_coord_pos hx hi0 him
        omega
      · have hiold : i < m := by omega
        have hjold : j < m := by omega
        rw [coord_initialFiveTransform_old x hi0 hiold, if_neg hi1,
          coord_initialFiveTransform_old x hj0 hjold, if_neg hj1]
        by_cases hsum : i + j < m
        · rw [coord_initialFiveTransform_old x (by omega) hsum, if_neg (by omega)]
          exact hx.noncarry i j hi0 hiold hj0 hjold hsum
        · by_cases heq : i + j = m
          · rw [heq, coord_initialFiveTransform_penultimate x (by omega)]
            have hipos := hx.coord_pos hi0 hiold
            have hjpos := hx.coord_pos hj0 hjold
            omega
          · have heq : i + j = m + 1 := by omega
            rw [heq, coord_initialFiveTransform_last]
            have hsource := hx.carry i j hi0 hiold hj0 hjold (by omega)
            have hindex : i + j - m = 1 := by omega
            rw [hindex, hfirst] at hsource
            omega
  · intro i j hi0 him hj0 hjm hij
    have ht := coord_le_of_bound hbound (i + j - (m + 2))
    have hi := initialFiveTransform_coord_pos hx hi0 him
    have hj := initialFiveTransform_coord_pos hx hj0 hjm
    omega

theorem weight_replaceInitial {m : ℕ} (x : KunzWord m) (hfirst : coord x 1 = 5) :
    weight (replaceInitial x) + 3 = weight x := by
  have hm := one_lt_multiplicity_of_initialFive x hfirst
  cases m with
  | zero => omega
  | succ n =>
    cases n with
    | zero => omega
    | succ k =>
      change (Fin (k + 1) → ℕ) at x
      have hx0 : x 0 = 5 := by
        have h := coord_index (m := k + 2) x (0 : Fin (k + 1))
        exact h.symm.trans hfirst
      change (∑ i : Fin (k + 1), replaceInitial (m := k + 2) x i) + 3 = ∑ i, x i
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
      simp [replaceInitial, hx0] <;> omega

theorem weight_initialFiveTransform {m : ℕ} (x : KunzWord m) (hfirst : coord x 1 = 5) :
    weight (initialFiveTransform x) = weight x + 1 := by
  have hm := one_lt_multiplicity_of_initialFive x hfirst
  unfold initialFiveTransform
  rw [weight_append _ (by omega), weight_append _ (by omega)]
  have h := weight_replaceInitial x hfirst
  omega

theorem initialFiveTransform_injective {m : ℕ} {x y : KunzWord m}
    (hx : coord x 1 = 5) (hy : coord y 1 = 5)
    (h : initialFiveTransform x = initialFiveTransform y) : x = y := by
  have hrep := append_injective (append_injective h)
  funext i
  by_cases hi : i.val = 0
  · have hxval := coord_index x i
    have hyval := coord_index y i
    rw [hi, Nat.zero_add, hx] at hxval
    rw [hi, Nat.zero_add, hy] at hyval
    exact hxval.symm.trans hyval
  · have hval := congrFun hrep i
    simpa only [replaceInitial, if_neg hi] using hval

end SubmittedGenus.KunzWord

namespace SubmittedGenus.OriginalMaps

open OriginalSources

abbrev TSource := {d : KunzData // sector d = .T}

def TTarget (s : TSource) : KunzData :=
  ⟨⟨s.val.1.val + 2, by omega⟩,
    ⟨KunzWord.initialFiveTransform s.val.2.val,
      s.val.2.property.initialFiveTransform
        ((sector_T_iff s.val).mp s.property).2.2.2.1
        ((sector_T_iff s.val).mp s.property).2.2.2.2⟩⟩

theorem TTarget_genus (s : TSource) : (TTarget s).toSemigroup.genus = s.val.weight + 1 := by
  rw [KunzData.genus_toSemigroup]
  exact KunzWord.weight_initialFiveTransform s.val.2.val
    ((sector_T_iff s.val).mp s.property).2.2.2.1

theorem TTarget_injective : Function.Injective (fun s : TSource => (TTarget s).toSemigroup) := by
  rintro ⟨⟨⟨m, hm⟩, ⟨x, hx⟩⟩, hTx⟩ ⟨⟨⟨n, hn⟩, ⟨y, hy⟩⟩, hTy⟩ h
  have hinitx := ((sector_T_iff _).mp hTx).2.2.2
  have hinity := ((sector_T_iff _).mp hTy).2.2.2
  let hx' := hx.initialFiveTransform hinitx.1 hinitx.2
  let hy' := hy.initialFiveTransform hinity.1 hinity.2
  change KunzWord.toSemigroup (KunzWord.initialFiveTransform x) (by omega) hx' =
    KunzWord.toSemigroup (KunzWord.initialFiveTransform y) (by omega) hy' at h
  have hxmult := KunzWord.isMultiplicity_toSemigroup (KunzWord.initialFiveTransform x) (by omega) hx'
  have hymult := KunzWord.isMultiplicity_toSemigroup (KunzWord.initialFiveTransform y) (by omega) hy'
  have hmn : m + 2 = n + 2 := hxmult.unique (h ▸ hymult)
  have hmn' : m = n := by omega
  subst n
  have hword := KunzWord.toSemigroup_injective (by omega) hx' hy' h
  have hxy := KunzWord.initialFiveTransform_injective hinitx.1 hinity.1 hword
  change x = y at hxy
  subst y
  rfl

def TMap (g : ℕ) (s : SourceClass g .T) : NumericalSemigroup.GenusFibre (g + 1) :=
  ⟨(TTarget ⟨s.val.val, s.property⟩).toSemigroup, by
    rw [TTarget_genus, s.val.property]⟩

theorem TMap_injective (g : ℕ) : Function.Injective (TMap g) := by
  intro x y h
  have hs := TTarget_injective (congrArg Subtype.val h)
  have hd : x.val.val = y.val.val := congrArg (fun z : TSource => z.val) hs
  exact Subtype.ext (Subtype.ext hd)

end SubmittedGenus.OriginalMaps
