import Results.Genus.Injection.SourceClasses

namespace SubmittedGenus.OriginalMaps

open OriginalSources

/-- The actual low-depth source type, across all multiplicities. -/
abbrev LowSource := {d : KunzData // low d}

/-- Appending to a genuine low-depth word, packaged again as genuine Kunz data. -/
def lowAppend (a : ℕ) (ha0 : 0 < a) (ha2 : a ≤ 2) (d : LowSource) : KunzData :=
  ⟨⟨d.val.1.val + 1, by omega⟩,
    ⟨KunzWord.append d.val.2.val a,
      d.val.2.property.append_low_depth d.val.1.property
        ((KunzWord.depth_le_iff d.val.2.val).mp d.property) ha0 ha2⟩⟩

@[simp] theorem lowAppend_weight (a : ℕ) (ha0 : 0 < a) (ha2 : a ≤ 2)
    (d : LowSource) : (lowAppend a ha0 ha2 d).weight = d.val.weight + a :=
  KunzWord.weight_append d.val.2.val d.val.1.property

@[simp] theorem lowAppend_genus (a : ℕ) (ha0 : 0 < a) (ha2 : a ≤ 2)
    (d : LowSource) : (lowAppend a ha0 ha2 d).toSemigroup.genus = d.val.weight + a := by
  rw [KunzData.genus_toSemigroup, lowAppend_weight]

theorem lowAppend_low (a : ℕ) (ha0 : 0 < a) (ha2 : a ≤ 2)
    (d : LowSource) : low (lowAppend a ha0 ha2 d) := by
  apply (KunzWord.depth_le_iff _).mpr
  exact KunzWord.append_bounded
    ((KunzWord.depth_le_iff d.val.2.val).mp d.property) (by omega)

/-- Injectivity holds globally across every old multiplicity, via the
actual target's unique multiplicity and the literal append inverse. -/
theorem lowAppend_semigroup_injective (a : ℕ) (ha0 : 0 < a) (ha2 : a ≤ 2) :
    Function.Injective (fun d : LowSource => (lowAppend a ha0 ha2 d).toSemigroup) := by
  rintro ⟨⟨⟨m, hm⟩, ⟨x, hx⟩⟩, hlowx⟩ ⟨⟨⟨n, hn⟩, ⟨y, hy⟩⟩, hlowy⟩ h
  let hx' := hx.append_low_depth hm ((KunzWord.depth_le_iff x).mp hlowx) ha0 ha2
  let hy' := hy.append_low_depth hn ((KunzWord.depth_le_iff y).mp hlowy) ha0 ha2
  change KunzWord.toSemigroup (KunzWord.append x a) (by omega) hx' =
    KunzWord.toSemigroup (KunzWord.append y a) (by omega) hy' at h
  have hxmult := KunzWord.isMultiplicity_toSemigroup (KunzWord.append x a) (by omega) hx'
  have hymult := KunzWord.isMultiplicity_toSemigroup (KunzWord.append y a) (by omega) hy'
  have hmn : m + 1 = n + 1 := hxmult.unique (h ▸ hymult)
  have hmn' : m = n := by omega
  subst n
  have happ := KunzWord.toSemigroup_injective (by omega) hx' hy' h
  have hxy := KunzWord.append_injective happ
  subst y
  rfl

/-- Actual targets made by different appended letters cannot coincide. -/
theorem lowAppend_letter_eq_of_semigroup_eq
    {a b : ℕ} {ha0 : 0 < a} {ha2 : a ≤ 2} {hb0 : 0 < b} {hb2 : b ≤ 2}
    (d e : LowSource)
    (h : (lowAppend a ha0 ha2 d).toSemigroup = (lowAppend b hb0 hb2 e).toSemigroup) :
    a = b := by
  rcases d with ⟨⟨⟨m, hm⟩, ⟨x, hx⟩⟩, hlowx⟩
  rcases e with ⟨⟨⟨n, hn⟩, ⟨y, hy⟩⟩, hlowy⟩
  let hx' := hx.append_low_depth hm ((KunzWord.depth_le_iff x).mp hlowx) ha0 ha2
  let hy' := hy.append_low_depth hn ((KunzWord.depth_le_iff y).mp hlowy) hb0 hb2
  change KunzWord.toSemigroup (KunzWord.append x a) (by omega) hx' =
    KunzWord.toSemigroup (KunzWord.append y b) (by omega) hy' at h
  have hxmult := KunzWord.isMultiplicity_toSemigroup (KunzWord.append x a) (by omega) hx'
  have hymult := KunzWord.isMultiplicity_toSemigroup (KunzWord.append y b) (by omega) hy'
  have hmn : m + 1 = n + 1 := hxmult.unique (h ▸ hymult)
  have hmn' : m = n := by omega
  subst n
  have happ := KunzWord.toSemigroup_injective (by omega) hx' hy' h
  have hlast := congrArg (fun w : KunzWord (m + 1) => KunzWord.coord w m) happ
  simpa only [KunzWord.coord_append_last _ hm] using hlast

/-- The first map in `cmb:maps`, with actual genus-`g+1` semigroups as target. -/
def LMap (g : ℕ) (s : SourceClass g .L) : NumericalSemigroup.GenusFibre (g + 1) :=
  ⟨(lowAppend 1 (by omega) (by omega)
    ⟨s.val.val, (sector_L_iff s.val.val).mp s.property⟩).toSemigroup, by
      rw [lowAppend_genus]
      exact congrArg (· + 1) s.val.property⟩

theorem LMap_injective (g : ℕ) : Function.Injective (LMap g) := by
  intro x y h
  have hlow := lowAppend_semigroup_injective 1 (by omega) (by omega)
    (congrArg Subtype.val h)
  have hdata : x.val.val = y.val.val := congrArg (fun z : LowSource => z.val) hlow
  exact Subtype.ext (Subtype.ext hdata)

end SubmittedGenus.OriginalMaps
