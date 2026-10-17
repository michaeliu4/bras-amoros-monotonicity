import Results.Genus.FiniteArithmetic.Reservoir.PrefixSeries

namespace SubmittedGenus.FiniteArithmetic.Reservoir

set_option synthInstance.maxSize 1000

/-- A shifted source cannot have negative residual weight. -/
theorem shift_le_of_element {d g : ℕ} {F : ℕ → Type} (a : Graded.Shift d F g) : d ≤ g := by
  by_contra h
  exact (cast (if_neg h) a : PEmpty).elim

def safeBodyCode {g : ℕ} : SafeBody g → SafeCode
  | .inl w => .inl w.val
  | .inr p => .inr (p.2.1.val, p.2.2.val)

theorem safeBodyCode_weight {g : ℕ} (a : SafeBody g) : (safeBodyCode a).weight = g + 3 := by
  cases a with
  | inl w =>
    change (w.val.map (fun p => uValue p.1 + vValue p.2)).sum + 3 = _
    have h : (w.val.map (fun p => uValue p.1 + vValue p.2)).sum = g := w.property
    omega
  | inr p =>
    have hi := p.1.isLt
    have ha : uValue p.2.1.val = p.1.val := p.2.1.property
    have hb : (p.2.2.val.map (fun x => uValue x.1 + vValue x.2)).sum = g - p.1.val := p.2.2.property
    change uValue p.2.1.val + (p.2.2.val.map (fun x => uValue x.1 + vValue x.2)).sum + 3 = _
    omega

theorem safeBodyCode_injective (g : ℕ) : Function.Injective (@safeBodyCode g) := by
  intro a b h
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl (Subtype.ext (Sum.inl.inj h))
    | inr b => cases h
  | inr a =>
    cases b with
    | inl b => cases h
    | inr b =>
      rcases a with ⟨i, ⟨a, ha⟩, ⟨l, hl⟩⟩
      rcases b with ⟨j, ⟨b, hb⟩, ⟨r, hr⟩⟩
      change Sum.inr (a, l) = Sum.inr (b, r) at h
      have hh := Prod.mk.inj (Sum.inr.inj h)
      rcases hh with ⟨rfl, rfl⟩
      have hij : i = j := Fin.ext (ha.symm.trans hb)
      subst j
      rfl

def safeSourceCode {g : ℕ} (a : SafeSource g) : SafeCode :=
  if h : 3 ≤ g then safeBodyCode (cast (if_pos h) a) else .inl []

theorem safeSourceCode_weight {g : ℕ} (a : SafeSource g) : (safeSourceCode a).weight = g := by
  have hg := shift_le_of_element a
  rw [safeSourceCode, dif_pos hg, safeBodyCode_weight]
  omega

theorem safeSourceCode_injective (g : ℕ) : Function.Injective (@safeSourceCode g) := by
  intro a b h
  have hg := shift_le_of_element a
  simp only [safeSourceCode, dif_pos hg] at h
  exact (Equiv.cast (if_pos hg)).injective (safeBodyCode_injective _ h)

theorem exists_safeSource (a : SafeCode) :
    ∃ b : SafeSource a.weight, safeSourceCode b = a := by
  have hg : 3 ≤ a.weight := by cases a <;> simp only [SafeCode.weight] <;> omega
  obtain ⟨b, hb⟩ : ∃ b : SafeBody (a.weight - 3), safeBodyCode b = a := by
    cases a with
    | inl l =>
      refine ⟨.inl ⟨l, ?_⟩, rfl⟩
      change (l.map (fun p => uValue p.1 + vValue p.2)).sum = _
      simp only [SafeCode.weight, Nat.add_sub_cancel]
    | inr a =>
      refine ⟨.inr ⟨⟨uValue a.1, ?_⟩, ⟨a.1, rfl⟩, ⟨a.2, ?_⟩⟩, rfl⟩
      · change uValue a.1 < uValue a.1 + (a.2.map (fun p => uValue p.1 + vValue p.2)).sum + 3 - 3 + 1
        omega
      · change (a.2.map (fun p => uValue p.1 + vValue p.2)).sum = _
        simp only [SafeCode.weight]
        change (a.2.map (fun p => uValue p.1 + vValue p.2)).sum =
          uValue a.1 + (a.2.map (fun p => uValue p.1 + vValue p.2)).sum + 3 - 3 - uValue a.1
        omega
  let t : SafeSource a.weight := cast (if_pos hg).symm b
  refine ⟨t, ?_⟩
  have he : cast (if_pos hg) t = b := (cast_cast _ _ b).trans (cast_eq _ b)
  simp only [safeSourceCode, dif_pos hg]
  exact (congrArg safeBodyCode he).trans hb

def safeSourceWord {g : ℕ} (a : SafeSource g) : List ℕ := (safeSourceCode a).decode

theorem safeSourceWord_weight {g : ℕ} (a : SafeSource g) : (safeSourceWord a).sum = g := by
  rw [safeSourceWord, SafeCode.decode_weight, safeSourceCode_weight]

theorem safeSourceWord_injective (g : ℕ) : Function.Injective (@safeSourceWord g) :=
  SafeCode.decode_injective.comp (safeSourceCode_injective g)

def earlyBodyCode {g : ℕ} (a : Graded.Product UUWords UWords g) : EarlyCode :=
  (a.2.1.val, a.2.2.val)

theorem earlyBodyCode_weight {g : ℕ} (a : Graded.Product UUWords UWords g) :
    (earlyBodyCode a).weight = g + 6 := by
  have hi := a.1.isLt
  have hp : (a.2.1.val.map (fun p => uValue p.1 + uValue p.2)).sum = a.1.val := a.2.1.property
  have hs : (a.2.2.val.map uValue).sum = g - a.1.val := a.2.2.property
  change (a.2.1.val.map (fun p => uValue p.1 + uValue p.2)).sum + (a.2.2.val.map uValue).sum + 6 = _
  omega

theorem earlyBodyCode_injective (g : ℕ) : Function.Injective (@earlyBodyCode g) := by
  rintro ⟨i, ⟨l, hl⟩, ⟨s, hs⟩⟩ ⟨j, ⟨r, hr⟩, ⟨t, ht⟩⟩ h
  change (l, s) = (r, t) at h
  rcases Prod.mk.inj h with ⟨rfl, rfl⟩
  have hij : i = j := Fin.ext (hl.symm.trans hr)
  subst j
  rfl

def earlySourceCode {g : ℕ} (a : EarlySource g) : EarlyCode :=
  if h : 6 ≤ g then earlyBodyCode (cast (if_pos h) a) else ([], [])

theorem earlySourceCode_weight {g : ℕ} (a : EarlySource g) : (earlySourceCode a).weight = g := by
  have hg := shift_le_of_element a
  rw [earlySourceCode, dif_pos hg, earlyBodyCode_weight]
  omega

theorem earlySourceCode_injective (g : ℕ) : Function.Injective (@earlySourceCode g) := by
  intro a b h
  have hg := shift_le_of_element a
  simp only [earlySourceCode, dif_pos hg] at h
  exact (Equiv.cast (if_pos hg)).injective (earlyBodyCode_injective _ h)

theorem exists_earlySource (a : EarlyCode) :
    ∃ b : EarlySource a.weight, earlySourceCode b = a := by
  have hg : 6 ≤ a.weight := by simp only [EarlyCode.weight]; omega
  let b : Graded.Product UUWords UWords (a.weight - 6) :=
    ⟨⟨(a.1.map (fun p => uValue p.1 + uValue p.2)).sum, by
      simp only [EarlyCode.weight]
      omega⟩, ⟨a.1, rfl⟩, ⟨a.2, by
      change (a.2.map uValue).sum = a.weight - 6 - (a.1.map (fun p => uValue p.1 + uValue p.2)).sum
      simp only [EarlyCode.weight]
      omega⟩⟩
  let t : EarlySource a.weight := cast (if_pos hg).symm b
  refine ⟨t, ?_⟩
  have he : cast (if_pos hg) t = b := (cast_cast _ _ b).trans (cast_eq _ b)
  simp only [earlySourceCode, dif_pos hg]
  exact congrArg earlyBodyCode he

def earlySourceWord {g : ℕ} (a : EarlySource g) : List ℕ := (earlySourceCode a).decode

theorem earlySourceWord_weight {g : ℕ} (a : EarlySource g) : (earlySourceWord a).sum = g := by
  rw [earlySourceWord, EarlyCode.decode_weight, earlySourceCode_weight]

theorem earlySourceWord_injective (g : ℕ) : Function.Injective (@earlySourceWord g) :=
  EarlyCode.decode_injective.comp (earlySourceCode_injective g)

#print axioms safeSourceWord_injective
#print axioms exists_safeSource
#print axioms earlySourceWord_injective
#print axioms exists_earlySource

end SubmittedGenus.FiniteArithmetic.Reservoir
