import Results.Genus.FiniteArithmetic.LocallyFiniteWords

/-!
# Reflection blocks are genuine words

An outer ordered pair is stored once, with one weight for each of its two
physical coordinates. A possible central singleton is stored once. The encoder
is proved bijective onto the recursive reflection language; no coefficient
identity substitutes for this source correspondence.
-/

namespace SubmittedGenus.FiniteArithmetic.Reflection

abbrev Pair (P : ℕ → ℕ → Prop) := {ab : ℕ × ℕ // P ab.1 ab.2}
abbrev Center (C : ℕ → Prop) := {a : ℕ // C a}
abbrev Code (P : ℕ → ℕ → Prop) (C : ℕ → Prop) := List (Pair P) × Option (Center C)

def centerWord {C : ℕ → Prop} : Option (Center C) → List ℕ
  | none => []
  | some a => [a.val]

def decodePairs {P : ℕ → ℕ → Prop} {C : ℕ → Prop}
    (pairs : List (Pair P)) (center : Option (Center C)) : List ℕ :=
  match pairs with
  | [] => centerWord center
  | p :: ps => p.val.1 :: (decodePairs ps center ++ [p.val.2])

def decode {P : ℕ → ℕ → Prop} {C : ℕ → Prop} (code : Code P C) : List ℕ :=
  decodePairs code.1 code.2

theorem centerWord_length_le {C : ℕ → Prop} (c : Option (Center C)) :
    (centerWord c).length ≤ 1 := by cases c <;> simp [centerWord]

theorem decodePairs_length {P : ℕ → ℕ → Prop} {C : ℕ → Prop}
    (ps : List (Pair P)) (c : Option (Center C)) :
    (decodePairs ps c).length = 2 * ps.length + (centerWord c).length := by
  induction ps with
  | nil => simp [decodePairs]
  | cons p ps ih => simp [decodePairs, ih]; omega

theorem centerWord_injective {C : ℕ → Prop} : Function.Injective (centerWord (C := C)) := by
  intro a b h
  cases a <;> cases b <;> simp_all [centerWord, Subtype.ext_iff]

/-- The physical list recovers every ordered pair and the optional center. -/
theorem decode_injective {P : ℕ → ℕ → Prop} {C : ℕ → Prop} :
    Function.Injective (decode (P := P) (C := C)) := by
  rintro ⟨ps, c⟩ ⟨qs, d⟩ h
  change decodePairs ps c = decodePairs qs d at h
  induction ps generalizing qs with
  | nil =>
    cases qs with
    | nil =>
      have := centerWord_injective h
      simp_all
    | cons q qs =>
      have hl := congrArg List.length h
      rw [decodePairs_length, decodePairs_length] at hl
      have := centerWord_length_le c
      simp only [List.length_nil, List.length_cons] at hl
      omega
  | cons p ps ih =>
    cases qs with
    | nil =>
      have hl := congrArg List.length h
      rw [decodePairs_length, decodePairs_length] at hl
      have := centerWord_length_le d
      simp only [List.length_nil, List.length_cons] at hl
      omega
    | cons q qs =>
      simp only [decodePairs, List.cons.injEq] at h
      obtain ⟨hinner, hright⟩ := List.append_inj' h.2 (by simp)
      have hp : p = q := by
        apply Subtype.ext
        apply Prod.ext h.1
        simpa using hright
      have hi := ih qs hinner
      cases hi
      simp [hp]

/-- Recursive form of the exact reflection constraints. -/
inductive Language (P : ℕ → ℕ → Prop) (C : ℕ → Prop) : List ℕ → Prop
  | nil : Language P C []
  | singleton (a : ℕ) (ha : C a) : Language P C [a]
  | pair (a b : ℕ) (w : List ℕ) (hab : P a b) (hw : Language P C w) :
      Language P C (a :: (w ++ [b]))

theorem decode_mem_language {P : ℕ → ℕ → Prop} {C : ℕ → Prop} (code : Code P C) :
    Language P C (decode code) := by
  rcases code with ⟨ps, c⟩
  induction ps with
  | nil =>
    cases c with
    | none => exact Language.nil
    | some a => exact Language.singleton a.val a.property
  | cons p ps ih => exact Language.pair _ _ _ p.property ih

theorem language_has_code {P : ℕ → ℕ → Prop} {C : ℕ → Prop} {w : List ℕ}
    (h : Language P C w) : ∃ code : Code P C, decode code = w := by
  induction h with
  | nil => exact ⟨⟨[], none⟩, rfl⟩
  | singleton a ha => exact ⟨⟨[], some ⟨a, ha⟩⟩, rfl⟩
  | pair a b w hab hw ih =>
    obtain ⟨⟨ps, c⟩, he⟩ := ih
    exact ⟨⟨⟨(a, b), hab⟩ :: ps, c⟩, by simp [decode, decodePairs] at he ⊢; rw [he]⟩

noncomputable def codeEquivLanguage (P : ℕ → ℕ → Prop) (C : ℕ → Prop) :
    Code P C ≃ {w : List ℕ // Language P C w} :=
  Equiv.ofBijective (fun code => ⟨decode code, decode_mem_language code⟩) (by
    constructor
    · intro a b h
      exact decode_injective (congrArg Subtype.val h)
    · rintro ⟨w, hw⟩
      obtain ⟨code, he⟩ := language_has_code hw
      exact ⟨code, Subtype.ext he⟩)

def pairWeight {P : ℕ → ℕ → Prop} (p : Pair P) : ℕ := p.val.1 + p.val.2

def centerWeight {C : ℕ → Prop} : Option (Center C) → ℕ
  | none => 0
  | some a => a.val

theorem decode_weight {P : ℕ → ℕ → Prop} {C : ℕ → Prop} (ps : List (Pair P))
    (c : Option (Center C)) :
    (decodePairs ps c).sum = (ps.map pairWeight).sum + centerWeight c := by
  induction ps with
  | nil => cases c <;> simp [decodePairs, centerWord, centerWeight]
  | cons p ps ih =>
    simp [decodePairs, ih, pairWeight]
    omega

#print axioms decode_injective
#print axioms codeEquivLanguage
#print axioms decode_weight

end SubmittedGenus.FiniteArithmetic.Reflection
