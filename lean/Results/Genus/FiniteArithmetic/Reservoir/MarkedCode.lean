import Results.Genus.FiniteArithmetic.Reservoir.PrefixCode

namespace SubmittedGenus.FiniteArithmetic.Reservoir

abbrev uThree : U := 1
abbrev vThree : V := 2

def optionalU (a : Option U) : List ℕ := a.toList.map uValue

def safeFromOption (a : Option U) (l : List (U × V)) : SafeCode :=
  match a with | none => .inl l | some a => .inr (a,l)

theorem safeFromOption_decode (a : Option U) (l : List (U × V)) :
    (safeFromOption a l).decode = optionalU a ++ pairDecode uValue vValue l ++ [3] := by
  cases a <;> rfl

def safeBodyWord : SafeCode → List ℕ
  | .inl l => pairDecode uValue vValue l
  | .inr (a,l) => uValue a :: pairDecode uValue vValue l

theorem safeBodyWord_append (a : SafeCode) : a.decode = safeBodyWord a ++ [3] := by
  cases a <;> rfl

def earlyBodyWord (a : EarlyCode) : List ℕ :=
  a.1.map (uValue ∘ Prod.fst) ++ 1 ::
    (a.1.map (uValue ∘ Prod.snd) ++ 2 :: a.2.map uValue)

theorem earlyBodyWord_append (a : EarlyCode) : a.decode = earlyBodyWord a ++ [3] := by
  simp [EarlyCode.decode, earlyBodyWord, List.append_assoc, Function.comp_def]

/-- A marked occurrence is represented by its actual left and right physical
sublists. Thus multiplicity and distance are retained independently of counts. -/
structure SplitMark where
  before : List ℕ
  after : List ℕ

def SplitMark.word (m : SplitMark) : List ℕ := m.before ++ 3 :: m.after

def SplitMark.index (m : SplitMark) : Fin m.word.length :=
  ⟨m.before.length, by simp [word]⟩

@[simp] theorem SplitMark.value (m : SplitMark) : m.word[m.index.val] = 3 := by
  simp [index, word]

@[simp] theorem SplitMark.distance (m : SplitMark) :
    m.word.length - 1 - m.index.val = m.after.length := by
  simp [index, word]

inductive SafeMarkedCode where
  | terminal (a : SafeCode)
  | vmark (a : Option U) (pre : List (U×V)) (mate : U) (post : List (U×V))
  | umark (a : Option U) (pre : List (U×V)) (mate : V) (post : List (U×V))
  | leading (pairs : List (U×V))

def SafeMarkedCode.prefix : SafeMarkedCode → SafeCode
  | .terminal a => a
  | .vmark a pre mate post => safeFromOption a (pre ++ (mate,vThree) :: post)
  | .umark a pre mate post => safeFromOption a (pre ++ (uThree,mate) :: post)
  | .leading pairs => .inr (uThree,pairs)

def SafeMarkedCode.split : SafeMarkedCode → SplitMark
  | .terminal a => ⟨safeBodyWord a, []⟩
  | .vmark a pre mate post =>
    ⟨optionalU a ++ (pre ++ (mate,vThree)::post).map (uValue ∘ Prod.fst) ++
      pre.map (vValue ∘ Prod.snd), post.map (vValue ∘ Prod.snd) ++ [3]⟩
  | .umark a pre mate post =>
    ⟨optionalU a ++ pre.map (uValue ∘ Prod.fst),
      post.map (uValue ∘ Prod.fst) ++
        (pre ++ (uThree,mate)::post).map (vValue ∘ Prod.snd) ++ [3]⟩
  | .leading pairs => ⟨[], pairDecode uValue vValue pairs ++ [3]⟩

theorem SafeMarkedCode.word_eq (m : SafeMarkedCode) : m.split.word = m.prefix.decode := by
  cases m with
  | terminal a => simpa [split, SafeMarkedCode.prefix, SplitMark.word] using (safeBodyWord_append a).symm
  | vmark a pre mate post =>
    simp [split, SafeMarkedCode.prefix, safeFromOption_decode, SplitMark.word, pairDecode,
      List.map_append, List.append_assoc, vThree, vValue, Function.comp_def]
  | umark a pre mate post =>
    simp [split, SafeMarkedCode.prefix, safeFromOption_decode, SplitMark.word, pairDecode,
      List.map_append, List.append_assoc, uThree, uValue, Function.comp_def]
  | leading pairs => rfl

inductive EarlyMarkedCode where
  | terminal (a : EarlyCode)
  | suffix (pairs : List (U×U)) (pre post : List U)
  | second (pre : List (U×U)) (mate : U) (post : List (U×U)) (suffix : List U)
  | first (pre : List (U×U)) (mate : U) (post : List (U×U)) (suffix : List U)

def EarlyMarkedCode.prefix : EarlyMarkedCode → EarlyCode
  | .terminal a => a
  | .suffix pairs pre post => (pairs, pre ++ uThree :: post)
  | .second pre mate post tail => (pre ++ (mate,uThree)::post, tail)
  | .first pre mate post tail => (pre ++ (uThree,mate)::post, tail)

def EarlyMarkedCode.split : EarlyMarkedCode → SplitMark
  | .terminal a => ⟨earlyBodyWord a, []⟩
  | .suffix pairs pre post =>
    ⟨pairs.map (uValue ∘ Prod.fst) ++ 1 ::
      (pairs.map (uValue ∘ Prod.snd) ++ 2 :: pre.map uValue), post.map uValue ++ [3]⟩
  | .second pre mate post tail =>
    ⟨(pre ++ (mate,uThree)::post).map (uValue ∘ Prod.fst) ++ 1 ::
      pre.map (uValue ∘ Prod.snd),
      post.map (uValue ∘ Prod.snd) ++ 2 :: (tail.map uValue ++ [3])⟩
  | .first pre mate post tail =>
    ⟨pre.map (uValue ∘ Prod.fst), post.map (uValue ∘ Prod.fst) ++ 1 ::
      ((pre ++ (uThree,mate)::post).map (uValue ∘ Prod.snd) ++ 2 :: (tail.map uValue ++ [3]))⟩

theorem EarlyMarkedCode.word_eq (m : EarlyMarkedCode) : m.split.word = m.prefix.decode := by
  cases m with
  | terminal a => simpa [split, EarlyMarkedCode.prefix, SplitMark.word] using (earlyBodyWord_append a).symm
  | suffix pairs pre post =>
    simp [split, EarlyMarkedCode.prefix, SplitMark.word, EarlyCode.decode,
      List.map_append, List.append_assoc, uThree, uValue, Function.comp_def]
  | second pre mate post tail =>
    simp [split, EarlyMarkedCode.prefix, SplitMark.word, EarlyCode.decode,
      List.map_append, List.append_assoc, uThree, uValue, Function.comp_def]
  | first pre mate post tail =>
    simp [split, EarlyMarkedCode.prefix, SplitMark.word, EarlyCode.decode,
      List.map_append, List.append_assoc, uThree, uValue, Function.comp_def]

#print axioms SafeMarkedCode.word_eq
#print axioms EarlyMarkedCode.word_eq
end SubmittedGenus.FiniteArithmetic.Reservoir
