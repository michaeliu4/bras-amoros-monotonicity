import Results.Genus.Injection.ReservoirSources.DecoratedPresentations
import Results.Genus.Injection.ReservoirSources.MarkedOccurrences
import Results.Genus.FiniteArithmetic.Reservoir.MarkedSeries

noncomputable section
namespace SubmittedGenus.FiniteArithmetic.Reservoir
set_option synthInstance.maxSize 4000

abbrev SafeRawV := Unit × (Option U × (U × (List (U×V) × List (U×V))))
abbrev SafeRawU := Unit × (Option U × (V × (List (U×V) × List (U×V))))
abbrev SafeRawLeading := Unit × List (U×V)
abbrev SafeMarkedRaw := SafeCode ⊕ (SafeRawV ⊕ (SafeRawU ⊕ SafeRawLeading))

abbrev EarlyRawSuffix := Unit × (List (U×U) × (List U × List U))
abbrev EarlyRawSecond := Unit × (U × (List (U×U) × (List (U×U) × List U)))
abbrev EarlyRawFirst := EarlyRawSecond
abbrev EarlyMarkedRaw := EarlyCode ⊕ (EarlyRawSuffix ⊕ (EarlyRawSecond ⊕ EarlyRawFirst))

def safeRawEquiv : SafeMarkedRaw ≃ SafeMarkedCode where
  toFun
    | .inl a => .terminal a
    | .inr (.inl (_,a,mate,pre,post)) => .vmark a pre mate post
    | .inr (.inr (.inl (_,a,mate,pre,post))) => .umark a pre mate post
    | .inr (.inr (.inr (_,pairs))) => .leading pairs
  invFun
    | .terminal a => .inl a
    | .vmark a pre mate post => .inr (.inl ((),a,mate,pre,post))
    | .umark a pre mate post => .inr (.inr (.inl ((),a,mate,pre,post)))
    | .leading pairs => .inr (.inr (.inr ((),pairs)))
  left_inv a := by
    rcases a with a | ⟨⟨⟩,a,mate,pre,post⟩ | ⟨⟨⟩,a,mate,pre,post⟩ | ⟨⟨⟩,pairs⟩ <;> rfl
  right_inv a := by cases a <;> rfl

def earlyRawEquiv : EarlyMarkedRaw ≃ EarlyMarkedCode where
  toFun
    | .inl a => .terminal a
    | .inr (.inl (_,pairs,pre,post)) => .suffix pairs pre post
    | .inr (.inr (.inl (_,mate,pre,post,tail))) => .second pre mate post tail
    | .inr (.inr (.inr (_,mate,pre,post,tail))) => .first pre mate post tail
  invFun
    | .terminal a => .inl a
    | .suffix pairs pre post => .inr (.inl ((),pairs,pre,post))
    | .second pre mate post tail => .inr (.inr (.inl ((),mate,pre,post,tail)))
    | .first pre mate post tail => .inr (.inr (.inr ((),mate,pre,post,tail)))
  left_inv a := by
    rcases a with a | ⟨⟨⟩,pairs,pre,post⟩ | ⟨⟨⟩,mate,pre,post,tail⟩ |
      ⟨⟨⟩,mate,pre,post,tail⟩ <;> rfl
  right_inv a := by cases a <;> rfl

def dpU (D : Decoration) : DecoratedPresentation D UAtoms U :=
  DecoratedPresentation.plain D (atomPresentation uValue)
def dpV (D : Decoration) : DecoratedPresentation D VAtoms V :=
  DecoratedPresentation.plain D (atomPresentation vValue)
def dpOptional (D : Decoration) : DecoratedPresentation D OptionalUAtoms (Option U) :=
  DecoratedPresentation.plain D (atomPresentation optionalWeight)
def dpWU (D : Decoration) (k : ℕ) : DecoratedPresentation D (DWU D k) (List U) :=
  DecoratedPresentation.words D uValue (by intro a; dsimp [uValue]; omega) k
def dpWUV (D : Decoration) (k : ℕ) : DecoratedPresentation D (DWUV D k) (List (U×V)) :=
  DecoratedPresentation.words D (fun p : U×V => uValue p.1+vValue p.2)
    (by intro a; dsimp [uValue,vValue]; omega) k
def dpWUU (D : Decoration) (k : ℕ) : DecoratedPresentation D (DWUU D k) (List (U×U)) :=
  DecoratedPresentation.words D (fun p : U×U => uValue p.1+uValue p.2)
    (by intro a; dsimp [uValue]; omega) k

def safeVDP (D : Decoration) : DecoratedPresentation D (SafeVSource D) SafeRawV :=
  ((DecoratedPresentation.slots D 1).product
    ((dpOptional D).product ((dpU D).product ((dpWUV D 0).product (dpWUV D 1))))).shift 6

def safeUDP (D : Decoration) : DecoratedPresentation D (SafeUSource D) SafeRawU :=
  ((DecoratedPresentation.slots D 2).product
    ((dpOptional D).product ((dpV D).product ((dpWUV D 1).product (dpWUV D 2))))).shift 6

def safeLeadingDP (D : Decoration) : DecoratedPresentation D (SafeLeadingSource D) SafeRawLeading :=
  ((DecoratedPresentation.slots D 1).product (dpWUV D 2)).shift 6

def safeMarkedDP (D : Decoration) : DecoratedPresentation D (SafeMarkedSource D) SafeMarkedRaw :=
  (DecoratedPresentation.plain D safePresentation).sum
    ((safeVDP D).sum ((safeUDP D).sum (safeLeadingDP D)))

def earlySuffixDP (D : Decoration) : DecoratedPresentation D (EarlySuffixSource D) EarlyRawSuffix :=
  ((DecoratedPresentation.slots D 1).product
    ((dpWUU D 0).product ((dpWU D 0).product (dpWU D 1)))).shift 9

def earlySecondDP (D : Decoration) : DecoratedPresentation D (EarlySecondSource D) EarlyRawSecond :=
  ((DecoratedPresentation.slots D 2).product
    ((dpU D).product ((dpWUU D 0).product ((dpWUU D 1).product (dpWU D 1))))).shift 9

def earlyFirstDP (D : Decoration) : DecoratedPresentation D (EarlyFirstSource D) EarlyRawFirst :=
  ((DecoratedPresentation.slots D 4).product
    ((dpU D).product ((dpWUU D 1).product ((dpWUU D 2).product (dpWU D 1))))).shift 9

def earlyMarkedDP (D : Decoration) : DecoratedPresentation D (EarlyMarkedSource D) EarlyMarkedRaw :=
  (DecoratedPresentation.plain D earlyPresentation).sum
    ((earlySuffixDP D).sum ((earlySecondDP D).sum (earlyFirstDP D)))

lemma safeMarkedDP_weight (D : Decoration) (a : SafeMarkedRaw) :
    (safeRawEquiv a).prefix.weight=(safeMarkedDP D).layout.weight a := by
  rcases a with a | ⟨⟨⟩,a,mate,pre,post⟩ | ⟨⟨⟩,a,mate,pre,post⟩ | ⟨⟨⟩,pairs⟩
  · rfl
  · change (SafeMarkedCode.vmark a pre mate post).prefix.weight=
      0+(optionalWeight a+(uValue mate+(uvWeight pre+uvWeight post)))+6
    rw [safe_vmark_weight]
    omega
  · change (SafeMarkedCode.umark a pre mate post).prefix.weight=
      0+(optionalWeight a+(vValue mate+(uvWeight pre+uvWeight post)))+6
    rw [safe_umark_weight]
    omega
  · change (SafeMarkedCode.leading pairs).prefix.weight=0+uvWeight pairs+6
    rw [safe_leading_weight]
    omega

lemma earlyMarkedDP_weight (D : Decoration) (a : EarlyMarkedRaw) :
    (earlyRawEquiv a).prefix.weight=(earlyMarkedDP D).layout.weight a := by
  rcases a with a | ⟨⟨⟩,pairs,pre,post⟩ | ⟨⟨⟩,mate,pre,post,tail⟩ | ⟨⟨⟩,mate,pre,post,tail⟩
  · rfl
  · change (EarlyMarkedCode.suffix pairs pre post).prefix.weight=
      0+(uuWeight pairs+(uWeight pre+uWeight post))+9
    rw [early_suffix_weight]
    omega
  · change (EarlyMarkedCode.second pre mate post tail).prefix.weight=
      0+(uValue mate+(uuWeight pre+(uuWeight post+uWeight tail)))+9
    rw [early_second_weight]
    omega
  · change (EarlyMarkedCode.first pre mate post tail).prefix.weight=
      0+(uValue mate+(uuWeight pre+(uuWeight post+uWeight tail)))+9
    rw [early_first_weight]
    omega

lemma safeMarkedDP_distance (D : Decoration) (a : SafeMarkedRaw) :
    Fintype.card ((safeMarkedDP D).layout.Index a)=(safeRawEquiv a).split.after.length := by
  rcases a with a | ⟨⟨⟩,a,mate,pre,post⟩ | ⟨⟨⟩,a,mate,pre,post⟩ | ⟨⟨⟩,pairs⟩
  · change Fintype.card (Fin 0)=0
    simp
  · change Fintype.card (Fin 1 ⊕ (Fin 0 ⊕ (Fin 0 ⊕
      ((Fin pre.length×Fin 0) ⊕ (Fin post.length×Fin 1)))))=_
    change _=(SafeMarkedCode.vmark a pre mate post).split.after.length
    rw [safe_vmark_distance]
    simp [Nat.add_comm]
  · change Fintype.card (Fin 2 ⊕ (Fin 0 ⊕ (Fin 0 ⊕
      ((Fin pre.length×Fin 1) ⊕ (Fin post.length×Fin 2)))))=_
    change _=(SafeMarkedCode.umark a pre mate post).split.after.length
    rw [safe_umark_distance]
    simp
    omega
  · change Fintype.card (Fin 1 ⊕ (Fin pairs.length×Fin 2))=_
    change _=(SafeMarkedCode.leading pairs).split.after.length
    rw [safe_leading_distance]
    simp
    omega

lemma earlyMarkedDP_distance (D : Decoration) (a : EarlyMarkedRaw) :
    Fintype.card ((earlyMarkedDP D).layout.Index a)=(earlyRawEquiv a).split.after.length := by
  rcases a with a | ⟨⟨⟩,pairs,pre,post⟩ | ⟨⟨⟩,mate,pre,post,tail⟩ | ⟨⟨⟩,mate,pre,post,tail⟩
  · change Fintype.card (Fin 0)=0
    simp
  · change Fintype.card (Fin 1 ⊕ ((Fin pairs.length×Fin 0) ⊕
      ((Fin pre.length×Fin 0) ⊕ (Fin post.length×Fin 1))))=_
    change _=(EarlyMarkedCode.suffix pairs pre post).split.after.length
    rw [early_suffix_distance]
    simp [Nat.add_comm]
  · change Fintype.card (Fin 2 ⊕ (Fin 0 ⊕ ((Fin pre.length×Fin 0) ⊕
      ((Fin post.length×Fin 1) ⊕ (Fin tail.length×Fin 1)))))=_
    change _=(EarlyMarkedCode.second pre mate post tail).split.after.length
    rw [early_second_distance]
    simp
    omega
  · change Fintype.card (Fin 4 ⊕ (Fin 0 ⊕ ((Fin pre.length×Fin 1) ⊕
      ((Fin post.length×Fin 2) ⊕ (Fin tail.length×Fin 1)))))=_
    change _=(EarlyMarkedCode.first pre mate post tail).split.after.length
    rw [early_first_distance]
    simp
    omega

/-- Exact original decorated safe-prefix grammar, now tied to actual marks. -/
def safeMarkedPresentation (D : Decoration) :
    Presentation (SafeMarkedSource D) (Σm:SafeMarkedCode,Fin m.split.after.length→D.Letter) :=
  (safeMarkedDP D).reindex safeRawEquiv (fun m => m.split.after.length) (fun m => m.prefix.weight)
    (safeMarkedDP_distance D) (safeMarkedDP_weight D)

/-- Exact original decorated early-prefix grammar, now tied to actual marks. -/
def earlyMarkedPresentation (D : Decoration) :
    Presentation (EarlyMarkedSource D) (Σm:EarlyMarkedCode,Fin m.split.after.length→D.Letter) :=
  (earlyMarkedDP D).reindex earlyRawEquiv (fun m => m.split.after.length) (fun m => m.prefix.weight)
    (earlyMarkedDP_distance D) (earlyMarkedDP_weight D)

#print axioms safeMarkedPresentation
#print axioms earlyMarkedPresentation
end SubmittedGenus.FiniteArithmetic.Reservoir
