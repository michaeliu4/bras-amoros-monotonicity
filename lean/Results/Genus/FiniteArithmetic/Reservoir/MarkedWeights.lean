import Results.Genus.FiniteArithmetic.Reservoir.MarkedCode

namespace SubmittedGenus.FiniteArithmetic.Reservoir

def optionalWeight : Option U → ℕ | none => 0 | some a => uValue a
abbrev uvWeight (l : List (U×V)) := (l.map (fun p => uValue p.1+vValue p.2)).sum
abbrev uuWeight (l : List (U×U)) := (l.map (fun p => uValue p.1+uValue p.2)).sum
abbrev uWeight (l : List U) := (l.map uValue).sum

theorem safe_vmark_weight (a : Option U) (pre : List (U×V)) (mate : U) (post : List (U×V)) :
    (SafeMarkedCode.vmark a pre mate post).prefix.weight =
      6 + optionalWeight a + uvWeight pre + uValue mate + uvWeight post := by
  cases a <;> simp [SafeMarkedCode.prefix, safeFromOption, SafeCode.weight,
    optionalWeight, uvWeight, List.map_append, vThree, vValue] <;> omega

theorem safe_umark_weight (a : Option U) (pre : List (U×V)) (mate : V) (post : List (U×V)) :
    (SafeMarkedCode.umark a pre mate post).prefix.weight =
      6 + optionalWeight a + uvWeight pre + vValue mate + uvWeight post := by
  cases a <;> simp [SafeMarkedCode.prefix, safeFromOption, SafeCode.weight,
    optionalWeight, uvWeight, List.map_append, uThree, uValue] <;> omega

theorem safe_leading_weight (pairs : List (U×V)) :
    (SafeMarkedCode.leading pairs).prefix.weight = 6 + uvWeight pairs := by
  simp [SafeMarkedCode.prefix, SafeCode.weight, uvWeight, uThree, uValue]
  omega

theorem safe_vmark_distance (a : Option U) (pre : List (U×V)) (mate : U) (post : List (U×V)) :
    (SafeMarkedCode.vmark a pre mate post).split.after.length = post.length+1 := by
  simp [SafeMarkedCode.split]

theorem safe_umark_distance (a : Option U) (pre : List (U×V)) (mate : V) (post : List (U×V)) :
    (SafeMarkedCode.umark a pre mate post).split.after.length = pre.length+2*post.length+2 := by
  simp [SafeMarkedCode.split]
  omega

theorem safe_leading_distance (pairs : List (U×V)) :
    (SafeMarkedCode.leading pairs).split.after.length = 2*pairs.length+1 := by
  simp [SafeMarkedCode.split, pairDecode]
  omega

theorem early_suffix_weight (pairs : List (U×U)) (pre post : List U) :
    (EarlyMarkedCode.suffix pairs pre post).prefix.weight = 9 + uuWeight pairs + uWeight pre + uWeight post := by
  simp [EarlyMarkedCode.prefix, EarlyCode.weight, uuWeight, uWeight, List.map_append, uThree, uValue]
  omega

theorem early_second_weight (pre : List (U×U)) (mate : U) (post : List (U×U)) (tail : List U) :
    (EarlyMarkedCode.second pre mate post tail).prefix.weight =
      9 + uuWeight pre + uValue mate + uuWeight post + uWeight tail := by
  simp [EarlyMarkedCode.prefix, EarlyCode.weight, uuWeight, uWeight, List.map_append, uThree, uValue]
  omega

theorem early_first_weight (pre : List (U×U)) (mate : U) (post : List (U×U)) (tail : List U) :
    (EarlyMarkedCode.first pre mate post tail).prefix.weight =
      9 + uuWeight pre + uValue mate + uuWeight post + uWeight tail := by
  simp [EarlyMarkedCode.prefix, EarlyCode.weight, uuWeight, uWeight, List.map_append, uThree, uValue]
  omega

theorem early_suffix_distance (pairs : List (U×U)) (pre post : List U) :
    (EarlyMarkedCode.suffix pairs pre post).split.after.length = post.length+1 := by
  simp [EarlyMarkedCode.split]

theorem early_second_distance (pre : List (U×U)) (mate : U) (post : List (U×U)) (tail : List U) :
    (EarlyMarkedCode.second pre mate post tail).split.after.length = post.length+tail.length+2 := by
  simp [EarlyMarkedCode.split]
  omega

theorem early_first_distance (pre : List (U×U)) (mate : U) (post : List (U×U)) (tail : List U) :
    (EarlyMarkedCode.first pre mate post tail).split.after.length = pre.length+2*post.length+tail.length+4 := by
  simp [EarlyMarkedCode.split]
  omega

#print axioms safe_vmark_weight
#print axioms early_first_distance
end SubmittedGenus.FiniteArithmetic.Reservoir
