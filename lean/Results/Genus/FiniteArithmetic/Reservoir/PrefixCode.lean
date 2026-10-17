import Results.Genus.FiniteArithmetic.FiniteAtoms
import Mathlib.Data.List.Basic

namespace SubmittedGenus.FiniteArithmetic.Reservoir

abbrev U := Fin 2
abbrev V := Fin 3

def uValue (a : U) : ℕ := a.val + 2
def vValue (a : V) : ℕ := a.val + 1

theorem uValue_injective : Function.Injective uValue := by
  intro a b h
  apply Fin.ext
  dsimp [uValue] at h
  omega

theorem vValue_injective : Function.Injective vValue := by
  intro a b h
  apply Fin.ext
  dsimp [vValue] at h
  omega

/-- Store two independently chosen equal-length blocks as a list of pairs. -/
def pairDecode {A B : Type} (u : A → ℕ) (v : B → ℕ) (l : List (A × B)) : List ℕ :=
  l.map (fun p => u p.1) ++ l.map (fun p => v p.2)

theorem pair_maps_injective {A B : Type} {u : A → ℕ} {v : B → ℕ}
    (hu : Function.Injective u) (hv : Function.Injective v) {l r : List (A × B)}
    (h₁ : l.map (fun p => u p.1) = r.map (fun p => u p.1))
    (h₂ : l.map (fun p => v p.2) = r.map (fun p => v p.2)) : l = r := by
  induction l generalizing r with
  | nil => cases r <;> simp_all
  | cons a l ih =>
    cases r with
    | nil => simp at h₁
    | cons b r =>
      simp only [List.map_cons, List.cons.injEq] at h₁ h₂
      have hab : a = b := Prod.ext (hu h₁.1) (hv h₂.1)
      exact congrArg₂ List.cons hab (ih h₁.2 h₂.2)

theorem pairDecode_injective {A B : Type} {u : A → ℕ} {v : B → ℕ}
    (hu : Function.Injective u) (hv : Function.Injective v) :
    Function.Injective (pairDecode u v) := by
  intro l r h
  have hlen := congrArg List.length h
  simp only [pairDecode, List.length_append, List.length_map] at hlen
  have hp := List.append_inj h (by simp only [List.length_map]; omega)
  exact pair_maps_injective hu hv hp.1 hp.2

theorem pairDecode_sum {A B : Type} (u : A → ℕ) (v : B → ℕ) (l : List (A × B)) :
    (pairDecode u v l).sum = (l.map (fun p => u p.1 + v p.2)).sum := by
  simp only [pairDecode, List.sum_append]
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    omega

/-- Odd/even physical prefix lengths: U^k V^k 3 or U^(k+1) V^k 3. -/
abbrev SafeCode := List (U × V) ⊕ (U × List (U × V))

def SafeCode.decode : SafeCode → List ℕ
  | .inl l => pairDecode uValue vValue l ++ [3]
  | .inr (a, l) => (uValue a :: pairDecode uValue vValue l) ++ [3]

theorem SafeCode.decode_injective : Function.Injective SafeCode.decode := by
  intro a b h
  cases a with
  | inl l =>
    cases b with
    | inl r =>
      exact congrArg Sum.inl (pairDecode_injective uValue_injective vValue_injective
        (List.append_cancel_right h))
    | inr r =>
      have hh := congrArg List.length h
      simp only [SafeCode.decode, pairDecode, List.length_append, List.length_map,
        List.length_cons, List.length_singleton] at hh
      omega
  | inr a =>
    cases b with
    | inl r =>
      have hh := congrArg List.length h
      simp only [SafeCode.decode, pairDecode, List.length_append, List.length_map,
        List.length_cons, List.length_singleton] at hh
      omega
    | inr b =>
      have hh := List.cons.inj (List.append_cancel_right h)
      exact congrArg Sum.inr (Prod.ext (uValue_injective hh.1)
        (pairDecode_injective uValue_injective vValue_injective hh.2))

def SafeCode.weight : SafeCode → ℕ
  | .inl l => (l.map (fun p => uValue p.1 + vValue p.2)).sum + 3
  | .inr (a, l) => uValue a + (l.map (fun p => uValue p.1 + vValue p.2)).sum + 3

theorem SafeCode.decode_weight (a : SafeCode) : a.decode.sum = a.weight := by
  cases a with
  | inl l => simp [decode, weight, pairDecode_sum]
  | inr p => simp [decode, weight, pairDecode_sum, Nat.add_assoc]

/-- Two independently chosen U blocks of length h, then an arbitrary U suffix. -/
abbrev EarlyCode := List (U × U) × List U

def EarlyCode.decode (a : EarlyCode) : List ℕ :=
  a.1.map (fun p => uValue p.1) ++ 1 ::
    (a.1.map (fun p => uValue p.2) ++ 2 :: (a.2.map uValue ++ [3]))

theorem uMap_no_one {A : Type} (f : A → U) (l : List A) :
    1 ∉ l.map (fun a => uValue (f a)) := by
  intro h
  obtain ⟨a, _, ha⟩ := List.mem_map.mp h
  dsimp [uValue] at ha
  omega

theorem EarlyCode.first_one (a : EarlyCode) : a.decode.idxOf 1 = a.1.length := by
  unfold decode
  rw [List.idxOf_append_of_notMem (uMap_no_one Prod.fst a.1)]
  simp

theorem EarlyCode.decode_injective : Function.Injective EarlyCode.decode := by
  intro a b h
  have hlen : a.1.length = b.1.length := by
    have hh := congrArg (List.idxOf 1) h
    simpa only [first_one] using hh
  have hfirst := List.append_inj h (by simpa only [List.length_map] using hlen)
  have hsecond := List.append_inj (List.cons.inj hfirst.2).2
    (by simpa only [List.length_map] using hlen)
  apply Prod.ext
  · exact pair_maps_injective uValue_injective uValue_injective hfirst.1 hsecond.1
  · exact List.map_injective_iff.mpr uValue_injective
      (List.append_cancel_right (List.cons.inj hsecond.2).2)

def EarlyCode.weight (a : EarlyCode) : ℕ :=
  (a.1.map (fun p => uValue p.1 + uValue p.2)).sum + (a.2.map uValue).sum + 6

theorem EarlyCode.decode_weight (a : EarlyCode) : a.decode.sum = a.weight := by
  have hp := pairDecode_sum uValue uValue a.1
  simp only [pairDecode, List.sum_append] at hp
  simp only [decode, weight, List.sum_append, List.sum_cons, List.sum_nil]
  omega

#print axioms SafeCode.decode_injective
#print axioms EarlyCode.decode_injective
#print axioms EarlyCode.decode_weight

end SubmittedGenus.FiniteArithmetic.Reservoir
