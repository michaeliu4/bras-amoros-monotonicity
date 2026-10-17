import Results.Genus.FiniteArithmetic.Reservoir.PrefixCode
import Results.Genus.Injection.FinalOneConstruction
import Results.Genus.Injection.WitnessedTargets
import Results.Genus.Injection.ReservoirSources.TailWitness

/-!
# Physical sources for the original witnessed reservoir

Only the two literal prefix families of the submitted manuscript are used.
Physical positions are one-based; internal list indices are zero-based.
-/
namespace SubmittedGenus.OriginalReservoir
open FiniteArithmetic.Reservoir

/-- The only possible obstruction at depth three is a noncarry pair of ones. -/
def PrefixAdmissible (p : List ℕ) : Prop :=
  (∀ a ∈ p, 1 ≤ a ∧ a ≤ 3) ∧
  ∀ i j : ℕ, (hi : i < p.length) → (hj : j < p.length) →
    p[i] = 1 → p[j] = 1 → (hij : i + j + 1 < p.length) → p[i + j + 1] ≤ 2

/-- A binary tail is literal, including the empty tail. -/
def BinaryTail (t : List ℕ) : Prop := ∀ a ∈ t, a = 1 ∨ a = 2

lemma u_bounds (a : U) : 2 ≤ uValue a ∧ uValue a ≤ 3 := by
  have := a.isLt
  dsimp [uValue]
  omega

lemma v_bounds (a : V) : 1 ≤ vValue a ∧ vValue a ≤ 3 := by
  have := a.isLt
  dsimp [vValue]
  omega

lemma map_u_bounds {A : Type} (f : A → U) (l : List A) :
    ∀ a ∈ l.map (fun b => uValue (f b)), 2 ≤ a ∧ a ≤ 3 := by
  intro a ha
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
  exact u_bounds _

lemma safe_bounds (s : SafeCode) : ∀ a ∈ s.decode, 1 ≤ a ∧ a ≤ 3 := by
  intro a ha
  cases s with
  | inl l =>
    simp only [SafeCode.decode, pairDecode, List.mem_append, List.mem_singleton,
      List.mem_map] at ha
    rcases ha with (⟨b, _, rfl⟩ | ⟨b, _, rfl⟩) | rfl
    · have := u_bounds b.1; omega
    · exact v_bounds _
    · omega
  | inr s =>
    simp only [SafeCode.decode, pairDecode, List.mem_append, List.mem_singleton,
      List.mem_cons, List.mem_map, List.not_mem_nil, or_false] at ha
    rcases ha with (rfl | ⟨b, _, rfl⟩ | ⟨b, _, rfl⟩) | rfl
    · have := u_bounds s.1; omega
    · have := u_bounds b.1; omega
    · exact v_bounds _
    · omega

lemma safe_one_late (s : SafeCode) (i : ℕ) (hi : i < s.decode.length)
    (hone : s.decode[i] = 1) : s.decode.length < 2 * (i + 1) := by
  cases s with
  | inl l =>
    have hn : l.length ≤ i := by
      by_contra h
      have hil : i < (l.map (fun p => uValue p.1)).length := by simp; omega
      have he : (SafeCode.decode (.inl l))[i] = uValue (l[i]'(by omega)).1 := by
        simp only [SafeCode.decode, pairDecode, List.getElem_append_left
          (show i < (l.map (fun p => uValue p.1) ++
            l.map (fun p => vValue p.2)).length by simp; omega),
          List.getElem_append_left hil, List.getElem_map]
      rw [he] at hone
      have := u_bounds (l[i]'(by omega)).1
      omega
    simp only [SafeCode.decode, pairDecode, List.length_append, List.length_map,
      List.length_singleton]
    omega
  | inr s =>
    rcases s with ⟨a,l⟩
    have hn : l.length + 1 ≤ i := by
      by_contra h
      have hil : i < (uValue a :: l.map (fun p => uValue p.1)).length := by simp; omega
      have he : (SafeCode.decode (.inr (a,l)))[i] =
          (uValue a :: l.map (fun p => uValue p.1))[i] := by
        simp only [SafeCode.decode, pairDecode, ← List.cons_append, List.append_assoc,
          List.getElem_append_left hil]
      rw [he] at hone
      have hmem := List.getElem_mem hil
      simp only [List.mem_cons] at hmem
      rcases hmem with hm | hm
      · have := u_bounds a; omega
      · have := map_u_bounds Prod.fst l _ hm; omega
    simp only [SafeCode.decode, pairDecode, List.length_append, List.length_map,
      List.length_cons, List.length_nil]
    omega

lemma safe_admissible (s : SafeCode) : PrefixAdmissible s.decode := by
  refine ⟨safe_bounds s, ?_⟩
  intro i j hi hj hi1 hj1 hij
  have := safe_one_late s i hi hi1
  have := safe_one_late s j hj hj1
  omega

lemma early_bounds (s : EarlyCode) : ∀ a ∈ s.decode, 1 ≤ a ∧ a ≤ 3 := by
  intro a ha
  simp only [EarlyCode.decode, List.mem_append, List.mem_cons, List.mem_singleton,
    List.mem_map, List.not_mem_nil, or_false] at ha
  rcases ha with ⟨b, _, rfl⟩ | rfl | ⟨b, _, rfl⟩ | rfl | ⟨b, _, rfl⟩ | rfl
  · have := u_bounds b.1; omega
  · omega
  · have := u_bounds b.2; omega
  · omega
  · have := u_bounds b; omega
  · omega

lemma early_one_unique (s : EarlyCode) (i : ℕ) (hi : i < s.decode.length)
    (hone : s.decode[i] = 1) : i = s.1.length := by
  by_cases hleft : i < s.1.length
  · have hget : s.decode[i] = uValue (s.1[i]'hleft).1 := by
      unfold EarlyCode.decode
      rw [List.getElem_append_left (by simpa using hleft), List.getElem_map]
    rw [hget] at hone
    have := u_bounds (s.1[i]'hleft).1
    omega
  by_cases heq : i = s.1.length
  · exact heq
  have hright : s.1.length + 1 ≤ i := by omega
  have hbound : i - (s.1.length + 1) <
      (s.1.map (fun p : U × U => uValue p.2) ++ 2 :: (s.2.map uValue ++ [3])).length := by
    simp only [EarlyCode.decode, List.length_append, List.length_map,
      List.length_cons, List.length_nil] at hi ⊢
    omega
  have hget : s.decode[i] =
      (s.1.map (fun p : U × U => uValue p.2) ++ 2 :: (s.2.map uValue ++ [3]))[i - (s.1.length + 1)]'hbound := by
    unfold EarlyCode.decode
    rw [List.getElem_append_right (by simpa using Nat.le_of_not_gt hleft)]
    have hs : i - s.1.length = (i - (s.1.length + 1)) + 1 := by omega
    simp only [List.length_map, hs, List.getElem_cons_succ]
  rw [hget] at hone
  have hm := List.getElem_mem hbound
  simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.mem_map, List.not_mem_nil, or_false] at hm
  rcases hm with ⟨b, _, hb⟩ | hb | ⟨b, _, hb⟩ | hb
  · have := u_bounds b.2; omega
  · omega
  · have := u_bounds b; omega
  · omega

lemma early_double_one (s : EarlyCode) :
    s.decode[2 * s.1.length + 1]'(by simp [EarlyCode.decode]; omega) = 2 := by
  unfold EarlyCode.decode
  rw [List.getElem_append_right (by simp; omega)]
  simp only [List.length_map]
  have hsub : 2 * s.1.length + 1 - s.1.length = s.1.length + 1 := by omega
  simp only [hsub, List.getElem_cons_succ]
  rw [List.getElem_append_right (by simp)]
  simp

lemma early_admissible (s : EarlyCode) : PrefixAdmissible s.decode := by
  refine ⟨early_bounds s, ?_⟩
  intro i j hi hj hi1 hj1 hij
  have hi' := early_one_unique s i hi hi1
  have hj' := early_one_unique s j hj hj1
  have hidx : i + j + 1 = 2 * s.1.length + 1 := by omega
  simpa only [hidx, early_double_one] using (show 2 ≤ 2 by omega)



lemma append_bounds {p t : List ℕ} (hp : PrefixAdmissible p) (ht : BinaryTail t) :
    ∀ a ∈ p ++ t, 1 ≤ a ∧ a ≤ 3 := by
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · exact hp.1 a ha
  · have := ht a ha; omega

/-- Every literal prefix followed by an arbitrary binary tail is valid.
This checks actual positive, noncarry and carry Kunz inequalities. -/
lemma append_valid {p t : List ℕ} (hp : PrefixAdmissible p) (ht : BinaryTail t) :
    KunzWord.Valid (KunzWord.ofList (p ++ t)) := by
  have hb := append_bounds hp ht
  have hcoord (i : ℕ) (hi : 0 < i) (him : i < (p ++ t).length + 1) :
      1 ≤ KunzWord.coord (KunzWord.ofList (p ++ t)) i ∧
        KunzWord.coord (KunzWord.ofList (p ++ t)) i ≤ 3 := by
    rw [KunzWord.coord_ofList_value _ hi (by omega)]
    exact hb _ (List.getElem_mem _)
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact (hb _ (List.getElem_mem (l := p ++ t) (n := i.val)
      (by simpa using i.isLt))).1
  · intro i j hi0 hi hj0 hj hij
    have hbi := hcoord i hi0 hi
    have hbj := hcoord j hj0 hj
    have hbij := hcoord (i+j) (by omega) hij
    by_cases hsmall : KunzWord.coord (KunzWord.ofList (p ++ t)) (i+j) ≤ 2
    · omega
    by_contra hfail
    have hi1 : KunzWord.coord (KunzWord.ofList (p ++ t)) i = 1 := by
      by_contra hn; omega
    have hj1 : KunzWord.coord (KunzWord.ofList (p ++ t)) j = 1 := by
      by_contra hn; omega
    have hprefix : i+j ≤ p.length := by
      by_contra hn
      rw [KunzWord.coord_ofList_value _ (by omega) (by omega),
        List.getElem_append_right (by omega)] at hsmall
      have ht' := ht _ (List.getElem_mem (l := t) (n := i+j-1-p.length) (by
        simp only [List.length_append] at hij; omega))
      omega
    rw [KunzWord.coord_ofList_value _ hi0 (by omega),
      List.getElem_append_left (by omega)] at hi1
    rw [KunzWord.coord_ofList_value _ hj0 (by omega),
      List.getElem_append_left (by omega)] at hj1
    have hs := hp.2 (i-1) (j-1) (by omega) (by omega) hi1 hj1 (by omega)
    have he : i-1 + (j-1) + 1 = i+j-1 := by omega
    simp only [he] at hs
    rw [KunzWord.coord_ofList_value _ (by omega) (by omega),
      List.getElem_append_left (by omega)] at hsmall
    omega
  · intro i j hi0 hi hj0 hj hij
    have hbi := hcoord i hi0 hi
    have hbj := hcoord j hj0 hj
    have hbij := hcoord (i+j-((p++t).length+1)) (by omega) (by omega)
    omega

/-- A genuine numerical-semigroup word made from a physical reservoir base. -/
def baseData (p t : List ℕ) (hp : PrefixAdmissible p) (ht : BinaryTail t) : KunzData :=
  ⟨⟨(p++t).length+1, by omega⟩, ⟨KunzWord.ofList (p++t), append_valid hp ht⟩⟩

@[simp] lemma baseData_toList (p t : List ℕ) (hp : PrefixAdmissible p) (ht : BinaryTail t) :
    (baseData p t hp ht).toList = p ++ t := KunzWord.ofFn_ofList _

lemma baseData_weight (p t : List ℕ) (hp : PrefixAdmissible p) (ht : BinaryTail t) :
    (baseData p t hp ht).weight = p.sum + t.sum := by
  rw [← KunzData.sum_toList, baseData_toList, List.sum_append]

lemma baseData_depth (p t : List ℕ) (hp : PrefixAdmissible p) (ht : BinaryTail t)
    (hthree : 3 ∈ p) : (baseData p t hp ht).depth = 3 := by
  have hle : (baseData p t hp ht).depth ≤ 3 := by
    apply (KunzWord.depth_le_iff _).mpr
    intro i
    exact (append_bounds hp ht _ (List.getElem_mem _)).2
  have hmem : 3 ∈ (baseData p t hp ht).toList := by
    rw [baseData_toList]; exact List.mem_append_left _ hthree
  obtain ⟨i, hi⟩ := (KunzData.mem_toList _ _).mp hmem
  have hge := KunzWord.le_depth (baseData p t hp ht).2.val i
  change _ ≤ (baseData p t hp ht).depth at hge
  omega

/-- The paper's tail equation is exactly a carried `1+1` witness in the
base multiplicity. No implication about unusedness is assumed here. -/
lemma baseData_carryWitnessed (p t : List ℕ) (hp : PrefixAdmissible p)
    (ht : BinaryTail t) (hw : FullyWitnessed p t) :
    OriginalMaps.CarryWitnessed (baseData p t hp ht) := by
  intro i hi0 him hi3
  change i < (p++t).length+1 at him
  change KunzWord.coord (KunzWord.ofList (p++t)) i = 3 at hi3
  rw [KunzWord.coord_ofList_value _ hi0 (by omega)] at hi3
  have hip : i ≤ p.length := by
    by_contra hn
    rw [List.getElem_append_right (by omega)] at hi3
    have := ht _ (List.getElem_mem (l := t) (n := i-1-p.length) (by
      simp only [List.length_append] at him; omega))
    omega
  rw [List.getElem_append_left (by omega)] at hi3
  obtain ⟨j,k,hj,hk,hjk⟩ := hw ⟨i-1, by omega⟩ hi3
  have hjlt := j.isLt
  have hklt := k.isLt
  refine ⟨p.length+j.val+1, p.length+k.val+1, by omega, ?_, by omega, ?_, ?_, ?_, ?_⟩
  · change _ < (p++t).length+1; simp only [List.length_append]; omega
  · change _ < (p++t).length+1; simp only [List.length_append]; omega
  · change KunzWord.coord (KunzWord.ofList (p++t)) _ = 1
    rw [KunzWord.coord_ofList_value _ (by omega) (by simp only [List.length_append]; omega),
      List.getElem_append_right (by omega)]
    simpa only [Nat.add_sub_cancel, Nat.add_sub_cancel_left] using hj
  · change KunzWord.coord (KunzWord.ofList (p++t)) _ = 1
    rw [KunzWord.coord_ofList_value _ (by omega) (by simp only [List.length_append]; omega),
      List.getElem_append_right (by omega)]
    simpa only [Nat.add_sub_cancel, Nat.add_sub_cancel_left] using hk
  · change _ = (p++t).length+1+i
    simp only [List.length_append]
    change (j.val+1)+(k.val+1)+(p.length-1-(i-1))=t.length+1 at hjk
    omega



lemma safe_terminal (s : SafeCode) : ∃ q, s.decode = q ++ [3] := by
  cases s with
  | inl l => exact ⟨_, rfl⟩
  | inr s => exact ⟨_, rfl⟩

lemma early_terminal (s : EarlyCode) : ∃ q, s.decode = q ++ [3] := by
  refine ⟨s.1.map (fun p => uValue p.1) ++ 1 ::
    (s.1.map (fun p => uValue p.2) ++ 2 :: s.2.map uValue), ?_⟩
  simp only [EarlyCode.decode, List.append_assoc, List.cons_append]

lemma early_first_one_value (s : EarlyCode) :
    s.decode[s.1.length]'(by simp [EarlyCode.decode]) = 1 := by
  unfold EarlyCode.decode
  rw [List.getElem_append_right (by simp)]
  simp

/-- The first early `1` lies strictly before any safe-family `1` could lie. -/
lemma safe_early_disjoint (s : SafeCode) (e : EarlyCode) : s.decode ≠ e.decode := by
  intro he
  have hlen := congrArg List.length he
  have hb : e.1.length < s.decode.length := by
    rw [he]; simp [EarlyCode.decode]
  have hv : s.decode[e.1.length]'hb = 1 := by
    simpa only [he] using early_first_one_value e
  have hl := safe_one_late s e.1.length hb hv
  simp only [EarlyCode.decode, List.length_append, List.length_map,
    List.length_cons, List.length_nil] at hlen
  omega

lemma binary_no_three {t : List ℕ} (ht : BinaryTail t) : 3 ∉ t := by
  intro h; have := ht 3 h; omega

/-- In any base, the last `3` identifies the exact prefix/tail cut. -/
lemma terminal_split_unique {p q t u : List ℕ}
    (hp : ∃ p', p = p' ++ [3]) (hq : ∃ q', q = q' ++ [3])
    (ht : BinaryTail t) (hu : BinaryTail u) (h : p ++ t = q ++ u) : p = q ∧ t = u := by
  have hidx := congrArg (fun w : List ℕ => w.reverse.idxOf 3) h
  have htn : 3 ∉ t.reverse := by simpa using binary_no_three ht
  have hun : 3 ∉ u.reverse := by simpa using binary_no_three hu
  obtain ⟨p',hp'⟩ := hp
  obtain ⟨q',hq'⟩ := hq
  simp only [List.reverse_append, List.idxOf_append_of_notMem htn,
    List.idxOf_append_of_notMem hun, hp', hq', List.reverse_singleton,
    List.singleton_append, List.idxOf_cons_self, List.length_reverse, Nat.add_zero] at hidx
  have hlen := congrArg List.length h
  simp only [List.length_append] at hlen
  exact List.append_inj h (by omega)

lemma baseData_injective {p q t u : List ℕ}
    (hp : PrefixAdmissible p) (hq : PrefixAdmissible q) (ht : BinaryTail t) (hu : BinaryTail u)
    (hpt : ∃ p', p = p' ++ [3]) (hqt : ∃ q', q = q' ++ [3])
    (h : baseData p t hp ht = baseData q u hq hu) : p = q ∧ t = u := by
  apply terminal_split_unique hpt hqt ht hu
  simpa only [baseData_toList] using congrArg KunzData.toList h

end SubmittedGenus.OriginalReservoir
