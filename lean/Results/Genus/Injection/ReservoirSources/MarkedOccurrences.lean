import Results.Genus.FiniteArithmetic.Reservoir.MarkedCode
import Results.Genus.Injection.ReservoirSources.MarkedFailures

noncomputable section
namespace SubmittedGenus.FiniteArithmetic.Reservoir

/-- An actual code and physical occurrence, without marking multiplicity loss. -/
abbrev CodeOccurrence {C : Type} (decode : C → List ℕ) :=
  {p : C × ℕ // ∃ h : p.2 < (decode p.1).length, (decode p.1)[p.2]'h=3}

lemma splitMark_lt (m : SplitMark) : m.before.length < m.word.length := by
  simp [SplitMark.word]

lemma splitMark_value (m : SplitMark) : m.word[m.before.length]'(splitMark_lt m)=3 := by
  simp [SplitMark.word]

lemma safeFromOption_inj {a b : Option U} {l r : List (U×V)} :
    safeFromOption a l = safeFromOption b r ↔ a=b ∧ l=r := by
  cases a <;> cases b <;> simp [safeFromOption]

lemma marked_list_unique {A : Type} {l r l' r' : List A} {a b : A}
    (h : l++a::r=l'++b::r') (hlen : l.length=l'.length) :
    l=l' ∧ a=b ∧ r=r' := by
  have he := List.append_inj h hlen
  exact ⟨he.1,(List.cons.inj he.2).1,(List.cons.inj he.2).2⟩

def SafeMarkedCode.occurrence (m : SafeMarkedCode) : CodeOccurrence SafeCode.decode :=
  ⟨(m.prefix,m.split.before.length),by
    have he := m.word_eq
    refine ⟨by rw [←he]; exact splitMark_lt m.split,?_⟩
    simpa only [he] using splitMark_value m.split⟩

lemma safe_mark_after_length {a b : SafeMarkedCode}
    (hp : a.prefix=b.prefix) (hi : a.split.before.length=b.split.before.length) :
    a.split.after.length=b.split.after.length := by
  have ha := congrArg List.length a.word_eq
  have hb := congrArg List.length b.word_eq
  simp only [SplitMark.word,List.length_append,List.length_cons,hp] at ha hb
  omega

lemma SafeMarkedCode.occurrence_injective : Function.Injective SafeMarkedCode.occurrence := by
  intro a b h
  have hp := congrArg (fun x : CodeOccurrence SafeCode.decode => x.val.1) h
  have hi := congrArg (fun x : CodeOccurrence SafeCode.decode => x.val.2) h
  change a.prefix=b.prefix at hp
  change a.split.before.length=b.split.before.length at hi
  have ht := safe_mark_after_length hp hi
  cases a with
  | terminal a =>
    cases b with
    | terminal b => exact congrArg SafeMarkedCode.terminal hp
    | vmark b pre mate post => simp [SafeMarkedCode.split] at ht
    | umark b pre mate post => simp [SafeMarkedCode.split] at ht
    | leading pairs => simp [SafeMarkedCode.split] at ht
  | vmark a pre mate post =>
    cases b with
    | terminal b => simp [SafeMarkedCode.split] at ht
    | vmark b pre' mate' post' =>
      have he := safeFromOption_inj.mp hp
      rcases he with ⟨rfl,he⟩
      have hlen := congrArg List.length he
      simp only [List.length_append,List.length_cons] at hlen
      have hpre : pre.length=pre'.length := by
        simp only [SafeMarkedCode.split,List.length_append,List.length_map,List.length_cons] at hi
        omega
      obtain ⟨rfl,hm,rfl⟩ := marked_list_unique he hpre
      have hm' : mate=mate' := congrArg Prod.fst hm
      subst mate'
      rfl
    | umark b pre' mate' post' =>
      have he := safeFromOption_inj.mp hp
      rcases he with ⟨rfl,he⟩
      have hlen := congrArg List.length he
      simp only [List.length_append,List.length_cons] at hlen
      simp only [SafeMarkedCode.split,List.length_append,List.length_map,List.length_cons] at hi
      omega
    | leading pairs =>
      have he : safeFromOption a (pre++(mate,vThree)::post) = safeFromOption (some uThree) pairs := hp
      have he' := safeFromOption_inj.mp he
      rcases he' with ⟨rfl,he'⟩
      simp [SafeMarkedCode.split,optionalU] at hi
  | umark a pre mate post =>
    cases b with
    | terminal b => simp [SafeMarkedCode.split] at ht
    | vmark b pre' mate' post' =>
      have he := safeFromOption_inj.mp hp
      rcases he with ⟨rfl,he⟩
      have hlen := congrArg List.length he
      simp only [List.length_append,List.length_cons] at hlen
      simp only [SafeMarkedCode.split,List.length_append,List.length_map,List.length_cons] at hi
      omega
    | umark b pre' mate' post' =>
      have he := safeFromOption_inj.mp hp
      rcases he with ⟨rfl,he⟩
      have hpre : pre.length=pre'.length := by
        simp only [SafeMarkedCode.split,List.length_append,List.length_map,List.length_cons] at hi
        omega
      obtain ⟨rfl,hm,rfl⟩ := marked_list_unique he hpre
      have hm' : mate=mate' := congrArg Prod.snd hm
      subst mate'
      rfl
    | leading pairs =>
      have he : safeFromOption a (pre++(uThree,mate)::post) = safeFromOption (some uThree) pairs := hp
      have he' := safeFromOption_inj.mp he
      rcases he' with ⟨rfl,he'⟩
      simp [SafeMarkedCode.split,optionalU] at hi
  | leading pairs =>
    cases b with
    | terminal b => simp [SafeMarkedCode.split] at ht
    | vmark b pre mate post =>
      have he : safeFromOption (some uThree) pairs = safeFromOption b (pre++(mate,vThree)::post) := hp
      have he' := safeFromOption_inj.mp he
      rcases he' with ⟨heq,he'⟩
      subst b
      simp [SafeMarkedCode.split,optionalU] at hi
    | umark b pre mate post =>
      have he : safeFromOption (some uThree) pairs = safeFromOption b (pre++(uThree,mate)::post) := hp
      have he' := safeFromOption_inj.mp he
      rcases he' with ⟨heq,he'⟩
      subst b
      simp [SafeMarkedCode.split,optionalU] at hi
    | leading pairs' =>
      have he : pairs=pairs' := congrArg Prod.snd (Sum.inr.inj hp)
      exact congrArg SafeMarkedCode.leading he



lemma list_take_mark_drop {A : Type} (l : List A) (i : ℕ) (hi : i<l.length) :
    l.take i ++ l[i] :: l.drop (i+1) = l := by
  have h := List.take_append_drop (i+1) l
  rw [←List.take_append_getElem hi] at h
  simpa only [List.append_assoc,List.singleton_append] using h

lemma safe_u_value (a : Option U) (l : List (U×V)) (i : ℕ) (hi : i<l.length) :
    (safeFromOption a l).decode[(optionalU a).length+i]'(by
      simp only [safeFromOption_decode,pairDecode,List.length_append,List.length_map,
        List.length_singleton]; omega) = uValue l[i].1 := by
  simp only [safeFromOption_decode,pairDecode,List.append_assoc]
  rw [List.getElem_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]
  rw [List.getElem_append_left (by simpa using hi),List.getElem_map]

lemma safe_v_value (a : Option U) (l : List (U×V)) (i : ℕ) (hi : i<l.length) :
    (safeFromOption a l).decode[(optionalU a).length+l.length+i]'(by
      simp only [safeFromOption_decode,pairDecode,List.length_append,List.length_map,
        List.length_singleton]; omega) = vValue l[i].2 := by
  simp only [safeFromOption_decode,pairDecode,List.append_assoc]
  rw [List.getElem_append_right (by omega)]
  have he : (optionalU a).length+l.length+i-(optionalU a).length=l.length+i := by omega
  simp only [he]
  rw [List.getElem_append_right (by simp)]
  simp only [List.length_map,Nat.add_sub_cancel_left]
  rw [List.getElem_append_left (by simpa using hi),List.getElem_map]

lemma exists_safe_mark_pair (a : Option U) (l : List (U×V))
    (i : ℕ) (hi : i<2*l.length+1)
    (hv : (safeFromOption a l).decode[(optionalU a).length+i]'(by
      simp only [safeFromOption_decode,pairDecode,List.length_append,List.length_map,
        List.length_singleton]; omega)=3) :
    ∃ m : SafeMarkedCode, m.prefix=safeFromOption a l ∧
      m.split.before.length=(optionalU a).length+i := by
  by_cases hend : i=2*l.length
  · refine ⟨.terminal (safeFromOption a l),rfl,?_⟩
    cases a <;> simp [SafeMarkedCode.split,safeBodyWord,safeFromOption,
      optionalU,pairDecode,hend] <;> omega
  by_cases hu : i<l.length
  · have hv' : uValue l[i].1=3 := (safe_u_value a l i hu).symm.trans hv
    have hm : l[i].1=uThree := uValue_injective hv'
    have he : l.take i ++ (uThree,l[i].2)::l.drop (i+1)=l := by
      simpa only [←hm,Prod.eta] using list_take_mark_drop l i hu
    refine ⟨.umark a (l.take i) l[i].2 (l.drop (i+1)),?_,?_⟩
    · simp only [SafeMarkedCode.prefix,he]
    · simp only [SafeMarkedCode.split,List.length_append,List.length_map,List.length_take]
      omega
  · have hi' : i-l.length<l.length := by omega
    have hv' : vValue (l[i-l.length]'hi').2=3 := by
      have he : (optionalU a).length+l.length+(i-l.length)=(optionalU a).length+i := by omega
      have hh := safe_v_value a l (i-l.length) hi'
      simp only [he] at hh
      exact hh.symm.trans hv
    have hm : (l[i-l.length]'hi').2=vThree := vValue_injective hv'
    have he : l.take (i-l.length) ++ ((l[i-l.length]'hi').1,vThree)::l.drop (i-l.length+1)=l := by
      simpa only [←hm,Prod.eta] using list_take_mark_drop l (i-l.length) hi'
    refine ⟨.vmark a (l.take (i-l.length)) (l[i-l.length]'hi').1 (l.drop (i-l.length+1)),?_,?_⟩
    · simp only [SafeMarkedCode.prefix,he]
    · simp only [SafeMarkedCode.split,he,List.length_append,List.length_map,List.length_take]
      omega

lemma SafeMarkedCode.occurrence_surjective : Function.Surjective SafeMarkedCode.occurrence := by
  rintro ⟨⟨c,i⟩,hi,hv⟩
  cases c with
  | inl l =>
    have hi' : i<2*l.length+1 := by
      simpa only [SafeCode.decode,pairDecode,List.length_append,List.length_map,
        List.length_singleton,two_mul] using hi
    obtain ⟨m,hp,hm⟩ := exists_safe_mark_pair none l i hi' (by
      simpa only [safeFromOption,optionalU,Option.toList_none,List.map_nil,List.length_nil,Nat.zero_add] using hv)
    refine ⟨m,Subtype.ext (Prod.ext hp ?_)⟩
    change m.split.before.length=i
    simpa [optionalU] using hm
  | inr c =>
    rcases c with ⟨a,l⟩
    by_cases hi0 : i=0
    · have ha : a=uThree := by
        apply uValue_injective
        change uValue a=3
        simpa [SafeCode.decode,hi0] using hv
      subst a
      refine ⟨.leading l,Subtype.ext (Prod.ext rfl ?_)⟩
      simpa [SafeMarkedCode.occurrence,SafeMarkedCode.split] using hi0.symm
    · have hi' : i-1<2*l.length+1 := by
        simp only [SafeCode.decode,pairDecode,List.length_append,List.length_map,
          List.length_singleton,List.length_cons,List.length_nil] at hi
        omega
      have hv' : (safeFromOption (some a) l).decode[(optionalU (some a)).length+(i-1)]'(by
          simp only [safeFromOption_decode,pairDecode,List.length_append,List.length_map,
            List.length_singleton]; omega)=3 := by
        have he : (optionalU (some a)).length+(i-1)=i := by simp [optionalU]; omega
        simpa only [he,safeFromOption] using hv
      obtain ⟨m,hp,hm⟩ := exists_safe_mark_pair (some a) l (i-1) hi' hv'
      refine ⟨m,Subtype.ext (Prod.ext hp ?_)⟩
      change m.split.before.length=i
      simp only [optionalU,Option.toList_some,List.length_map,List.length_singleton] at hm
      omega

noncomputable def safeMarkedOccurrenceEquiv : SafeMarkedCode ≃ CodeOccurrence SafeCode.decode :=
  Equiv.ofBijective SafeMarkedCode.occurrence
    ⟨SafeMarkedCode.occurrence_injective,SafeMarkedCode.occurrence_surjective⟩

#print axioms safeMarkedOccurrenceEquiv



def EarlyMarkedCode.occurrence (m : EarlyMarkedCode) : CodeOccurrence EarlyCode.decode :=
  ⟨(m.prefix,m.split.before.length),by
    have he := m.word_eq
    refine ⟨by rw [←he]; exact splitMark_lt m.split,?_⟩
    simpa only [he] using splitMark_value m.split⟩

lemma early_mark_after_length {a b : EarlyMarkedCode}
    (hp : a.prefix=b.prefix) (hi : a.split.before.length=b.split.before.length) :
    a.split.after.length=b.split.after.length := by
  have ha := congrArg List.length a.word_eq
  have hb := congrArg List.length b.word_eq
  simp only [SplitMark.word,List.length_append,List.length_cons,hp] at ha hb
  omega

lemma EarlyMarkedCode.occurrence_injective : Function.Injective EarlyMarkedCode.occurrence := by
  intro a b h
  have hp := congrArg (fun x : CodeOccurrence EarlyCode.decode => x.val.1) h
  have hi := congrArg (fun x : CodeOccurrence EarlyCode.decode => x.val.2) h
  change a.prefix=b.prefix at hp
  change a.split.before.length=b.split.before.length at hi
  have ht := early_mark_after_length hp hi
  have hl := congrArg (fun x : EarlyCode => x.1.length) hp
  cases a with
  | terminal a =>
    cases b with
    | terminal b => exact congrArg EarlyMarkedCode.terminal hp
    | suffix pairs pre post => simp [EarlyMarkedCode.split] at ht
    | second pre mate post suffix => simp [EarlyMarkedCode.split] at ht
    | first pre mate post suffix => simp [EarlyMarkedCode.split] at ht
  | suffix pairs pre post =>
    cases b with
    | terminal b => simp [EarlyMarkedCode.split] at ht
    | suffix pairs' pre' post' =>
      have he : pairs=pairs' ∧ pre++uThree::post=pre'++uThree::post' := Prod.mk.inj hp
      rcases he with ⟨rfl,he⟩
      have hpre : pre.length=pre'.length := by
        simp only [EarlyMarkedCode.split,List.length_append,List.length_map,List.length_cons] at hi
        omega
      obtain ⟨rfl,_,rfl⟩ := marked_list_unique he hpre
      rfl
    | second pre' mate post' suffix =>
      simp only [EarlyMarkedCode.prefix,List.length_append,List.length_cons] at hl
      simp only [EarlyMarkedCode.split,List.length_append,List.length_map,List.length_cons] at hi
      omega
    | first pre' mate post' suffix =>
      simp only [EarlyMarkedCode.prefix,List.length_append,List.length_cons] at hl
      simp only [EarlyMarkedCode.split,List.length_append,List.length_map,List.length_cons] at hi
      omega
  | second pre mate post suffix =>
    cases b with
    | terminal b => simp [EarlyMarkedCode.split] at ht
    | suffix pairs' pre' post' =>
      simp only [EarlyMarkedCode.prefix,List.length_append,List.length_cons] at hl
      simp only [EarlyMarkedCode.split,List.length_append,List.length_map,List.length_cons] at hi
      omega
    | second pre' mate' post' suffix' =>
      have he : pre++(mate,uThree)::post=pre'++(mate',uThree)::post' ∧ suffix=suffix' := Prod.mk.inj hp
      rcases he with ⟨he,rfl⟩
      have hpre : pre.length=pre'.length := by
        simp only [EarlyMarkedCode.prefix,List.length_append,List.length_cons] at hl
        simp only [EarlyMarkedCode.split,List.length_append,List.length_map,List.length_cons] at hi
        omega
      obtain ⟨rfl,hm,rfl⟩ := marked_list_unique he hpre
      have hm' : mate=mate' := congrArg Prod.fst hm
      subst mate'
      rfl
    | first pre' mate' post' suffix' =>
      simp only [EarlyMarkedCode.prefix,List.length_append,List.length_cons] at hl
      simp only [EarlyMarkedCode.split,List.length_append,List.length_map,List.length_cons] at hi
      omega
  | first pre mate post suffix =>
    cases b with
    | terminal b => simp [EarlyMarkedCode.split] at ht
    | suffix pairs' pre' post' =>
      simp only [EarlyMarkedCode.prefix,List.length_append,List.length_cons] at hl
      simp only [EarlyMarkedCode.split,List.length_append,List.length_map,List.length_cons] at hi
      omega
    | second pre' mate' post' suffix' =>
      simp only [EarlyMarkedCode.prefix,List.length_append,List.length_cons] at hl
      simp only [EarlyMarkedCode.split,List.length_append,List.length_map,List.length_cons] at hi
      omega
    | first pre' mate' post' suffix' =>
      have he : pre++(uThree,mate)::post=pre'++(uThree,mate')::post' ∧ suffix=suffix' := Prod.mk.inj hp
      rcases he with ⟨he,rfl⟩
      have hpre : pre.length=pre'.length := by
        simpa only [EarlyMarkedCode.split,List.length_map] using hi
      obtain ⟨rfl,hm,rfl⟩ := marked_list_unique he hpre
      have hm' : mate=mate' := congrArg Prod.snd hm
      subst mate'
      rfl

lemma early_first_value (l : List (U×U)) (s : List U) (i : ℕ) (hi : i<l.length) :
    (EarlyCode.decode (l,s))[i]'(by simp only [EarlyCode.decode,List.length_append,List.length_map,
      List.length_cons,List.length_nil]; omega)=uValue l[i].1 := by
  unfold EarlyCode.decode
  rw [List.getElem_append_left (by simpa using hi),List.getElem_map]

lemma early_second_value (l : List (U×U)) (s : List U) (i : ℕ) (hi : i<l.length) :
    (EarlyCode.decode (l,s))[l.length+1+i]'(by
      simp only [EarlyCode.decode,List.length_append,List.length_map,List.length_cons,List.length_nil]
      omega) = uValue l[i].2 := by
  unfold EarlyCode.decode
  rw [List.getElem_append_right (by simp; omega)]
  have he : l.length+1+i-l.length=i+1 := by omega
  simp only [List.length_map,he,List.getElem_cons_succ]
  rw [List.getElem_append_left (by simpa using hi),List.getElem_map]

lemma early_suffix_value (l : List (U×U)) (s : List U) (i : ℕ) (hi : i<s.length) :
    (EarlyCode.decode (l,s))[2*l.length+2+i]'(by
      simp only [EarlyCode.decode,List.length_append,List.length_map,List.length_cons,List.length_nil]
      omega) = uValue s[i] := by
  unfold EarlyCode.decode
  rw [List.getElem_append_right (by simp; omega)]
  have he : 2*l.length+2+i-l.length=(l.length+1+i)+1 := by omega
  simp only [List.length_map,he,List.getElem_cons_succ]
  rw [List.getElem_append_right (by simp; omega)]
  have he' : l.length+1+i-l.length=i+1 := by omega
  simp only [List.length_map,he',List.getElem_cons_succ]
  rw [List.getElem_append_left (by simpa using hi),List.getElem_map]



lemma exists_early_mark (l : List (U×U)) (s : List U) (i : ℕ)
    (hi : i<(EarlyCode.decode (l,s)).length) (hv : (EarlyCode.decode (l,s))[i]=3) :
    ∃ m : EarlyMarkedCode, m.prefix=(l,s) ∧ m.split.before.length=i := by
  have hlen : i<2*l.length+s.length+3 := by
    simp only [EarlyCode.decode,List.length_append,List.length_map,
      List.length_cons,List.length_nil] at hi
    omega
  by_cases hend : i=2*l.length+s.length+2
  · refine ⟨.terminal (l,s),rfl,?_⟩
    simp only [EarlyMarkedCode.split,earlyBodyWord,List.length_append,List.length_map,
      List.length_cons]
    omega
  by_cases hfirst : i<l.length
  · have hh := early_first_value l s i hfirst
    have hm : l[i].1=uThree := uValue_injective (hh.symm.trans hv)
    have he : l.take i ++ (uThree,l[i].2)::l.drop (i+1)=l := by
      simpa only [←hm,Prod.eta] using list_take_mark_drop l i hfirst
    refine ⟨.first (l.take i) l[i].2 (l.drop (i+1)) s,?_,?_⟩
    · simp only [EarlyMarkedCode.prefix,he]
    · simp only [EarlyMarkedCode.split,List.length_map,List.length_take]
      omega
  by_cases hone : i=l.length
  · have hh := OriginalReservoir.early_first_one_value (l,s)
    have hbad : (1:ℕ)=3 := hh.symm.trans (by simpa only [hone] using hv)
    omega
  by_cases hsecond : i<2*l.length+1
  · have hpos : i-l.length-1<l.length := by omega
    have hidx : l.length+1+(i-l.length-1)=i := by omega
    have hh := early_second_value l s (i-l.length-1) hpos
    simp only [hidx] at hh
    have hm : (l[i-l.length-1]'hpos).2=uThree := uValue_injective (hh.symm.trans hv)
    have he : l.take (i-l.length-1) ++ ((l[i-l.length-1]'hpos).1,uThree)::l.drop (i-l.length-1+1)=l := by
      simpa only [←hm,Prod.eta] using list_take_mark_drop l (i-l.length-1) hpos
    refine ⟨.second (l.take (i-l.length-1)) (l[i-l.length-1]'hpos).1
      (l.drop (i-l.length-1+1)) s,?_,?_⟩
    · simp only [EarlyMarkedCode.prefix,he]
    · simp only [EarlyMarkedCode.split,he,List.length_append,List.length_map,
        List.length_cons,List.length_take]
      omega
  by_cases htwo : i=2*l.length+1
  · have hh := OriginalReservoir.early_double_one (l,s)
    have hbad : (2:ℕ)=3 := hh.symm.trans (by simpa only [htwo] using hv)
    omega
  have hpos : i-(2*l.length+2)<s.length := by omega
  have hidx : 2*l.length+2+(i-(2*l.length+2))=i := by omega
  have hh := early_suffix_value l s (i-(2*l.length+2)) hpos
  simp only [hidx] at hh
  have hm : (s[i-(2*l.length+2)]'hpos)=uThree := by
    exact uValue_injective (hh.symm.trans hv)
  have he : s.take (i-(2*l.length+2)) ++ uThree::s.drop (i-(2*l.length+2)+1)=s := by
    simpa only [←hm] using list_take_mark_drop s (i-(2*l.length+2)) hpos
  refine ⟨.suffix l (s.take (i-(2*l.length+2))) (s.drop (i-(2*l.length+2)+1)),?_,?_⟩
  · simp only [EarlyMarkedCode.prefix,he]
  · simp only [EarlyMarkedCode.split,List.length_append,List.length_map,
      List.length_cons,List.length_take]
    omega

lemma EarlyMarkedCode.occurrence_surjective : Function.Surjective EarlyMarkedCode.occurrence := by
  rintro ⟨⟨⟨l,s⟩,i⟩,hi,hv⟩
  obtain ⟨m,hp,hm⟩ := exists_early_mark l s i hi hv
  exact ⟨m,Subtype.ext (Prod.ext hp hm)⟩

noncomputable def earlyMarkedOccurrenceEquiv : EarlyMarkedCode ≃ CodeOccurrence EarlyCode.decode :=
  Equiv.ofBijective EarlyMarkedCode.occurrence
    ⟨EarlyMarkedCode.occurrence_injective,EarlyMarkedCode.occurrence_surjective⟩

#print axioms earlyMarkedOccurrenceEquiv



/-- Exact weight fibres of physical occurrences, used by failure convolution. -/
def codeOccurrenceAtEquiv {C : Type} (F : OriginalReservoir.PrefixFamily C) (n : ℕ) :
    {o : CodeOccurrence F.decode // F.weight o.val.1=n} ≃ OriginalReservoir.PrefixOccurrence F n where
  toFun o := ⟨⟨o.val.val.1,o.property⟩,
    ⟨⟨o.val.val.2,o.val.property.choose⟩,o.val.property.choose_spec⟩⟩
  invFun p := ⟨⟨(p.1.val,p.2.val.val),p.2.val.isLt,p.2.property⟩,p.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def safeMarkedPrefixEquiv (n : ℕ) :
    {m : SafeMarkedCode // m.prefix.weight=n} ≃
      OriginalReservoir.PrefixOccurrence OriginalReservoir.safeFamily n :=
  (safeMarkedOccurrenceEquiv.subtypeEquiv (fun _ => Iff.rfl)).trans
    (codeOccurrenceAtEquiv OriginalReservoir.safeFamily n)

noncomputable def earlyMarkedPrefixEquiv (n : ℕ) :
    {m : EarlyMarkedCode // m.prefix.weight=n} ≃
      OriginalReservoir.PrefixOccurrence OriginalReservoir.earlyFamily n :=
  (earlyMarkedOccurrenceEquiv.subtypeEquiv (fun _ => Iff.rfl)).trans
    (codeOccurrenceAtEquiv OriginalReservoir.earlyFamily n)

lemma safeMarkedPrefixEquiv_distance (n : ℕ) (m : {m : SafeMarkedCode // m.prefix.weight=n}) :
    (safeMarkedPrefixEquiv n m).distance=m.val.split.after.length := by
  change m.val.prefix.decode.length-1-m.val.split.before.length=m.val.split.after.length
  have h := m.val.split.distance
  simp only [SplitMark.index] at h
  rw [m.val.word_eq] at h
  exact h

lemma earlyMarkedPrefixEquiv_distance (n : ℕ) (m : {m : EarlyMarkedCode // m.prefix.weight=n}) :
    (earlyMarkedPrefixEquiv n m).distance=m.val.split.after.length := by
  change m.val.prefix.decode.length-1-m.val.split.before.length=m.val.split.after.length
  have h := m.val.split.distance
  simp only [SplitMark.index] at h
  rw [m.val.word_eq] at h
  exact h

#print axioms safeMarkedPrefixEquiv
#print axioms earlyMarkedPrefixEquiv
#print axioms safeMarkedPrefixEquiv_distance
#print axioms earlyMarkedPrefixEquiv_distance

end SubmittedGenus.FiniteArithmetic.Reservoir
