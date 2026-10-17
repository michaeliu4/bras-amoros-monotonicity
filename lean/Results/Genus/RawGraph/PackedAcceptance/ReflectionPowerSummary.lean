import Results.Genus.RawGraph.PackedAcceptance.ReflectionWordPowerSlices

namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord

/-- Cached total length/value and an ordered arbitrary-subword query. No
expanded word is stored. Whole and empty queries return cached constants. -/
structure PowerSummary (M : Type*) where
  length : ℕ
  value : M
  slice : ℕ→ℕ→M

def PowerSummary.Rep {A M : Type*} [Monoid M] (f : A→M) (s : PowerSummary M) (w : List A) : Prop :=
  s.length=w.length ∧ s.value=(w.map f).prod ∧
    ∀a n, s.slice a n=(((w.drop a).take n).map f).prod

def guardedSlice {M : Type*} [Monoid M] (len : ℕ) (total : M)
    (body : ℕ→ℕ→M) (a n : ℕ) : M :=
  if n=0 ∨ len≤a then 1 else if a=0 ∧ len≤n then total else body a n

lemma guardedSlice_correct {A M : Type*} [Monoid M] (f : A→M) (w : List A)
    (body : ℕ→ℕ→M) (hb : ∀a n, a<w.length → body a n=(((w.drop a).take n).map f).prod)
    (a n : ℕ) :
    guardedSlice w.length (w.map f).prod body a n=(((w.drop a).take n).map f).prod := by
  unfold guardedSlice
  split
  · rename_i h
    rcases h with h|h
    · simp [h]
    · simp [List.drop_of_length_le h]
  · rename_i h
    split
    · rename_i h'
      rcases h' with ⟨rfl,hn⟩
      simp [List.take_of_length_le hn]
    · exact hb a n (by omega)

def PowerSummary.empty {M : Type*} [Monoid M] : PowerSummary M := ⟨0,1,fun _ _=>1⟩
def PowerSummary.atom {M : Type*} [Monoid M] (x : M) : PowerSummary M :=
  ⟨1,x,fun a n=>if a=0 ∧ 0<n then x else 1⟩

def PowerSummary.mul {M : Type*} [Monoid M] (x y : PowerSummary M) : PowerSummary M :=
  ⟨x.length+y.length,x.value*y.value,
    guardedSlice (x.length+y.length) (x.value*y.value)
      (fun a n=>x.slice a n*y.slice (a-x.length) (n-(x.length-a)))⟩

def PowerSummary.pow {M : Type*} [Monoid M] (x : PowerSummary M) (k : ℕ) : PowerSummary M :=
  ⟨k*x.length,x.value^k,
    guardedSlice (k*x.length) (x.value^k) (fun a n=>
      let m:=min n (k*x.length-a)
      let r:=m-(x.length-a%x.length)
      x.slice (a%x.length) m*x.value^(r/x.length)*x.slice 0 (r%x.length))⟩

lemma PowerSummary.empty_rep {A M : Type*} [Monoid M] (f : A→M) :
    PowerSummary.Rep f PowerSummary.empty [] := by simp [Rep,empty]

lemma PowerSummary.atom_rep {A M : Type*} [Monoid M] (f : A→M) (a : A) :
    PowerSummary.Rep f (PowerSummary.atom (f a)) [a] := by
  refine ⟨rfl,by simp [atom],?_⟩
  intro s n
  cases s <;> cases n <;> simp [atom]

lemma PowerSummary.mul_rep {A M : Type*} [Monoid M] (f : A→M)
    (x y : PowerSummary M) (u v : List A) (hx : x.Rep f u) (hy : y.Rep f v) :
    (x.mul y).Rep f (u++v) := by
  rcases hx with ⟨hxlen,hxval,hxs⟩
  rcases hy with ⟨hylen,hyval,hys⟩
  refine ⟨by simp [mul,hxlen,hylen],by simp [mul,hxval,hyval],?_⟩
  intro a n
  simp only [PowerSummary.mul]
  rw [hxlen,hylen,hxval,hyval,←List.length_append,←List.prod_append,←List.map_append]
  apply guardedSlice_correct
  intro a n _
  rw [hxs,hys,List.drop_append,List.take_append,List.length_drop,List.map_append,List.prod_append]

lemma PowerSummary.pow_rep {A M : Type*} [Monoid M] (f : A→M)
    (x : PowerSummary M) (w : List A) (hx : x.Rep f w) (k : ℕ) :
    (x.pow k).Rep f (repeatWord w k) := by
  rcases hx with ⟨hxlen,hxval,hxs⟩
  refine ⟨by simp [pow,hxlen,repeatWord_length],by simp [pow,hxval,repeatWord_product],?_⟩
  intro a n
  simp only [PowerSummary.pow]
  rw [hxlen,hxval,←repeatWord_length,←repeatWord_product f w k]
  apply guardedSlice_correct
  intro a n ha
  have hw : 0<w.length := by
    rw [repeatWord_length] at ha
    by_contra hn
    have hz : w.length=0 := by omega
    simp [hz] at ha
  have ha' : a<k*w.length := by simpa [repeatWord_length] using ha
  let m:=min n (k*w.length-a)
  let r:=m-(w.length-a%w.length)
  have hm : m≤k*w.length-a := Nat.min_le_right _ _
  have hq : a/w.length<k := (Nat.div_lt_iff_lt_mul hw).mpr ha'
  have he:=Nat.mod_add_div a w.length
  have hr : r≤(k-a/w.length-1)*w.length := by
    dsimp [r]
    have hsplit : (k-a/w.length-1)*w.length+w.length+a/w.length*w.length=k*w.length := by
      have hh : k=(k-a/w.length-1)+1+a/w.length := by omega
      conv_rhs=>rw [hh]
      ring
    rw [Nat.mul_comm w.length] at he
    omega
  simp only [repeatWord_length]
  change x.slice (a%w.length) m*(w.map f).prod^(r/w.length)*x.slice 0 (r%w.length)=_
  rw [hxs,hxs,List.drop_zero]
  conv_rhs=>rw [List.take_eq_take_min,List.length_drop,repeatWord_length]
  change _=(((repeatWord w k).drop a).take m |>.map f).prod
  rw [drop_repeatWord w k a hw ha',List.take_append,List.length_drop]
  change _=(((w.drop (a%w.length)).take m ++ (repeatWord w (k-a/w.length-1)).take r).map f).prod
  rw [take_repeatWord w (k-a/w.length-1) r hw hr,List.map_append,List.map_append,
    List.prod_append,List.prod_append,repeatWord_product]
  simp [mul_assoc]

#print axioms PowerSummary.mul_rep
#print axioms PowerSummary.pow_rep
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord
