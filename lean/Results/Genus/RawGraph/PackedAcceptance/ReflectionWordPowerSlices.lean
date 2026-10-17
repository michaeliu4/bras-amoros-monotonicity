import Results.Genus.RawGraph.PackedAcceptance.ReflectionSourcePowerProgram
import Mathlib.Algebra.FreeMonoid.Basic

namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord

def repeatWord {A : Type*} (w : List A) (k : ℕ) : List A :=
  (List.replicate k w).flatten

lemma repeatWord_zero {A : Type*} (w : List A) : repeatWord w 0=[] := rfl
lemma repeatWord_succ {A : Type*} (w : List A) (k : ℕ) :
    repeatWord w (k+1)=w++repeatWord w k := by simp [repeatWord,List.replicate_succ]
lemma repeatWord_add {A : Type*} (w : List A) (a b : ℕ) :
    repeatWord w (a+b)=repeatWord w a++repeatWord w b := by
  simp only [repeatWord,List.replicate_add,List.flatten_append]
lemma repeatWord_length {A : Type*} (w : List A) (k : ℕ) :
    (repeatWord w k).length=k*w.length := by
  induction k with
  | zero=>simp [repeatWord]
  | succ k ih=>rw [repeatWord_succ,List.length_append,ih,Nat.succ_mul];omega

lemma take_repeatWord {A : Type*} (w : List A) (k n : ℕ) (hw : 0<w.length)
    (hn : n≤k*w.length) :
    (repeatWord w k).take n=repeatWord w (n/w.length)++w.take (n%w.length) := by
  induction k generalizing n with
  | zero=>
    have hz : n=0 := by omega
    simp [hz,repeatWord]
  | succ k ih=>
    rw [repeatWord_succ]
    by_cases h : n<w.length
    · rw [List.take_append_of_le_length h.le,Nat.div_eq_of_lt h,Nat.mod_eq_of_lt h]
      simp [repeatWord]
    · have hle : w.length≤n := by omega
      have hn' : n-w.length≤k*w.length := by
        rw [Nat.succ_mul] at hn
        omega
      rw [List.take_append,List.take_of_length_le hle,ih (n-w.length) hn']
      have he : n=w.length+(n-w.length) := by omega
      have hd : n/w.length=(n-w.length)/w.length+1 := by
        conv_lhs=>rw [he]
        exact Nat.add_div_left _ hw
      have hm : n%w.length=(n-w.length)%w.length := by
        conv_lhs=>rw [he]
        exact Nat.add_mod_left _ _
      rw [hd,hm,repeatWord_succ,List.append_assoc]

lemma drop_repeatWord {A : Type*} (w : List A) (k s : ℕ) (hw : 0<w.length)
    (hs : s<k*w.length) :
    (repeatWord w k).drop s=w.drop (s%w.length)++repeatWord w (k-s/w.length-1) := by
  have hq : s/w.length<k := (Nat.div_lt_iff_lt_mul hw).mpr hs
  have he : k=s/w.length+((k-s/w.length-1)+1) := by omega
  conv_lhs=>rw [he,repeatWord_add,repeatWord_succ]
  rw [List.drop_append]
  have hlen : (repeatWord w (s/w.length)).length≤s := by
    rw [repeatWord_length]
    exact Nat.div_mul_le_self _ _
  rw [List.drop_of_length_le hlen,List.nil_append,repeatWord_length]
  have hsrem : s-s/w.length*w.length=s%w.length := by
    have h:=Nat.mod_add_div s w.length
    rw [Nat.mul_comm w.length] at h
    omega
  rw [hsrem,List.drop_append_of_le_length (Nat.mod_lt s hw).le]

lemma repeatWord_product {A M : Type*} [Monoid M] (f : A→M) (w : List A) (k : ℕ) :
    ((repeatWord w k).map f).prod=(w.map f).prod^k := by
  simp [repeatWord,List.map_flatten,List.prod_flatten,List.map_map,Function.comp_def]

#print axioms take_repeatWord
#print axioms drop_repeatWord
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord
