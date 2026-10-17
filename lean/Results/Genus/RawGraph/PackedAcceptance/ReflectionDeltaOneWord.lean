import Results.Genus.RawGraph.PackedAcceptance.ReflectionThresholdWord

/-! Closed-form, order-preserving word compression for reduced gap one.
The computation uses one quotient and three blocks, without scanning vertices.
The identities hold in an arbitrary noncommutative monoid. -/
namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord

/-- Number of nonnegative `k` satisfying `a+g*k<t`. -/
def cut (g a t : ℕ) : ℕ := if a<t then (t-1-a)/g+1 else 0

lemma lt_cut_iff (g a t k : ℕ) (hg : 0<g) :
    k<cut g a t ↔ a+g*k<t := by
  unfold cut
  by_cases ha : a<t
  · rw [if_pos ha]
    rw [Nat.lt_succ_iff,Nat.le_div_iff_mul_le hg]
    constructor <;> intro h <;> nlinarith [Nat.sub_add_cancel (by omega : a≤t-1),
      Nat.sub_add_cancel (by omega : 1≤t)]
  · rw [if_neg ha]
    constructor <;> intro h <;> omega

lemma cut_le (g a t n : ℕ) (hg : 0<g) (hn : t≤a+g*n) : cut g a t≤n := by
  by_contra h
  have ht := (lt_cut_iff g a t n hg).mp (by omega)
  omega

/-- At reduced gap one, every nonzero coset has exactly one final C letter. -/
lemma delta_one_letter (g L r a k : ℕ) (hg : 0<g) (ha0 : 0<a) (ha : a<g)
    (hL : 0<L) (hp : r+g<g*L) (hk : k<L) :
    letter (g*L) r g (a+g*k)=
      if k<cut g a r then .fullStrong else if k<L-1 then .carryCarry else .carryStrong := by
  have hcut := lt_cut_iff g a r k hg
  have hlast : a+g*k<g*L-g ↔ k<L-1 := by
    have he : g*(L-1)+g=g*L := by
      nlinarith [Nat.sub_add_cancel hL]
    constructor
    · intro h
      by_contra hn
      have hm := Nat.mul_le_mul_left g (by omega : L-1≤k)
      omega
    · intro h
      have hm:=Nat.mul_le_mul_left g (by omega : k+1≤L-1)
      rw [Nat.mul_succ] at hm
      omega
  simp only [letter,←hcut,hlast]

lemma map_range_three (q b : ℕ) {A : Type*} (x y z : A) :
    (List.range (q+b+1)).map (fun k=>if k<q then x else if k<q+b then y else z)=
      List.replicate q x ++ List.replicate b y ++ [z] := by
  induction q with
  | zero =>
    simp only [Nat.zero_add,Nat.not_lt_zero,↓reduceIte,List.replicate_zero,List.nil_append]
    induction b with
    | zero => simp
    | succ b ih =>
      rw [List.range_succ_eq_map]
      simp only [List.map_cons,List.map_map,Nat.zero_lt_succ,↓reduceIte,
        Nat.succ_lt_succ_iff,Function.comp_def,List.replicate_succ]
      simpa only [Nat.succ_eq_add_one,List.cons_append] using congrArg (List.cons y) ih
  | succ q ih =>
    rw [show q+1+b+1=(q+b+1)+1 by omega,List.range_succ_eq_map]
    simp only [List.map_cons,List.map_map,Nat.zero_lt_succ,↓reduceIte,
      Function.comp_def,List.replicate_succ,List.cons_append]
    congr 1
    convert ih using 1
    congr 1
    funext k
    simp only [show k+1<q+1 ↔ k<q by omega,
      show k+1<q+1+b ↔ k<q+b by omega]

/-- Exact complete cycle pair-word. The final C contains the true closure. -/
theorem delta_one_word (g L r a : ℕ) (hg : 0<g) (ha0 : 0<a) (ha : a<g)
    (hL : 0<L) (hp : r+g<g*L) :
    (List.range L).map (fun k=>letter (g*L) r g (a+g*k))=
      List.replicate (cut g a r) Letter.fullStrong ++
      List.replicate (L-1-cut g a r) Letter.carryCarry ++ [Letter.carryStrong] := by
  have hc : cut g a r≤L-1 := by
    apply cut_le g a r (L-1) hg
    have he : g*(L-1)+g=g*L := by nlinarith [Nat.sub_add_cancel hL]
    omega
  have hn : cut g a r+(L-1-cut g a r)+1=L := by omega
  have hm := map_range_three (cut g a r) (L-1-cut g a r)
    Letter.fullStrong Letter.carryCarry Letter.carryStrong
  rw [hn] at hm
  rw [←hm]
  apply List.map_congr_left
  intro k hk
  have hkl : k<L := List.mem_range.mp hk
  rw [delta_one_letter g L r a k hg ha0 ha hL hp hkl]
  rw [show cut g a r+(L-1-cut g a r)=L-1 by omega]

/-- Arbitrary noncommutative products compress to three ordered powers. -/
theorem delta_one_product {A : Type*} [Monoid A] (f : Letter→A)
    (g L r a : ℕ) (hg : 0<g) (ha0 : 0<a) (ha : a<g)
    (hL : 0<L) (hp : r+g<g*L) :
    ((List.range L).map (fun k=>f (letter (g*L) r g (a+g*k)))).prod=
      f .fullStrong ^ cut g a r * f .carryCarry ^ (L-1-cut g a r) * f .carryStrong := by
  rw [show (List.range L).map (fun k=>f (letter (g*L) r g (a+g*k)))=
      ((List.range L).map (fun k=>letter (g*L) r g (a+g*k))).map f by simp]
  rw [delta_one_word g L r a hg ha0 ha hL hp]
  simp [List.prod_append,mul_assoc]

#print axioms delta_one_word
#print axioms delta_one_product
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord
