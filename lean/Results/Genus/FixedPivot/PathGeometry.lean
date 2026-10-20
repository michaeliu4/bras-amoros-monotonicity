import Results.Genus.FixedPivot.Geometry

/-!
# Actual paired and fixed carry-path geometry
This refines the canonical reflected residue lists into an ordered path model.
Endpoint formulas and loop parity are derived from the two source targets.
-/
namespace SubmittedGenus.FixedPivot

/-- Representatives in1,...,d are unique even at the residue-zero port d. -/
lemma residue_list_unique {d a b k l : ℕ} (ha : 0 < a) (had : a ≤ d)
    (hb : 0 < b) (hbd : b ≤ d) (he : a+k*d=b+l*d) : a=b ∧ k=l := by
  have hkl : k=l := by
    rcases lt_trichotomy k l with h | h | h
    · have hh : (k+1)*d ≤ l*d := Nat.mul_le_mul_right d (by omega)
      have hx : (k+1)*d=k*d+d := by ring
      omega
    · exact h
    · have hh : (l+1)*d ≤ k*d := Nat.mul_le_mul_right d (by omega)
      have hx : (l+1)*d=l*d+d := by ring
      omega
  constructor
  · rw [hkl] at he
    omega
  · exact hkl

namespace ResiduePair
variable {N d : ℕ} (L : ResiduePair N d)

/-- Swap the two lists without changing their length. -/
def swap : ResiduePair N d where
  a := L.b
  b := L.a
  n := L.n
  d_pos := L.d_pos
  a_pos := L.b_pos
  a_le := L.b_le
  b_pos := L.a_pos
  b_le := L.a_le
  n_pos := L.n_pos
  endpoint := by have he:=L.endpoint; omega

lemma reflectF_right {k : ℕ} (hk : k < L.n) :
    reflectF N (L.right k)=L.left (L.n-1-k) := L.swap.reflectF_left hk

lemma reflectG_right {k : ℕ} (hk0 : 0 < k) (hk : k < L.n) :
    reflectG N d (L.right k)=L.left (L.n-k) := L.swap.reflectG_left hk0 hk

lemma left_injective : Function.Injective L.left := by
  intro k l he
  exact (residue_list_unique L.a_pos L.a_le L.a_pos L.a_le he).2

lemma right_injective : Function.Injective L.right := by
  intro k l he
  exact (residue_list_unique L.b_pos L.b_le L.b_pos L.b_le he).2

lemma lists_disjoint (hab : L.a ≠ L.b) (k l : ℕ) : L.left k ≠ L.right l := by
  intro he
  exact hab (residue_list_unique L.a_pos L.a_le L.b_pos L.b_le he).1

/-- The even vertices in the paper's alternating paired-class path. -/
def pairedEven (k : ℕ) : ℕ := L.left k

/-- The odd vertices reverse the partner's residue list. -/
def pairedOdd (k : ℕ) : ℕ := L.right (L.n-1-k)

lemma paired_even_vertex {k : ℕ} (hk : k < L.n) : CarryVertex N (L.pairedEven k) :=
  L.left_vertex hk

lemma paired_odd_vertex {k : ℕ} (hk : k < L.n) : CarryVertex N (L.pairedOdd k) := by
  apply L.right_vertex
  have hn:=L.n_pos
  omega

/-- Every even-to-odd step is exactly an F edge. -/
lemma paired_F_step {k : ℕ} (hk : k < L.n) :
    L.pairedEven k+L.pairedOdd k=N := by
  have he:=L.reflectF_left hk
  have hx:=L.left_vertex hk
  unfold reflectF CarryVertex at *
  unfold pairedEven pairedOdd
  omega

/-- Every odd-to-next-even step is exactly a G edge. -/
lemma paired_G_step {k : ℕ} (hk : k+1 < L.n) :
    L.pairedOdd k+L.pairedEven (k+1)=N+d := by
  have hrev : 0 < L.n-1-k := by omega
  have hrev' : L.n-1-k < L.n := by omega
  have he:=L.reflectG_right hrev hrev'
  have hi : L.n-(L.n-1-k)=k+1 := by omega
  rw [hi] at he
  have hx:=L.right_vertex hrev'
  unfold reflectG CarryVertex at *
  unfold pairedEven pairedOdd
  omega

/-- The only paired-path ports are its two extreme vertices. -/
lemma paired_ports : L.pairedEven 0=L.a ∧ L.pairedOdd (L.n-1)=L.b := by
  simp [pairedEven,pairedOdd,left,right]

/-- Both lists occur completely in the alternating paired path. -/
lemma paired_covers_left {k : ℕ} (hk : k < L.n) :
    ∃ j < L.n, L.left k=L.pairedEven j := ⟨k,hk,rfl⟩

lemma paired_covers_right {k : ℕ} (hk : k < L.n) :
    ∃ j < L.n, L.right k=L.pairedOdd j := by
  refine ⟨L.n-1-k, by have hn:=L.n_pos; omega, ?_⟩
  unfold pairedOdd
  congr 1
  omega

lemma paired_no_F_loop (hab : L.a ≠ L.b) {k : ℕ} (hk : k < L.n) :
    L.pairedEven k ≠ L.pairedOdd k := L.lists_disjoint hab _ _

lemma paired_no_G_loop (hab : L.a ≠ L.b) {k : ℕ} (hk : k+1 < L.n) :
    L.pairedOdd k ≠ L.pairedEven (k+1) := Ne.symm (L.lists_disjoint hab _ _)

/-- Source incidences between the two paired residue lists are precisely the
adjacent positions in the alternating path; no extra graph edge is omitted. -/
lemma paired_cross_incidence_iff (hab : L.a ≠ L.b) {k l : ℕ}
    (hk : k < L.n) (hl : l < L.n) :
    CarryIncidence N d (L.pairedEven k) (L.pairedOdd l) ↔
      k=l ∨ k=l+1 := by
  have hleft:=L.left_vertex hk
  have hright:=L.paired_odd_vertex hl
  unfold pairedEven
  rw [incidence_iff_reflections hleft hright]
  constructor
  · rintro (he | he)
    · left
      rw [L.reflectF_left hk] at he
      have hi:=L.right_injective he
      omega
    · right
      have hg : d < L.left k := (reflectG_vertex_iff hleft).1 (he ▸ hright)
      have hk0 : 0 < k := by
        by_contra h
        have hkz : k=0 := by omega
        subst k
        have ha:=L.a_le
        simp [left] at hg
        omega
      rw [L.reflectG_left hk0 hk] at he
      have hi:=L.right_injective he
      omega
  · rintro (rfl | rfl)
    · exact Or.inl (L.reflectF_left hk).symm
    · right
      rw [L.reflectG_left (by omega) hk]
      unfold pairedOdd
      congr 1
      omega

/-- No paired component contains edges within just one of its residue lists. -/
lemma paired_no_same_list_incidence (hab : L.a ≠ L.b) {k l : ℕ}
    (hk : k < L.n) (hl : l < L.n) :
    ¬ CarryIncidence N d (L.left k) (L.left l) := by
  intro h
  rw [incidence_iff_reflections (L.left_vertex hk) (L.left_vertex hl)] at h
  rcases h with h | h
  · rw [L.reflectF_left hk] at h
    exact L.lists_disjoint hab l _ h
  · have hg : d < L.left k := (reflectG_vertex_iff (L.left_vertex hk)).1 (h ▸ L.left_vertex hl)
    have hk0 : 0 < k := by
      by_contra hh
      have hkz : k=0 := by omega
      subst k
      have ha:=L.a_le
      simp [left] at hg
      omega
    rw [L.reflectG_left hk0 hk] at h
    exact L.lists_disjoint hab l _ h


end ResiduePair
/-- Alternating list indices0,n−1,1,n−2,..., stopping after n vertices. -/
def zigzagIndex (n t : ℕ) : ℕ := if t%2=0 then t/2 else n-1-t/2

lemma zigzagIndex_lt {n t : ℕ} (ht : t<n) : zigzagIndex n t<n := by
  unfold zigzagIndex
  split_ifs <;> omega

lemma zigzagIndex_injective (n : ℕ) :
    Function.Injective (fun t : Fin n => (⟨zigzagIndex n t,zigzagIndex_lt t.isLt⟩ : Fin n)) := by
  intro t s he
  have he' := congrArg Fin.val he
  have ht:=t.isLt
  have hs:=s.isLt
  change zigzagIndex n t.val=zigzagIndex n s.val at he'
  unfold zigzagIndex at he'
  split_ifs at he' <;> apply Fin.ext <;> omega

/-- The zigzag lists every fixed-class vertex once. -/
noncomputable def zigzagEquiv (n : ℕ) : Fin n ≃ Fin n :=
  Equiv.ofBijective (fun t => ⟨zigzagIndex n t,zigzagIndex_lt t.isLt⟩)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨zigzagIndex_injective n,rfl⟩)

lemma zigzag_even_step {n t : ℕ} (ht : t+1<n) (he : t%2=0) :
    zigzagIndex n t+zigzagIndex n (t+1)=n-1 := by
  unfold zigzagIndex
  have ho : (t+1)%2≠0 := by omega
  rw [if_pos he,if_neg ho]
  omega

lemma zigzag_odd_step {n t : ℕ} (ht : t+1<n) (he : t%2≠0) :
    zigzagIndex n t+zigzagIndex n (t+1)=n := by
  unfold zigzagIndex
  have ho : (t+1)%2=0 := by omega
  rw [if_neg he,if_pos ho]
  omega

lemma zigzag_last_odd {n : ℕ} (hn : 0<n) (he : n%2=1) :
    2*zigzagIndex n (n-1)=n-1 := by
  unfold zigzagIndex
  have ht : (n-1)%2=0 := by omega
  rw [if_pos ht]
  omega

lemma zigzag_last_even {n : ℕ} (hn : 0<n) (he : n%2=0) :
    2*zigzagIndex n (n-1)=n := by
  unfold zigzagIndex
  have ht : (n-1)%2≠0 := by omega
  rw [if_neg ht]
  omega

/-- In zigzag order, the two reflection targets give the path edges and just its final loop. -/
lemma zigzag_incidence_iff {n t s : ℕ} (ht : t<n) (hs : s<n) :
    (zigzagIndex n t+zigzagIndex n s=n-1 ∨ zigzagIndex n t+zigzagIndex n s=n) ↔
      t+1=s ∨ s+1=t ∨ (t=n-1 ∧ s=n-1) := by
  unfold zigzagIndex
  split_ifs <;> omega


namespace ResiduePair
variable {N d : ℕ} (L : ResiduePair N d)

def fixedVertex (t : ℕ) : ℕ := L.left (zigzagIndex L.n t)

lemma fixed_vertex {t : ℕ} (ht : t<L.n) : CarryVertex N (L.fixedVertex t) :=
  L.left_vertex (zigzagIndex_lt ht)

lemma fixed_F_step (hab : L.a=L.b) {t : ℕ} (ht : t+1<L.n) (he : t%2=0) :
    L.fixedVertex t+L.fixedVertex (t+1)=N := by
  have hidx:=zigzag_even_step ht he
  have hend:=L.endpoint
  rw [← hab] at hend
  unfold fixedVertex left
  nlinarith

lemma fixed_G_step (hab : L.a=L.b) {t : ℕ} (ht : t+1<L.n) (he : t%2≠0) :
    L.fixedVertex t+L.fixedVertex (t+1)=N+d := by
  have hidx:=zigzag_odd_step ht he
  have hend:=L.endpoint
  have hn:=L.n_pos
  rw [← hab] at hend
  have hn' : L.n=L.n-1+1 := by omega
  unfold fixedVertex left
  nlinarith

/-- A fixed-class odd-length list ends in precisely the F loop. -/
lemma fixed_F_loop (hab : L.a=L.b) (he : L.n%2=1) :
    2*L.fixedVertex (L.n-1)=N := by
  have hi:=zigzag_last_odd L.n_pos he
  have hend:=L.endpoint
  rw [← hab] at hend
  unfold fixedVertex left
  nlinarith

/-- A fixed-class even-length list ends in precisely the G loop. -/
lemma fixed_G_loop (hab : L.a=L.b) (he : L.n%2=0) :
    2*L.fixedVertex (L.n-1)=N+d := by
  have hi:=zigzag_last_even L.n_pos he
  have hend:=L.endpoint
  have hn:=L.n_pos
  rw [← hab] at hend
  have hn' : L.n=L.n-1+1 := by omega
  unfold fixedVertex left
  nlinarith

/-- Both possible carry loops impose the exact same cap-three unary alphabet. -/
lemma loop_restriction (v : ℕ) : 3≤2*v ↔ 2≤v := by omega

/-- Complete source-edge coverage for a fixed residue class, including its last loop. -/
lemma fixed_incidence_iff (hab : L.a=L.b) {t s : ℕ} (ht : t<L.n) (hs : s<L.n) :
    CarryIncidence N d (L.fixedVertex t) (L.fixedVertex s) ↔
      t+1=s ∨ s+1=t ∨ (t=L.n-1 ∧ s=L.n-1) := by
  have hend:=L.endpoint
  rw [← hab] at hend
  have hm : L.n*d=(L.n-1)*d+d := by
    have hh : L.n=L.n-1+1 := by have hn:=L.n_pos; omega
    calc L.n*d=(L.n-1+1)*d := by rw [← hh]
         _ = (L.n-1)*d+d := by ring
  have hF : L.fixedVertex t+L.fixedVertex s=N ↔
      zigzagIndex L.n t+zigzagIndex L.n s=L.n-1 := by
    unfold fixedVertex left
    constructor
    · intro h
      apply Nat.mul_right_cancel L.d_pos
      nlinarith
    · intro h
      have hh:=congrArg (fun k => k*d) h
      nlinarith
  have hG : L.fixedVertex t+L.fixedVertex s=N+d ↔
      zigzagIndex L.n t+zigzagIndex L.n s=L.n := by
    unfold fixedVertex left
    constructor
    · intro h
      apply Nat.mul_right_cancel L.d_pos
      nlinarith
    · intro h
      have hh:=congrArg (fun k => k*d) h
      nlinarith
  rw [CarryIncidence,hF,hG]
  exact zigzag_incidence_iff ht hs

/-- The fixed-class path starts at its unique port. -/
lemma fixed_port : L.fixedVertex 0=L.a := by
  simp [fixedVertex,zigzagIndex,left]


end ResiduePair

end SubmittedGenus.FixedPivot
