import Mathlib.Data.List.Rotate
import Mathlib.Data.List.Basic
import Lean.Elab.Tactic.Omega

namespace SubmittedGenus.CapFourMass.CyclicColors

lemma first_true {l : List Bool} (ht : true∈l) :
    ∃ n b,l=List.replicate n false ++ true::b := by
  induction l with
  | nil => simp at ht
  | cons a l ih =>
    cases a
    · obtain ⟨n,b,h⟩ := ih (by simpa using ht)
      exact ⟨n+1,b,by simp [List.replicate_succ,h]⟩
    · exact ⟨0,l,by simp⟩

lemma split_member {α : Type*} {x : α} {l : List α} (hx : x∈l) :
    ∃a b,l=a++x::b := by
  induction l with
  | nil => simp at hx
  | cons y l ih =>
    rcases List.mem_cons.mp hx with h | h
    · subst y
      exact ⟨[],l,rfl⟩
    · obtain ⟨a,b,hab⟩ := ih h
      exact ⟨y::a,b,by simp [hab]⟩

lemma replicate_last (k : ℕ) : (List.replicate (k+1) false).getLast?=some false := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [List.replicate_succ] using ih

/-- Any genuinely mixed cycle can be cut at a false-to-true boundary. -/
theorem exists_rotation {l : List Bool} (ht : true∈l) (hf : false∈l) :
    ∃ n,(l.rotate n).head?=some true ∧ (l.rotate n).getLast?=some false ∧
      (l.rotate n).Perm l := by
  obtain ⟨a,b,hab⟩ := split_member hf
  have hrot : l.rotate a.length = false::(b++a) := by
    rw [hab,List.rotate_append_length_eq]
    rfl
  have ht' : true∈(false::(b++a)) := by
    rw [←hrot]
    exact (List.rotate_perm l a.length).mem_iff.mpr ht
  obtain ⟨k,c,hk⟩ := first_true ht'
  have hkpos : 0<k := by
    cases k with
    | zero => simp at hk
    | succ k => omega
  have hsecond : (l.rotate a.length).rotate k =
      (true::c)++List.replicate k false := by
    rw [hrot,hk]
    simpa using List.rotate_append_length_eq (List.replicate k false) (true::c)
  refine ⟨a.length+k,?_,?_,List.rotate_perm ..⟩
  · rw [←List.rotate_rotate,hsecond]
    simp
  · rw [←List.rotate_rotate,hsecond]
    rw [List.getLast?_append_of_ne_nil _ (by simpa using ne_of_gt hkpos)]
    cases k with
    | zero => omega
    | succ k => exact replicate_last k

theorem exists_colored_rotation {α : Type*} (color : α → Bool) {l : List α}
    (ht : true∈l.map color) (hf : false∈l.map color) :
    ∃ n,((l.rotate n).map color).head?=some true ∧
      ((l.rotate n).map color).getLast?=some false ∧ (l.rotate n).Perm l := by
  obtain ⟨n,hn,hl,_⟩ := exists_rotation ht hf
  exact ⟨n,by simpa [List.map_rotate] using hn,
    by simpa [List.map_rotate] using hl,List.rotate_perm ..⟩

#print axioms exists_rotation
#print axioms exists_colored_rotation
end SubmittedGenus.CapFourMass.CyclicColors
