import Results.Genus.CapFourMass.CycleWords
import Results.Genus.CapFourMass.CyclicColors
import Results.Genus.CapFourMass.RunCounts

/-! Cutting the actual cyclic word at a genuine strong/carry transition. -/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFourMass.ActualComponent
open RawGraph RawGraph.Topology

/-- Adjacency together with its closing incidence, including arbitrary list cuts. -/
def CyclicChain {A : Type*} (R : A→A→Prop) (l : List A) : Prop :=
  l.IsChain R ∧ ∀ x∈l.getLast?,∀ y∈l.head?,R x y

lemma cyclicChain_rotate_one {A : Type*} {R : A→A→Prop} {l : List A}
    (h : CyclicChain R l) : CyclicChain R (l.rotate 1) := by
  cases l with
  | nil => simpa using h
  | cons a l =>
    cases l with
    | nil => simpa using h
    | cons b l =>
      rw [show 1=0+1 from rfl,List.rotate_cons_succ,List.rotate_zero]
      constructor
      · apply List.IsChain.append h.1.tail (by simp)
        intro x hx y hy
        have hy' : y=a := by simpa using (Option.mem_some_iff.mp hy).symm
        subst y
        exact h.2 x (by simpa using hx) a (by simp)
      · intro x hx y hy
        have hx' : x=a := by simpa using (Option.mem_some_iff.mp hx).symm
        have hy' : y=b := by simpa using (Option.mem_some_iff.mp hy).symm
        subst x; subst y
        exact h.1.rel

lemma cyclicChain_rotate {A : Type*} {R : A→A→Prop} {l : List A}
    (h : CyclicChain R l) (n : ℕ) : CyclicChain R (l.rotate n) := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    rw [← List.rotate_rotate]
    exact cyclicChain_rotate_one ih

lemma closedWord_cyclic_compatible {m r p : ℕ} (hp : RawGraph.Parameters m r p 4)
    (c : Component m r p) (hc : (freeComponentOrder m r p c).cycle=true) :
    CyclicChain CompatibleKinds (closedWord c) := by
  refine ⟨closedWord_compatible hp c hc,?_⟩
  have hn : 3≤edgeCount c := (freeComponentOrder m r p c).cycle_min hc
  have hnon : pathWord c≠[] := by intro h; have := congrArg List.length h; simp at this; omega
  intro x hx y hy
  have hx' : x=kind r p (vertex c (Fin.last _)) (vertex c 0) := by
    simp only [closedWord,List.getLast?_append,List.getLast?_cons,List.getLast?_nil] at hx
    exact (Option.mem_some_iff.mp hx).symm
  have hy' : y=kind r p (vertex c (Fin.castSucc ⟨0,by omega⟩)) (vertex c (Fin.succ ⟨0,by omega⟩)) := by
    rw [closedWord,List.head?_append_of_ne_nil _ hnon,List.head?_eq_some_head hnon] at hy
    have he := (Option.mem_some_iff.mp hy).symm
    simpa only [pathWord,List.head_ofFn] using he
  subst x; subst y
  apply neighbor_compatible hp (closing_adj c hc) (consecutive_adj c ⟨0,by omega⟩)
  intro he
  have hh := congrArg Fin.val (vertex_injective c he)
  simp only [Fin.val_last,Fin.val_succ] at hh
  omega

/-- Matrix trace is invariant under the same actual cyclic edge rotation. -/
lemma matrix_word_trace_rotate {A : Type*} (f : A→Matrix State State ℝ) (l : List A) (n : ℕ) :
    (((l.rotate n).map f).prod).trace=((l.map f).prod).trace := by
  rw [List.rotate_eq_drop_append_take_mod]
  simp only [List.map_append,List.prod_append]
  rw [Matrix.trace_mul_comm]
  rw [← List.prod_append,← List.map_append,List.take_append_drop]

/-- A real source cycle admits a source-preserving cut with a strong first
run and a carry last run; both are nonempty and all E runs remain singletons. -/
theorem actual_cycle_run_cut {m r p : ℕ} (hp : RawGraph.Parameters m r p 4)
    (c : Component m r p) (hc : (freeComponentOrder m r p c).cycle=true) :
    ∃ n,
      (((closedWord c).rotate n).map strongColor).head?=some true ∧
      (((closedWord c).rotate n).map strongColor).getLast?=some false ∧
      ((closedWord c).rotate n).IsChain CompatibleKinds ∧
      ((closedWord c).rotate n).Perm (closedWord c) ∧
      componentMass c ≤ ((((closedWord c).rotate n).map EdgeKind.matrix).prod).trace := by
  obtain ⟨ht,hf⟩ := closedWord_both_colors hp c hc
  obtain ⟨n,hn,hl,hperm⟩ := CyclicColors.exists_colored_rotation strongColor ht hf
  refine ⟨n,hn,hl,(cyclicChain_rotate (closedWord_cyclic_compatible hp c hc) n).1,hperm,?_⟩
  rw [matrix_word_trace_rotate,closedWord_matrix]
  exact componentMass_cycle_le_base hp c hc

lemma rotated_exponents (l : List EdgeKind) (n : ℕ) :
    strongLength (l.rotate n)=strongLength l ∧ carryLength (l.rotate n)=carryLength l ∧
      restrictedLength (l.rotate n)=restrictedLength l := by
  have h := List.rotate_perm l n
  exact ⟨(h.map _).sum_eq,(h.map _).sum_eq,(h.map _).sum_eq⟩

end SubmittedGenus.CapFourMass.ActualComponent
