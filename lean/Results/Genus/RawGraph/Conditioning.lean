import Results.Genus.RawGraph.Layout
import Mathlib.Data.Fintype.Sum

/-!
# Conditioning the original raw source on a finite core

The core and tail positions are a disjoint cover of physical coordinates.
Core-tail edges are imposed in the tail unary weight after the core is fixed.
This gives an exact finite-core contraction without copying endpoint weights.
-/
namespace SubmittedGenus.RawGraph.Conditioning
open SourceModel Factorization LayoutCompiler
open scoped BigOperators

structure Layout (m : ℕ) (K C : Type*) where
  edges : C → ℕ
  cycle : C → Bool
  label : (K ⊕ (Σ c, Fin (edges c + 1))) ≃ Fin (m - 1)

variable {m r p a : ℕ} {K C : Type*} [Fintype K] [Fintype C]
  [DecidableEq K] [DecidableEq C]

abbrev coreVertex (L : Layout m K C) (k : K) := L.label (Sum.inl k)
abbrev tailVertex (L : Layout m K C) (c : C) (j : Fin (L.edges c + 1)) := L.label (Sum.inr ⟨c, j⟩)

def TailAdjacent (L : Layout m K C) (u v : Σ c, Fin (L.edges c + 1)) : Prop :=
  ∃ c : C,
    (∃ j : Fin (L.edges c),
      (u = ⟨c, j.castSucc⟩ ∧ v = ⟨c, j.succ⟩) ∨
      (v = ⟨c, j.castSucc⟩ ∧ u = ⟨c, j.succ⟩)) ∨
    (L.cycle c = true ∧
      ((u = ⟨c, Fin.last (L.edges c)⟩ ∧ v = ⟨c, 0⟩) ∨
       (v = ⟨c, Fin.last (L.edges c)⟩ ∧ u = ⟨c, 0⟩)))

def Covers (L : Layout m K C) (r p a : ℕ) : Prop :=
  ∀ u v, 0 < edgeBound r p a (L.label (Sum.inr u)) (L.label (Sum.inr v)) → TailAdjacent L u v

def CoreAllowed (L : Layout m K C) (r p a : ℕ) (x : K → Fin (a + 1)) : Prop :=
  (∀ k, Domain r p a (coreVertex L k) (x k).val) ∧
    ∀ k l, edgeBound r p a (coreVertex L k) (coreVertex L l) ≤ (x k).val + (x l).val

def TailUnary (L : Layout m K C) (r p a : ℕ) (x : K → Fin (a + 1))
    (c : C) (j : Fin (L.edges c + 1)) (v : Fin (a + 1)) : Prop :=
  Domain r p a (tailVertex L c j) v.val ∧
    ∀ k, edgeBound r p a (coreVertex L k) (tailVertex L c j) ≤ (x k).val + v.val

def TailAllowed (L : Layout m K C) (r p a : ℕ) (x : K → Fin (a + 1))
    (c : C) (y : Fin (L.edges c + 1) → Fin (a + 1)) : Prop :=
  (∀ j, TailUnary L r p a x c j (y j)) ∧
    (∀ j : Fin (L.edges c), edgeBound r p a (tailVertex L c j.castSucc)
      (tailVertex L c j.succ) ≤ (y j.castSucc).val + (y j.succ).val) ∧
    (L.cycle c = true → edgeBound r p a (tailVertex L c (Fin.last _))
      (tailVertex L c 0) ≤ (y (Fin.last _)).val + (y 0).val)

instance (L : Layout m K C) (r p a : ℕ) (x : K → Fin (a + 1)) :
    Decidable (CoreAllowed L r p a x) := by unfold CoreAllowed; infer_instance
instance (L : Layout m K C) (r p a : ℕ) (x : K → Fin (a + 1))
    (c : C) (j : Fin (L.edges c + 1)) (v : Fin (a + 1)) :
    Decidable (TailUnary L r p a x c j v) := by unfold TailUnary; infer_instance
instance (L : Layout m K C) (r p a : ℕ) (x : K → Fin (a + 1))
    (c : C) (y : Fin (L.edges c + 1) → Fin (a + 1)) :
    Decidable (TailAllowed L r p a x c y) := by unfold TailAllowed; infer_instance

/-- Conditioning preserves precisely the original alphabets and every retained
ordinary, carried and self constraint. -/
theorem raw_iff_conditioned (L : Layout m K C) (hp : Parameters m r p a)
    (hc : Covers L r p a) (z : Fin (m - 1) → Fin (a + 1)) :
    RawAdmissible r p a (boundedWord z) ↔
      CoreAllowed L r p a (fun k => z (coreVertex L k)) ∧
        ∀ c, TailAllowed L r p a (fun k => z (coreVertex L k)) c
          (fun j => z (tailVertex L c j)) := by
  rw [raw_iff_compiled]
  constructor
  · intro h
    refine ⟨⟨fun k => h.2.1 _, fun k l => admissible_edge_all h _ _⟩, ?_⟩
    intro c
    exact ⟨fun j => ⟨h.2.1 _, fun k => admissible_edge_all h _ _⟩,
      fun j => admissible_edge_all h _ _, fun _ => admissible_edge_all h _ _⟩
  · rintro ⟨hx, hy⟩
    refine ⟨hp, ?_, ?_⟩
    · intro i
      obtain ⟨k | ⟨c, j⟩, rfl⟩ := L.label.surjective i
      · exact hx.1 k
      · exact (hy c).1 j |>.1
    · intro i j _
      obtain ⟨u, rfl⟩ := L.label.surjective i
      obtain ⟨v, rfl⟩ := L.label.surjective j
      cases u with
      | inl k =>
        cases v with
        | inl l => exact hx.2 k l
        | inr w => exact ((hy w.1).1 w.2).2 k
      | inr u =>
        cases v with
        | inl k => simpa only [boundedWord, coreVertex, tailVertex, edgeBound_symm, Nat.add_comm] using ((hy u.1).1 u.2).2 k
        | inr v =>
          by_cases he : edgeBound r p a (L.label (.inr u)) (L.label (.inr v)) = 0
          · rw [he]; exact Nat.zero_le _
          obtain ⟨c, hedge | hclose⟩ := hc u v (Nat.pos_of_ne_zero he)
          · obtain ⟨k, h | h⟩ := hedge
            · rcases h with ⟨rfl, rfl⟩; exact (hy c).2.1 k
            · rcases h with ⟨rfl, rfl⟩
              simpa only [boundedWord, coreVertex, tailVertex, edgeBound_symm, Nat.add_comm] using (hy c).2.1 k
          · obtain ⟨hcy, h | h⟩ := hclose
            · rcases h with ⟨rfl, rfl⟩; exact (hy c).2.2 hcy
            · rcases h with ⟨rfl, rfl⟩
              simpa only [boundedWord, coreVertex, tailVertex, edgeBound_symm, Nat.add_comm] using (hy c).2.2 hcy

noncomputable def coreTerm (L : Layout m K C) (r p a : ℕ) (x : K → Fin (a + 1)) : Polynomial ℕ :=
  if CoreAllowed L r p a x then Polynomial.X ^ (∑ k, (x k).val) else 0

noncomputable def tailTerm (L : Layout m K C) (r p a : ℕ) (x : K → Fin (a + 1))
    (c : C) (y : Fin (L.edges c + 1) → Fin (a + 1)) : Polynomial ℕ :=
  if TailAllowed L r p a x c y then Polynomial.X ^ (∑ j, (y j).val) else 0

noncomputable def componentPolynomial (L : Layout m K C) (r p a : ℕ)
    (x : K → Fin (a + 1)) (c : C) : Polynomial ℕ := ∑ y, tailTerm L r p a x c y


theorem sum_core_tail {W A R : Type*} [Fintype W] [DecidableEq W]
    [Fintype A] [AddCommMonoid R] (f : (K ⊕ W → A) → R) :
    (∑ z, f z) = ∑ x : K → A, ∑ y : W → A, f (Sum.elim x y) := by
  classical
  calc
    (∑ z, f z) = ∑ xy : (K → A) × (W → A),
      f ((Equiv.sumArrowEquivProdArrow K W A).symm xy) :=
      ((Equiv.sumArrowEquivProdArrow K W A).symm.sum_comp f).symm
    _ = _ := by rw [Fintype.sum_prod_type]; rfl

/-- Exact finite-core contraction of the original raw source. The core and
tail assignments are disjoint; no port or endpoint weight is duplicated. -/
theorem rawPolynomial_eq_conditioned (L : Layout m K C) (hp : Parameters m r p a)
    (hc : Covers L r p a) :
    rawPolynomial m r p a = ∑ x : K → Fin (a + 1),
      coreTerm L r p a x * ∏ c : C, componentPolynomial L r p a x c := by
  classical
  unfold rawPolynomial
  rw [sum_assignments_reindex L.label, sum_core_tail]
  apply Finset.sum_congr rfl
  intro x _
  unfold componentPolynomial
  rw [← sum_product_components, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  have he : RawAdmissible r p a
      (boundedWord (fun v => Sum.elim x y (L.label.symm v))) ↔
      CoreAllowed L r p a x ∧ ∀ c, TailAllowed L r p a x c (fun j => y ⟨c, j⟩) := by
    simpa only [coreVertex, tailVertex, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr]
      using raw_iff_conditioned L hp hc (fun v => Sum.elim x y (L.label.symm v))
  have hg : genus (boundedWord (fun v => Sum.elim x y (L.label.symm v))) =
      (∑ k, (x k).val) + ∑ c, ∑ j, (y ⟨c, j⟩).val := by
    unfold genus boundedWord
    rw [← L.label.sum_comp (fun v => (Sum.elim x y (L.label.symm v)).val)]
    simp only [Equiv.symm_apply_apply, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      Fintype.sum_sigma]
  unfold tailTerm
  rw [prod_gated_powers]
  simp only [he, hg, coreTerm]
  split_ifs <;> simp_all [pow_add]

noncomputable def unaryWeight (L : Layout m K C) (r p a : ℕ) (x : K → Fin (a + 1))
    (c : C) (j : Fin (L.edges c + 1)) (v : Fin (a + 1)) : Polynomial ℕ :=
  if TailUnary L r p a x c j v then Polynomial.X ^ v.val else 0

noncomputable def componentTerm (L : Layout m K C) (r p a : ℕ) (x : K → Fin (a + 1))
    (c : C) (y : Fin (L.edges c + 1) → Fin (a + 1)) : Polynomial ℕ :=
  (∏ j, unaryWeight L r p a x c j (y j)) *
    (∏ j : Fin (L.edges c), edgeWeight r p a (tailVertex L c j.castSucc)
      (tailVertex L c j.succ) (y j.castSucc) (y j.succ)) *
    (if L.cycle c = true then edgeWeight r p a (tailVertex L c (Fin.last _))
      (tailVertex L c 0) (y (Fin.last _)) (y 0) else 1)

theorem componentTerm_eq_tailTerm (L : Layout m K C) (r p a : ℕ) (x : K → Fin (a + 1))
    (c : C) (y : Fin (L.edges c + 1) → Fin (a + 1)) :
    componentTerm L r p a x c y = tailTerm L r p a x c y := by
  classical
  unfold componentTerm unaryWeight edgeWeight tailTerm
  rw [prod_gated_powers, prod_gate]
  simp only [Finset.prod_const_one]
  unfold TailAllowed
  split_ifs <;> simp_all

noncomputable def transferVertices (L : Layout m K C) (r p a : ℕ) (x : K → Fin (a + 1))
    (c : C) (j : ℕ) (v : Fin (a + 1)) : Polynomial ℕ :=
  if h : j < L.edges c + 1 then unaryWeight L r p a x c ⟨j, h⟩ v else 0
noncomputable def transferEdges (L : Layout m K C) (r p a : ℕ)
    (c : C) (j : ℕ) (v w : Fin (a + 1)) : Polynomial ℕ :=
  if h : j < L.edges c then edgeWeight r p a (tailVertex L c (⟨j, h⟩ : Fin (L.edges c)).castSucc)
    (tailVertex L c (⟨j, h⟩ : Fin (L.edges c)).succ) v w else 1
noncomputable def transferClose (L : Layout m K C) (r p a : ℕ)
    (c : C) (v w : Fin (a + 1)) : Polynomial ℕ :=
  edgeWeight r p a (tailVertex L c (Fin.last _)) (tailVertex L c 0) v w

@[simp] theorem transferVertices_fin (L : Layout m K C) (r p a : ℕ) (x : K → Fin (a + 1))
    (c : C) (j : Fin (L.edges c + 1)) (v : Fin (a + 1)) :
    transferVertices L r p a x c j.val v = unaryWeight L r p a x c j v := by
  simp only [transferVertices, dif_pos j.isLt]
@[simp] theorem transferEdges_fin (L : Layout m K C) (r p a : ℕ)
    (c : C) (j : Fin (L.edges c)) (v w : Fin (a + 1)) :
    transferEdges L r p a c j.val v w = edgeWeight r p a
      (tailVertex L c j.castSucc) (tailVertex L c j.succ) v w := by
  simp only [transferEdges, dif_pos j.isLt]

noncomputable def componentRun (L : Layout m K C) (r p a : ℕ) (x : K → Fin (a + 1))
    (c : C) : Polynomial ℕ :=
  if L.cycle c = true then Transfer.cycleRun (L.edges c)
    (transferVertices L r p a x c) (transferEdges L r p a c) (transferClose L r p a c)
  else Transfer.pathRun (L.edges c) (transferVertices L r p a x c) (transferEdges L r p a c)

/-- The core-conditioned source sum is evaluated by the existing exact transfer. -/
theorem componentRun_eq_polynomial (L : Layout m K C) (r p a : ℕ) (x : K → Fin (a + 1))
    (c : C) : componentRun L r p a x c = componentPolynomial L r p a x c := by
  classical
  unfold componentRun componentPolynomial
  simp_rw [← componentTerm_eq_tailTerm]
  split_ifs with hc
  · rw [Transfer.cycleRun_eq_source]
    unfold Transfer.cycleSource
    apply Finset.sum_congr rfl
    intro y _
    simp only [Transfer.sourceTerm, componentTerm, transferVertices_fin, transferEdges_fin,
      transferClose, hc, if_true]
  · rw [Transfer.pathRun_eq_source]
    unfold Transfer.pathSource
    apply Finset.sum_congr rfl
    intro y _
    simp only [Transfer.sourceTerm, componentTerm, transferVertices_fin, transferEdges_fin,
      hc, Bool.false_eq_true, if_false]

theorem rawPolynomial_eq_conditioned_transfer (L : Layout m K C) (hp : Parameters m r p a)
    (hc : Covers L r p a) :
    rawPolynomial m r p a = ∑ x : K → Fin (a + 1),
      coreTerm L r p a x * ∏ c : C, componentRun L r p a x c := by
  simp_rw [componentRun_eq_polynomial]
  exact rawPolynomial_eq_conditioned L hp hc

end SubmittedGenus.RawGraph.Conditioning
