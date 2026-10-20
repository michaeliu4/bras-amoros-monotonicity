import Results.Genus.RawGraph.RawComponents
import Mathlib.Data.Fintype.Sum

namespace SubmittedGenus.RawGraph.Topology

open SourceModel LayoutCompiler SimpleGraph
open scoped BigOperators
noncomputable section

abbrev FullComponent (m r p : ℕ) := Bool ⊕ (freeGraph m r p).ConnectedComponent

noncomputable instance actualFreeComponentFintype (m r p : ℕ) :
    Fintype (freeGraph m r p).ConnectedComponent := Fintype.ofFinite _

noncomputable instance fullComponentFintype (m r p : ℕ) : Fintype (FullComponent m r p) :=
  by
    letI : Fintype (freeGraph m r p).ConnectedComponent := Fintype.ofFinite _
    exact inferInstance

/-- The pivot singleton labels retain their original physical coordinates. -/
def pivotVertex {m r p a : ℕ} (hp : Parameters m r p a) (b : Bool) : Fin (m - 1) :=
  ⟨Incidence.target r p b - 1, by
    have h1 := hp.1; have h2 := hp.2.1; have h3 := hp.2.2.1
    cases b <;> simp only [Incidence.target, Bool.false_eq_true, if_false, if_true] <;> omega⟩

theorem physical_pivotVertex {m r p a : ℕ} (hp : Parameters m r p a) (b : Bool) :
    physical (pivotVertex hp b) = Incidence.target r p b := by
  have h1 := hp.1; have h2 := hp.2.1
  cases b <;> simp only [pivotVertex, physical, Incidence.target, Bool.false_eq_true,
    if_false, if_true] <;> omega

def pivotFreeEquiv {m r p a : ℕ} (hp : Parameters m r p a) :
    Bool ⊕ FreeVertex m r p ≃ Fin (m - 1) :=
  Equiv.ofBijective (Sum.elim (pivotVertex hp) Subtype.val) (by
    constructor
    · intro x y h
      cases x with
      | inl b =>
        cases y with
        | inl c =>
          have hh := congrArg physical h
          change physical (pivotVertex hp b) = physical (pivotVertex hp c) at hh
          rw [physical_pivotVertex, physical_pivotVertex] at hh
          have hrp := hp.2.1
          have he : b = c := by cases b <;> cases c <;> simp_all [Incidence.target]
          exact congrArg Sum.inl he
        | inr v =>
          have hv := v.property
          change ¬ IsPivot r p v.val at hv
          have hh := congrArg physical h
          change physical (pivotVertex hp b) = physical v.val at hh
          rw [physical_pivotVertex] at hh
          cases b <;> simp_all [Incidence.target, IsPivot]
      | inr u =>
        cases y with
        | inl c =>
          have hu := u.property
          change ¬ IsPivot r p u.val at hu
          have hh := congrArg physical h
          change physical u.val = physical (pivotVertex hp c) at hh
          rw [physical_pivotVertex] at hh
          cases c <;> simp_all [Incidence.target, IsPivot]
        | inr v => exact congrArg Sum.inr (Subtype.ext h)
    · intro i
      by_cases hr : physical i = r
      · refine ⟨Sum.inl false, ?_⟩
        change pivotVertex hp false = i
        apply Fin.ext
        have hh := physical_pivotVertex hp false
        dsimp [Incidence.target, physical] at hh hr
        omega
      · by_cases hpp : physical i = p
        · refine ⟨Sum.inl true, ?_⟩
          change pivotVertex hp true = i
          apply Fin.ext
          have hh := physical_pivotVertex hp true
          dsimp [Incidence.target, physical] at hh hpp
          omega
        · exact ⟨Sum.inr ⟨i, by simp [IsFree, IsPivot, hr, hpp]⟩, rfl⟩)

def fullEdges (m r p : ℕ) : FullComponent m r p → ℕ
  | .inl _ => 0
  | .inr c => (freeComponentOrder m r p c).edges

def fullCycle (m r p : ℕ) : FullComponent m r p → Bool
  | .inl _ => false
  | .inr c => (freeComponentOrder m r p c).cycle

def singletonPositions : (Σ _ : Bool, Fin 1) ≃ Bool where
  toFun x := x.1
  invFun b := ⟨b, 0⟩
  left_inv x := by
    rcases x with ⟨b, j⟩
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    rfl
  right_inv _ := rfl

def fullVertexEquiv {m r p a : ℕ} (hp : Parameters m r p a) :
    (Σ c : FullComponent m r p, Fin (fullEdges m r p c + 1)) ≃ Fin (m - 1) :=
  (Equiv.sumSigmaDistrib _).trans
    ((Equiv.sumCongr singletonPositions (freeOrderedVertexEquiv m r p)).trans
      (pivotFreeEquiv hp))

def fullIndexEquiv (m r p : ℕ) :
    Fin (Fintype.card (FullComponent m r p)) ≃ FullComponent m r p :=
  (Fintype.equivFin _).symm

/-- A source-complete actual layout exists for every valid parameter triple.
The two pivots are separate singletons, followed by all genuine free components. -/
def actualLayout {m r p a : ℕ} (hp : Parameters m r p a) : Layout m where
  count := Fintype.card (FullComponent m r p)
  edges c := fullEdges m r p (fullIndexEquiv m r p c)
  cycle c := fullCycle m r p (fullIndexEquiv m r p c)
  label := (Equiv.sigmaCongrLeft (fullIndexEquiv m r p)).trans (fullVertexEquiv hp)

theorem fullVertexEquiv_pivot {m r p a : ℕ} (hp : Parameters m r p a) (b : Bool)
    (j : Fin 1) : fullVertexEquiv hp ⟨Sum.inl b, j⟩ = pivotVertex hp b := rfl

theorem fullVertexEquiv_free {m r p a : ℕ} (hp : Parameters m r p a)
    (c : (freeGraph m r p).ConnectedComponent)
    (j : Fin ((freeComponentOrder m r p c).edges + 1)) :
    fullVertexEquiv hp ⟨Sum.inr c, j⟩ =
      ((freeComponentOrder m r p c).label j).val.val := rfl

theorem edgeBound_pos_rawGraph {m r p a : ℕ} {i j : Fin (m - 1)}
    (h : 0 < edgeBound r p a i j) : (rawGraph m r p).Adj i j := by
  unfold edgeBound at h
  split_ifs at h with hbad hs hc
  · omega
  · simp only [not_or] at hbad
    exact ⟨hbad.2.2, hbad.1, hbad.2.1, by
      rcases hs with hs | hs
      · exact Or.inl (Or.inl hs)
      · exact Or.inr (Or.inl hs)⟩
  · simp only [not_or] at hbad
    exact ⟨hbad.2.2, hbad.1, hbad.2.1, by
      rcases hc with hc | hc
      · exact Or.inl (Or.inr hc)
      · exact Or.inr (Or.inr hc)⟩
  · omega


theorem actualLayout_covers {m r p a : ℕ} (hp : Parameters m r p a) :
    Covers (actualLayout hp) r p a := by
  classical
  intro u v huv
  have ha := edgeBound_pos_rawGraph huv
  let uf : FreeVertex m r p := ⟨u, ha.2.1⟩
  let vf : FreeVertex m r p := ⟨v, ha.2.2.1⟩
  have haf : (freeGraph m r p).Adj uf vf := ha
  let c := (freeGraph m r p).connectedComponentMk uf
  let uu : c := ⟨uf, rfl⟩
  let vv : c := ⟨vf, (ConnectedComponent.connectedComponentMk_eq_of_adj haf).symm⟩
  let O := freeComponentOrder m r p c
  let i := O.label.symm uu
  let j := O.label.symm vv
  have hi : fullVertexEquiv hp ⟨Sum.inr c, i⟩ = u := by
    change (O.label (O.label.symm uu)).val.val = u
    simp [uu, uf]
  have hj : fullVertexEquiv hp ⟨Sum.inr c, j⟩ = v := by
    change (O.label (O.label.symm vv)).val.val = v
    simp [vv, vf]
  have hadj : c.toSimpleGraph.Adj (O.label i) (O.label j) := by
    rw [show O.label i = uu from O.label.apply_symm_apply uu,
      show O.label j = vv from O.label.apply_symm_apply vv]
    exact haf
  have hpos := (O.adjacent_iff i j).mp hadj
  have hfull : ∃ d : FullComponent m r p,
      (∃ k : Fin (fullEdges m r p d),
        (fullVertexEquiv hp ⟨d, k.castSucc⟩ = u ∧ fullVertexEquiv hp ⟨d, k.succ⟩ = v) ∨
        (fullVertexEquiv hp ⟨d, k.castSucc⟩ = v ∧ fullVertexEquiv hp ⟨d, k.succ⟩ = u)) ∨
      (fullCycle m r p d = true ∧
        ((fullVertexEquiv hp ⟨d, Fin.last (fullEdges m r p d)⟩ = u ∧
            fullVertexEquiv hp ⟨d, 0⟩ = v) ∨
          (fullVertexEquiv hp ⟨d, Fin.last (fullEdges m r p d)⟩ = v ∧
            fullVertexEquiv hp ⟨d, 0⟩ = u))) := by
    refine ⟨Sum.inr c, ?_⟩
    rcases hpos with hij | hji | ⟨hc, hcpos⟩
    · left
      let k : Fin O.edges := ⟨i.val, by have := j.isLt; omega⟩
      have hki : k.castSucc = i := Fin.ext rfl
      have hkj : k.succ = j := Fin.ext hij
      exact ⟨k, Or.inl ⟨(congrArg (fun t : Fin (O.edges + 1) => fullVertexEquiv hp ⟨Sum.inr c, t⟩) hki).trans hi,
        (congrArg (fun t : Fin (O.edges + 1) => fullVertexEquiv hp ⟨Sum.inr c, t⟩) hkj).trans hj⟩⟩
    · left
      let k : Fin O.edges := ⟨j.val, by have := i.isLt; omega⟩
      have hkj : k.castSucc = j := Fin.ext rfl
      have hki : k.succ = i := Fin.ext hji
      exact ⟨k, Or.inr ⟨(congrArg (fun t : Fin (O.edges + 1) => fullVertexEquiv hp ⟨Sum.inr c, t⟩) hkj).trans hj,
        (congrArg (fun t : Fin (O.edges + 1) => fullVertexEquiv hp ⟨Sum.inr c, t⟩) hki).trans hi⟩⟩
    · right
      refine ⟨hc, ?_⟩
      rcases hcpos with ⟨hi0, hjn⟩ | ⟨hj0, hin⟩
      · have hi0' : i = 0 := Fin.ext hi0
        have hjn' : j = Fin.last O.edges := Fin.ext hjn
        exact Or.inr ⟨(congrArg (fun t : Fin (O.edges + 1) => fullVertexEquiv hp ⟨Sum.inr c, t⟩) hjn'.symm).trans hj,
          (congrArg (fun t : Fin (O.edges + 1) => fullVertexEquiv hp ⟨Sum.inr c, t⟩) hi0'.symm).trans hi⟩
      · have hj0' : j = 0 := Fin.ext hj0
        have hin' : i = Fin.last O.edges := Fin.ext hin
        exact Or.inl ⟨(congrArg (fun t : Fin (O.edges + 1) => fullVertexEquiv hp ⟨Sum.inr c, t⟩) hin'.symm).trans hi,
          (congrArg (fun t : Fin (O.edges + 1) => fullVertexEquiv hp ⟨Sum.inr c, t⟩) hj0'.symm).trans hj⟩
  obtain ⟨d, hd⟩ := hfull
  obtain ⟨k, rfl⟩ := (fullIndexEquiv m r p).surjective d
  exact ⟨k, hd⟩

/-- The original raw polynomial is evaluated by the actual, universally
constructed component transfers, with no external layout premise. -/
theorem rawPolynomial_eq_actual_components {m r p a : ℕ} (hp : Parameters m r p a) :
    rawPolynomial m r p a =
      ∏ c : Fin (actualLayout hp).count, componentRun (actualLayout hp) r p a c :=
  rawPolynomial_eq_components (actualLayout hp) hp (actualLayout_covers hp)


theorem freeVertex_card {m r p a : ℕ} (hp : Parameters m r p a)
    [Fintype (FreeVertex m r p)] : Fintype.card (FreeVertex m r p) = m - 3 := by
  have hh := Fintype.card_congr (pivotFreeEquiv hp)
  simp only [Fintype.card_sum, Fintype.card_bool, Fintype.card_fin] at hh
  have h1 := hp.1; have h2 := hp.2.1; have h3 := hp.2.2.1
  omega

/-- Generic-index form of the exact source polynomial of one actual component. -/
def fullComponentPolynomial {m r p a : ℕ} (hp : Parameters m r p a)
    (c : FullComponent m r p) : Polynomial ℕ :=
  ∑ x : Fin (fullEdges m r p c + 1) → Fin (a + 1),
    (∏ j, vertexWeight r p a (fullVertexEquiv hp ⟨c, j⟩) (x j)) *
      (∏ j : Fin (fullEdges m r p c), edgeWeight r p a
        (fullVertexEquiv hp ⟨c, j.castSucc⟩) (fullVertexEquiv hp ⟨c, j.succ⟩)
        (x j.castSucc) (x j.succ)) *
      (if fullCycle m r p c = true then edgeWeight r p a
        (fullVertexEquiv hp ⟨c, Fin.last _⟩) (fullVertexEquiv hp ⟨c, 0⟩)
        (x (Fin.last _)) (x 0) else 1)

theorem actual_componentRun_eq {m r p a : ℕ} (hp : Parameters m r p a)
    (k : Fin (actualLayout hp).count) :
    componentRun (actualLayout hp) r p a k =
      fullComponentPolynomial hp (fullIndexEquiv m r p k) := by
  rw [componentRun_eq_source]
  rfl

/-- Canonical source factorization indexed by the two pivots and actual free
components. The physical-coordinate bijection supplies every weight once. -/
theorem rawPolynomial_eq_full_components {m r p a : ℕ} (hp : Parameters m r p a) :
    rawPolynomial m r p a = ∏ c : FullComponent m r p, fullComponentPolynomial hp c := by
  rw [rawPolynomial_eq_actual_components hp]
  simp_rw [actual_componentRun_eq]
  exact (fullIndexEquiv m r p).prod_comp (fullComponentPolynomial hp)

theorem fullComponentPolynomial_pivot {m r p a : ℕ} (hp : Parameters m r p a)
    (b : Bool) : fullComponentPolynomial hp (Sum.inl b) = Polynomial.X ^ a := by
  classical
  have hpiv : IsPivot r p (pivotVertex hp b) := by
    unfold IsPivot
    rw [physical_pivotVertex]
    cases b <;> simp [Incidence.target]
  have hv (v : Fin (a + 1)) : vertexWeight r p a (pivotVertex hp b) v =
      if v.val = a then Polynomial.X ^ a else 0 := by
    simp only [vertexWeight, Domain, IsFree, hpiv, not_true_eq_false,
      false_implies, implies_true, and_true, true_implies]
    by_cases h : v.val = a <;> simp [h]
  unfold fullComponentPolynomial
  change (∑ x : Fin 1 → Fin (a + 1),
    (∏ j : Fin 1, vertexWeight r p a (pivotVertex hp b) (x j)) *
      (∏ j : Fin 0, edgeWeight r p a (pivotVertex hp b) (pivotVertex hp b)
        (x j.castSucc) (x j.succ)) * 1) = _
  simp only [Fin.prod_univ_one, Fin.prod_univ_zero, mul_one]
  simp_rw [hv]
  rw [show (∑ x : Fin 1 → Fin (a + 1), if (x 0).val = a then Polynomial.X ^ a else 0) =
      ∑ v : Fin (a + 1), if v.val = a then Polynomial.X ^ a else 0 from
    by simpa [Equiv.funUnique] using
      (Equiv.funUnique (Fin 1) (Fin (a + 1))).sum_comp
        (fun v : Fin (a + 1) => if v.val = a then Polynomial.X ^ a else 0)]
  have he (v : Fin (a + 1)) : v.val = a ↔ v = ⟨a, Nat.lt_succ_self a⟩ := by
    constructor
    · intro h; apply Fin.ext; exact h
    · intro h; exact congrArg Fin.val h
  simp_rw [he]
  simp

/-- The original raw polynomial has exactly the two fixed pivot weights times
the product of source-exact free-component polynomials. -/
theorem rawPolynomial_eq_pivots_free {m r p a : ℕ} (hp : Parameters m r p a) :
    rawPolynomial m r p a = Polynomial.X ^ (2 * a) *
      ∏ c : (freeGraph m r p).ConnectedComponent, fullComponentPolynomial hp (Sum.inr c) := by
  rw [rawPolynomial_eq_full_components hp]
  rw [Fintype.prod_sum_type]
  simp_rw [fullComponentPolynomial_pivot]
  simp only [Fintype.prod_bool, ← pow_add, two_mul]

end
end SubmittedGenus.RawGraph.Topology
