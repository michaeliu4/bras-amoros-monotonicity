import Results.Genus.RawGraph.ActualLayout
import Results.Genus.RawGraph.StrongRuns
import Results.Genus.CapFourMass.EndpointBounds

/-! Exact finite-state source factorization for the original cap-four graph. -/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFourMass.ActualComponent
open RawGraph RawGraph.SourceModel RawGraph.Topology RawGraph.LayoutCompiler

abbrev Component (m r p : ℕ) := (freeGraph m r p).ConnectedComponent
noncomputable instance (m r p : ℕ) : Fintype (Component m r p) := Fintype.ofFinite _
noncomputable instance (m r p : ℕ) : DecidableEq (Component m r p) := Classical.decEq _

def edgeCount {m r p : ℕ} (c : Component m r p) : ℕ := (freeComponentOrder m r p c).edges

def vertex {m r p : ℕ} (c : Component m r p) (j : Fin (edgeCount c+1)) : Fin (m-1) :=
  ((freeComponentOrder m r p c).label j).val.val

lemma vertex_free {m r p : ℕ} (c : Component m r p) (j : Fin (edgeCount c+1)) :
    IsFree r p (vertex c j) := ((freeComponentOrder m r p c).label j).val.property

def AllowedValues {m r p : ℕ} (c : Component m r p) (x : Fin (edgeCount c+1)→ℕ) : Prop :=
  (∀ j, Domain r p 4 (vertex c j) (x j)) ∧
  (∀ j : Fin (edgeCount c), edgeBound r p 4 (vertex c j.castSucc) (vertex c j.succ) ≤
    x j.castSucc+x j.succ) ∧
  ((freeComponentOrder m r p c).cycle=true →
    edgeBound r p 4 (vertex c (Fin.last _)) (vertex c 0) ≤ x (Fin.last _)+x 0)

instance {m r p : ℕ} (c : Component m r p) (x : Fin (edgeCount c+1)→ℕ) :
    Decidable (AllowedValues c x) := by unfold AllowedValues; infer_instance

def Allowed {m r p : ℕ} (c : Component m r p) (x : Fin (edgeCount c+1)→State) : Prop :=
  AllowedValues c (fun j => (x j).val+1)

instance {m r p : ℕ} (c : Component m r p) (x : Fin (edgeCount c+1)→State) :
    Decidable (Allowed c x) := by unfold Allowed; infer_instance

def componentPolynomial {m r p : ℕ} (c : Component m r p) : Polynomial ℕ :=
  ∑ x : Fin (edgeCount c+1)→State,
    if Allowed c x then Polynomial.X^(∑ j, ((x j).val+1)) else 0

def componentMass {m r p : ℕ} (c : Component m r p) : ℝ :=
  ∑ x : Fin (edgeCount c+1)→State,
    if Allowed c x then radius^(∑ j, ((x j).val+1)) else 0

lemma componentMass_nonneg {m r p : ℕ} (c : Component m r p) : 0≤componentMass c := by
  apply Finset.sum_nonneg
  intro x _
  split_ifs
  · exact pow_nonneg radius_pos.le _
  · rfl

lemma componentMass_eq_eval {m r p : ℕ} (c : Component m r p) :
    componentMass c = (componentPolynomial c).eval₂ (Nat.castRingHom ℝ) radius := by
  unfold componentMass componentPolynomial
  rw [Polynomial.eval₂_finsetSum]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp

def positiveColor (v : State) : Fin 5 := ⟨v.val+1,by have := v.isLt; omega⟩

def positiveAssignments (V : Type*) : (V→State) ≃ {x : V→Fin 5 // ∀ j, 0<(x j).val} where
  toFun x := ⟨fun j => positiveColor (x j), fun j => Nat.succ_pos _⟩
  invFun x j := ⟨(x.val j).val-1,by have := x.property j; have := (x.val j).isLt; omega⟩
  left_inv x := by funext j; apply Fin.ext; simp [positiveColor]
  right_inv x := by
    apply Subtype.ext
    funext j
    apply Fin.ext
    have := x.property j
    dsimp [positiveColor]
    omega

lemma sum_positive {V R : Type*} [Fintype V] [DecidableEq V] [AddCommMonoid R]
    (f : (V→Fin 5)→R) (hf : ∀ x, ¬(∀ j,0<(x j).val) → f x=0) :
    (∑ x,f x) = ∑ x : V→State,f (fun j => positiveColor (x j)) := by
  classical
  let P (x : V→Fin 5) := ∀ j,0<(x j).val
  calc
    (∑ x,f x) = ∑ x,if P x then f x else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases h : P x
      · simp [h]
      · simp [h,hf x h]
    _ = ∑ x : {x : V→Fin 5 // P x}, f x.val := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype (Finset.univ.filter P) (by simp) f
    _ = ∑ x : V→State,f (fun j => positiveColor (x j)) :=
      ((positiveAssignments V).sum_comp (fun x => f x.val)).symm

lemma fullComponentPolynomial_eq_bounded {m r p : ℕ} (hp : Parameters m r p 4)
    (c : Component m r p) :
    fullComponentPolynomial hp (Sum.inr c) =
      ∑ x : Fin (edgeCount c+1)→Fin 5,
        if AllowedValues c (fun j => (x j).val) then Polynomial.X^(∑ j,(x j).val) else 0 := by
  unfold fullComponentPolynomial
  change (∑ x : Fin (edgeCount c+1)→Fin 5,
    (∏ j,vertexWeight r p 4 (vertex c j) (x j))*
      (∏ j : Fin (edgeCount c),edgeWeight r p 4 (vertex c j.castSucc) (vertex c j.succ)
        (x j.castSucc) (x j.succ))*
      (if (freeComponentOrder m r p c).cycle=true then
        edgeWeight r p 4 (vertex c (Fin.last _)) (vertex c 0) (x (Fin.last _)) (x 0) else 1))=_
  apply Finset.sum_congr rfl
  intro x _
  unfold vertexWeight edgeWeight
  rw [Factorization.prod_gate,Factorization.prod_gate,Finset.prod_pow_eq_pow_sum]
  simp only [Finset.prod_const_one]
  unfold AllowedValues
  split_ifs <;> simp_all

/-- The zero state is removed only because the genuine unary source forces
all free coordinates to be positive; the remaining values are exactly1..4. -/
theorem fullComponentPolynomial_eq {m r p : ℕ} (hp : Parameters m r p 4)
    (c : Component m r p) : fullComponentPolynomial hp (Sum.inr c)=componentPolynomial c := by
  rw [fullComponentPolynomial_eq_bounded hp c]
  have hzero (x : Fin (edgeCount c+1)→Fin 5) (hx : ¬(∀ j,0<(x j).val)) :
      (if AllowedValues c (fun j => (x j).val) then (Polynomial.X : Polynomial ℕ)^(∑ j,(x j).val) else 0)=0 := by
    have hn : ¬ AllowedValues c (fun j => (x j).val) := by
      intro h
      apply hx
      intro j
      have hj := h.1 j
      rw [domain_iff_unary] at hj
      exact (hj.2 (vertex_free c j)).1
    simp [hn]
  rw [sum_positive _ hzero]
  rfl

/-- Exact global cap-four source factorization, with both fixed pivot weights
and exactly one weight for each actual nonpivot physical coordinate. -/
theorem rawPolynomial_eq_component_product {m r p : ℕ} (hp : Parameters m r p 4) :
    rawPolynomial m r p 4 = Polynomial.X^8 * ∏ c : Component m r p,componentPolynomial c := by
  rw [rawPolynomial_eq_pivots_free hp]
  simp_rw [fullComponentPolynomial_eq hp]

theorem raw_eval_eq_component_product {m r p : ℕ} (hp : Parameters m r p 4) :
    (rawPolynomial m r p 4).eval₂ (Nat.castRingHom ℝ) radius =
      radius^8 * ∏ c : Component m r p,componentMass c := by
  rw [rawPolynomial_eq_component_product hp]
  change (Polynomial.eval₂RingHom (Nat.castRingHom ℝ) radius) _=_
  rw [map_mul,map_prod]
  simp only [Polynomial.coe_eval₂RingHom,Polynomial.eval₂_pow,Polynomial.eval₂_X]
  simp_rw [componentMass_eq_eval]

end SubmittedGenus.CapFourMass.ActualComponent
