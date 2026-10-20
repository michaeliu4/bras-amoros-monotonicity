import Results.Genus.RawGraph.Conditioning
import Results.Genus.RawGraph.ActualLayout
import Results.Genus.FixedPivot.TailLayout

/-! The original fixed-pivot raw source conditioned on physical coordinates
1,...,p, with every remaining coordinate in its exact carry tail. -/
namespace SubmittedGenus.FixedPivot
open RawGraph RawGraph.SourceModel
open scoped BigOperators
noncomputable section

lemma parameter_gap_positive {m r p a : ℕ} (hp : Parameters m r p a) : 0 < p - r := by
  have := hp.2.1; omega
lemma parameter_gap_lt {m r p a : ℕ} (hp : Parameters m r p a) : p - r < m - r := by
  have := hp.2.1; have := hp.2.2.1; omega
lemma parameter_tail_long {m r p a : ℕ} (hp : Parameters m r p a) (hm : 2 * p < m) :
    2 * (p - r) < m - r := by
  have := hp.1; have := hp.2.1; omega

abbrev TailRepresentative {m r p a : ℕ} (hp : Parameters m r p a) :=
  CarryRepresentative (m - r) (p - r) (parameter_gap_lt hp)

noncomputable instance {m r p a : ℕ} (hp : Parameters m r p a) : Fintype (TailRepresentative hp) :=
  Fintype.ofFinite _

private def coreCode {m r p a : ℕ} (hp : Parameters m r p a) (k : Fin p) : Fin (m - 1) :=
  ⟨k.val, by have := k.isLt; have := hp.2.2.1; omega⟩
private def tailCode {m r p a : ℕ} (hp : Parameters m r p a)
    (x : {x : ℕ // p - r < x ∧ x < m - r}) : Fin (m - 1) :=
  ⟨r + x.val - 1, by have := x.property; have := hp.1; have := hp.2.1; have := hp.2.2.1; omega⟩

/-- The finite core and the strict carry tail partition all physical coordinates. -/
def coreTailSplit {m r p a : ℕ} (hp : Parameters m r p a) :
    Fin p ⊕ {x : ℕ // p - r < x ∧ x < m - r} ≃ Fin (m - 1) :=
  Equiv.ofBijective (Sum.elim (coreCode hp) (tailCode hp)) (by
    constructor
    · intro u v h
      have h1 := hp.1; have h2 := hp.2.1; have h3 := hp.2.2.1
      cases u with
      | inl k =>
        cases v with
        | inl l =>
          apply congrArg Sum.inl
          apply Fin.ext
          have he := congrArg (fun i : Fin (m - 1) => i.val) h
          exact he
        | inr x =>
          have hk := k.isLt
          have hx := x.property
          have he := congrArg Fin.val h
          change k.val = r + x.val - 1 at he
          omega
      | inr x =>
        cases v with
        | inl k =>
          have hk := k.isLt
          have hx := x.property
          have he := congrArg Fin.val h
          change r + x.val - 1 = k.val at he
          omega
        | inr y =>
          have hx := x.property; have hy := y.property
          have he := congrArg Fin.val h
          change r + x.val - 1 = r + y.val - 1 at he
          exact congrArg Sum.inr (Subtype.ext (by omega))
    · intro i
      have h1 := hp.1; have h2 := hp.2.1; have h3 := hp.2.2.1
      have hi := i.isLt
      by_cases hc : i.val < p
      · exact ⟨Sum.inl ⟨i.val, hc⟩, Fin.ext rfl⟩
      · let x : {x : ℕ // p - r < x ∧ x < m - r} := ⟨i.val + 1 - r, by omega⟩
        refine ⟨Sum.inr x, ?_⟩
        apply Fin.ext
        change r + (i.val + 1 - r) - 1 = i.val
        omega)

@[simp] theorem coreTailSplit_core {m r p a : ℕ} (hp : Parameters m r p a) (k : Fin p) :
    physical (coreTailSplit hp (Sum.inl k)) = k.val + 1 := rfl

@[simp] theorem coreTailSplit_tail {m r p a : ℕ} (hp : Parameters m r p a)
    (x : {x : ℕ // p - r < x ∧ x < m - r}) :
    physical (coreTailSplit hp (Sum.inr x)) = r + x.val := by
  change r + x.val - 1 + 1 = r + x.val
  have := hp.1
  omega

def conditionedTailEdges {m r p a : ℕ} (hp : Parameters m r p a) (c : TailRepresentative hp) : ℕ :=
  carryTailSize (m - r) (p - r) (parameter_gap_lt hp) c - 1

def tailPositionEquiv {m r p a : ℕ} (hp : Parameters m r p a) (hm : 2 * p < m)
    (c : TailRepresentative hp) : Fin (conditionedTailEdges hp c + 1) ≃
      Fin (carryTailSize (m - r) (p - r) (parameter_gap_lt hp) c) :=
  finCongr (Nat.sub_add_cancel (carryTailSize_positive (m - r) (p - r)
    (parameter_gap_lt hp) (parameter_tail_long hp hm) c))

/-- Exact ordered tail coordinates, after the fixed-core ports are removed. -/
def tailCoordinatesEquiv {m r p a : ℕ} (hp : Parameters m r p a) (hm : 2 * p < m) :
    (Σ c : TailRepresentative hp, Fin (conditionedTailEdges hp c + 1)) ≃
      {x : ℕ // p - r < x ∧ x < m - r} :=
  (Equiv.sigmaCongrRight (tailPositionEquiv hp hm)).trans
    (carryTailEquiv (m - r) (p - r) (parameter_gap_positive hp) (parameter_gap_lt hp))

/-- The original fixed-pivot finite core and all exact carry tails. -/
def conditioningLayout {m r p a : ℕ} (hp : Parameters m r p a) (hm : 2 * p < m) :
    RawGraph.Conditioning.Layout m (Fin p) (TailRepresentative hp) where
  edges := conditionedTailEdges hp
  cycle _ := false
  label := (Equiv.sumCongr (Equiv.refl _) (tailCoordinatesEquiv hp hm)).trans (coreTailSplit hp)

@[simp] theorem conditioning_core_physical {m r p a : ℕ} (hp : Parameters m r p a)
    (hm : 2 * p < m) (k : Fin p) :
    physical (RawGraph.Conditioning.coreVertex (conditioningLayout hp hm) k) = k.val + 1 := rfl

@[simp] theorem conditioning_tail_physical {m r p a : ℕ} (hp : Parameters m r p a)
    (hm : 2 * p < m) (c : TailRepresentative hp) (j : Fin (conditionedTailEdges hp c + 1)) :
    physical (RawGraph.Conditioning.tailVertex (conditioningLayout hp hm) c j) =
      r + carryTailLabel (m - r) (p - r) (parameter_gap_lt hp) c j.val := by
  change physical (coreTailSplit hp (Sum.inr (tailCoordinatesEquiv hp hm ⟨c, j⟩))) = _
  rw [coreTailSplit_tail]
  rfl

lemma conditionedTailIndex_lt {m r p a : ℕ} (hp : Parameters m r p a) (hm : 2 * p < m)
    (c : TailRepresentative hp) (j : Fin (conditionedTailEdges hp c + 1)) :
    j.val < carryTailSize (m - r) (p - r) (parameter_gap_lt hp) c :=
  (tailPositionEquiv hp hm c j).isLt


lemma conditioning_tail_incidence {m r p a : ℕ} (hp : Parameters m r p a) (hm : 2 * p < m)
    (c e : TailRepresentative hp)
    (j : Fin (conditionedTailEdges hp c + 1)) (k : Fin (conditionedTailEdges hp e + 1))
    (he : 0 < edgeBound r p a
      (RawGraph.Conditioning.tailVertex (conditioningLayout hp hm) c j)
      (RawGraph.Conditioning.tailVertex (conditioningLayout hp hm) e k)) :
    CarryIncidence (m - r) (p - r)
      (carryTailLabel (m - r) (p - r) (parameter_gap_lt hp) c j.val)
      (carryTailLabel (m - r) (p - r) (parameter_gap_lt hp) e k.val) := by
  have ha := RawGraph.Topology.edgeBound_pos_rawGraph he
  have hj := carryTailLabel_vertex (m - r) (p - r) (parameter_gap_lt hp) c
    (conditionedTailIndex_lt hp hm c j)
  have hk := carryTailLabel_vertex (m - r) (p - r) (parameter_gap_lt hp) e
    (conditionedTailIndex_lt hp hm e k)
  have ht := ha.2.2.2
  unfold TargetPair at ht
  rw [conditioning_tail_physical, conditioning_tail_physical] at ht
  apply (physical_carry_iff hp.2.1.le (by have := hp.2.2.1; have := hp.2.1; omega)).mp
  have h1 := hp.1; have h2 := hp.2.1
  omega

/-- Every original tail-tail binary constraint is exactly a consecutive carry
path edge. No externally supplied layout certificate is assumed. -/
theorem conditioningLayout_covers {m r p a : ℕ} (hp : Parameters m r p a) (hm : 2 * p < m) :
    RawGraph.Conditioning.Covers (conditioningLayout hp hm) r p a := by
  classical
  rintro ⟨c, j⟩ ⟨e, k⟩ hpos
  have hinc := conditioning_tail_incidence hp hm c e j k hpos
  have hj := conditionedTailIndex_lt hp hm c j
  have hk := conditionedTailIndex_lt hp hm e k
  have hce : c = e := carry_incidence_same_component (m - r) (p - r)
    (parameter_gap_positive hp) (parameter_gap_lt hp) c e
    ⟨j.val + 1, carryTail_position (m - r) (p - r) (parameter_gap_lt hp) c hj⟩
    ⟨k.val + 1, carryTail_position (m - r) (p - r) (parameter_gap_lt hp) e hk⟩ hinc
  subst e
  have hdistinct : j.val ≠ k.val := by
    intro he
    have he' : j = k := Fin.ext he
    subst k
    simpa [edgeBound] using hpos
  have hshape := (carryTail_incidence_iff (m - r) (p - r) (parameter_gap_lt hp) c hj hk).mp hinc
  refine ⟨c, Or.inl ?_⟩
  rcases hshape with hjk | hkj | hloop
  · let t : Fin (conditionedTailEdges hp c) := ⟨j.val, by have := k.isLt; omega⟩
    have htj : t.castSucc = j := Fin.ext rfl
    have htk : t.succ = k := Fin.ext hjk
    exact ⟨t, Or.inl ⟨congrArg (Sigma.mk c) htj.symm, congrArg (Sigma.mk c) htk.symm⟩⟩
  · let t : Fin (conditionedTailEdges hp c) := ⟨k.val, by have := j.isLt; omega⟩
    have htk : t.castSucc = k := Fin.ext rfl
    have htj : t.succ = j := Fin.ext hkj
    exact ⟨t, Or.inr ⟨congrArg (Sigma.mk c) htk.symm, congrArg (Sigma.mk c) htj.symm⟩⟩
  · exact (hdistinct (hloop.2.1.trans hloop.2.2.symm)).elim

/-- Exact all-parameter finite-core source contraction in the manuscript's
long-multiplicity region m>2p. The core is the actual interval 1,...,p. -/
theorem rawPolynomial_eq_core_carry_transfers {m r p a : ℕ}
    (hp : Parameters m r p a) (hm : 2 * p < m) :
    rawPolynomial m r p a = ∑ x : Fin p → Fin (a + 1),
      RawGraph.Conditioning.coreTerm (conditioningLayout hp hm) r p a x *
        ∏ c : TailRepresentative hp,
          RawGraph.Conditioning.componentRun (conditioningLayout hp hm) r p a x c := by
  classical
  exact RawGraph.Conditioning.rawPolynomial_eq_conditioned_transfer
    (conditioningLayout hp hm) hp (conditioningLayout_covers hp hm)

end
end SubmittedGenus.FixedPivot
