import Results.Genus.CapFourMass.ActualConditionalDensity
import Results.Genus.CapFourMass.FeedbackOrder
import Results.Genus.CapFourMass.ConditionalProduct
import Results.Genus.CapFourMass.LocalPartitions

namespace SubmittedGenus.CapFourMass.ActualContraction
open scoped BigOperators
open RawGraph ContractionGeometry ConditionalDensity ConditionalProduct
noncomputable section
attribute [local instance] Classical.propDecidable

def center (l : List ℕ) (n : ℕ) : ℕ := if h : n < l.length then l.get ⟨n,h⟩ else 0
lemma center_eq (l : List ℕ) {n : ℕ} (hn : n<l.length) :
    center l n = l.get ⟨n,hn⟩ := by simp [center,hn]

lemma indexed_bound {m r p : ℕ} (hr : 1 ≤ r) (hrp : r<p)
    {z : ℝ} (hz : 0<z) (l : List ℕ) (hl : l.Nodup)
    (hel : ∀i,i∈l ↔ Eligible m p i) (P : Finset ℕ)
    (hP : P ⊆ Finset.range l.length) (hK : P.card ≤ 1+(p-r)/3)
    (horder : ∀ i j : Fin l.length, i<j → j.val∉P →
      ¬Arrow m r p (l.get j) (l.get i)) :
    (∑ x : Fin (m-1) → Fin 5,
      if RawGraph.SourceModel.Admissible r p 4 (boundedWord x) ∧
        (∀n<l.length,¬Failure (KunzWord.coord (boundedWord x)) (center l n))
      then ∏v,z^(x v).val else 0) ≤
    (1-LocalWeights.epsilon z)^l.length *
      ((1-LocalWeights.delta z)/(1-LocalWeights.epsilon z))^(1+(p-r)/3) *
      (∑ x : Fin (m-1) → Fin 5,
        if RawGraph.SourceModel.Admissible r p 4 (boundedWord x)
        then ∏v,z^(x v).val else 0) := by
  let w := fun x : Fin (m-1) → Fin 5 => ∏v,z^(x v).val
  let A := Finset.univ.filter (fun x : Fin (m-1) → Fin 5 =>
    RawGraph.SourceModel.Admissible r p 4 (boundedWord x))
  let F := fun n (x : Fin (m-1) → Fin 5) =>
    Failure (KunzWord.coord (boundedWord x)) (center l n)
  have hfailure : ∀n<l.length,
      (if n∈P then LocalWeights.delta z else LocalWeights.epsilon z)*
        mass w (survivors A F n) ≤ mass w ((survivors A F n).filter (F n)) := by
    intro n hn
    let J := (Finset.range n).image (center l)
    have hi : Eligible m p (center l n) := by
      rw [center_eq l hn]
      exact (hel _).mp (List.get_mem ..)
    have hj : ∀j∈J,Eligible m p j := by
      intro j hj
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj
      have hk' : k<l.length := lt_trans (Finset.mem_range.mp hk) hn
      rw [center_eq l hk']
      exact (hel _).mp (List.get_mem ..)
    have hne : ∀j∈J,center l n ≠ j := by
      intro j hj he
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj
      have hk' : k<l.length := lt_trans (Finset.mem_range.mp hk) hn
      rw [center_eq l hn,center_eq l hk'] at he
      have he' : n=k := hl.getElem_inj_iff.mp he
      have := Finset.mem_range.mp hk
      omega
    have hg (x : Fin (m-1) → Fin 5) :
        Good m r p J x ↔ RawGraph.SourceModel.Admissible r p 4 (boundedWord x) ∧
          ∀k<n,¬F k x := by simp [Good,J,F]
    have hm : mass w (survivors A F n) =
        ∑x,if Good m r p J x then w x else 0 := by
      simp only [mass,survivors,A,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x hx
      rw [hg]
      split_ifs <;> simp_all
    have hf : mass w ((survivors A F n).filter (F n)) =
        ∑x,if Good m r p J x ∧ F n x then w x else 0 := by
      simp only [mass,survivors,A,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x hx
      rw [hg]
      split_ifs <;> simp_all
    rw [hm,hf]
    by_cases hp : n∈P
    · simp only [if_pos hp]
      exact ActualConditionalDensity.postponed hr hrp hi hz J hj hne
    · simp only [if_neg hp]
      apply ActualConditionalDensity.nonpostponed hr hrp hi hz J hj hne
      intro j hj
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj
      have hk' : k<l.length := lt_trans (Finset.mem_range.mp hk) hn
      rw [center_eq l hn,center_eq l hk']
      exact horder ⟨k,hk'⟩ ⟨n,hn⟩ (Finset.mem_range.mp hk) hp
  have hh := feedback_product w (fun x => by dsimp [w]; positivity) A F P
    l.length (1+(p-r)/3) hP hK (LocalWeights.epsilon z) (LocalWeights.delta z)
    (le_of_lt (LocalWeights.delta_pos hz)) (LocalWeights.delta_le_epsilon hz)
    (LocalWeights.epsilon_lt_one hz) hfailure
  simpa [mass,survivors,A,F,w,Finset.sum_filter,ite_and] using hh

/-- The submitted self-pair contraction on the actual finite raw source.
All conditional gadget bounds and the bounded feedback order are discharged. -/
theorem actual_contraction {m r p : ℕ} (hr : 1 ≤ r) (hrp : r<p)
    {z : ℝ} (hz : 0<z) :
    (∑ x : Fin (m-1) → Fin 5,
      if RawGraph.SourceModel.Admissible r p 4 (boundedWord x) ∧
        (∀i,Eligible m p i → ¬Failure (KunzWord.coord (boundedWord x)) i)
      then ∏v,z^(x v).val else 0) ≤
    (1-LocalWeights.epsilon z)^((m-1)/2-p) *
      ((1-LocalWeights.delta z)/(1-LocalWeights.epsilon z))^(1+(p-r)/3) *
      (∑ x : Fin (m-1) → Fin 5,
        if RawGraph.SourceModel.Admissible r p 4 (boundedWord x)
        then ∏v,z^(x v).val else 0) := by
  obtain ⟨l,P,hl,hlen,hel,hP,hK,_,ho⟩ :=
    FeedbackOrder.eligible_feedback_indexed m r p hrp
  have hequiv (x : Fin (m-1) → Fin 5) :
      (∀n<l.length,¬Failure (KunzWord.coord (boundedWord x)) (center l n)) ↔
      (∀i,Eligible m p i → ¬Failure (KunzWord.coord (boundedWord x)) i) := by
    constructor
    · intro h i hi
      have hm := (hel i).mpr hi
      obtain ⟨k,hk⟩ := List.mem_iff_get.mp hm
      have hh := h k.val k.isLt
      rw [center_eq l k.isLt] at hh
      change ¬Failure (KunzWord.coord (boundedWord x)) (l.get k) at hh
      rwa [hk] at hh
    · intro h n hn
      rw [center_eq l hn]
      exact h _ ((hel _).mp (List.get_mem ..))
  have hh := indexed_bound hr hrp hz l hl hel P hP hK ho
  simp_rw [hequiv] at hh
  simpa only [hlen] using hh

/-- Original contraction, expressed against the actual raw polynomial. -/
theorem actual_contraction_polynomial {m r p : ℕ} (hr : 1 ≤ r) (hrp : r<p)
    {z : ℝ} (hz : 0<z) :
    (∑ x : Fin (m-1) → Fin 5,
      if RawGraph.SourceModel.Admissible r p 4 (boundedWord x) ∧
        (∀i,Eligible m p i → ¬Failure (KunzWord.coord (boundedWord x)) i)
      then z^RawGraph.genus (boundedWord x) else 0) ≤
    (1-LocalWeights.epsilon z)^((m-1)/2-p) *
      ((1-LocalWeights.delta z)/(1-LocalWeights.epsilon z))^(1+(p-r)/3) *
      Polynomial.eval₂ (Nat.castRingHom ℝ) z (RawGraph.rawPolynomial m r p 4) := by
  simpa only [LocalPartitions.raw_partition_eval,←LocalPartitions.genus_weight] using
    actual_contraction hr hrp hz

/-- Genuine Kunz words avoid every eligible self-pair failure. -/
theorem valid_partition_bound {m r p : ℕ} (hr : 1 ≤ r) (hrp : r<p)
    {z : ℝ} (hz : 0<z) :
    (∑ x : Fin (m-1) → Fin 5,
      if RawGraph.SourceModel.Admissible r p 4 (boundedWord x) ∧ KunzWord.Valid (boundedWord x)
      then z^RawGraph.genus (boundedWord x) else 0) ≤
    (1-LocalWeights.epsilon z)^((m-1)/2-p) *
      ((1-LocalWeights.delta z)/(1-LocalWeights.epsilon z))^(1+(p-r)/3) *
      Polynomial.eval₂ (Nat.castRingHom ℝ) z (RawGraph.rawPolynomial m r p 4) := by
  apply le_trans _ (actual_contraction_polynomial hr hrp hz)
  apply Finset.sum_le_sum
  intro x hx
  split_ifs with hv ha
  · rfl
  · exfalso
    apply ha
    exact ⟨hv.1,fun i hi => valid_avoids hv.2 hi⟩
  · positivity
  · rfl

end
end SubmittedGenus.CapFourMass.ActualContraction
