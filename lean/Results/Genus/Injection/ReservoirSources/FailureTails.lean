import Results.Genus.FiniteArithmetic.Reservoir.BinaryLength
import Results.Genus.FiniteArithmetic.Reservoir.FailureGeometry
import Results.Genus.Injection.ReservoirSources.Candidates

noncomputable section
namespace SubmittedGenus.FiniteArithmetic.Reservoir
open PowerSeries Reflection
open scoped BigOperators
attribute [local instance] Classical.propDecidable

abbrev ShortFailureSource (d g : ℕ) := Σ ell : Fin d, BinaryLengthSource ell.val g
abbrev LongFailureSource (d : ℕ) := Graded.Product (Blocks failureSystem) (BinaryLengthSource d)
abbrev FailureTailSource (d g : ℕ) := ShortFailureSource d g ⊕ LongFailureSource d g

/-- All actual binary tails of weight g failing the physical distance-d mark. -/
abbrev FailedTail (d g : ℕ) :=
  {t : List ℕ // OriginalReservoir.BinaryTail t ∧ t.sum = g ∧ ¬ OriginalReservoir.TailWitness t d}

lemma failure_block_binary {w : List ℕ}
    (h : Language failureSystem.pairAllowed failureSystem.centerAllowed w) :
    OriginalReservoir.BinaryTail w := by
  intro a ha
  have := bounded_language_letters h a ha
  omega

lemma no_tailWitness_append {p t : List ℕ} {d : ℕ}
    (hp : Language failureSystem.pairAllowed failureSystem.centerAllowed p)
    (ht : OriginalReservoir.BinaryTail t) (hlen : t.length = d) :
    ¬ OriginalReservoir.TailWitness (p++t) d := by
  have hb : ∀ a ∈ p++t, a=1 ∨ a=2 := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact failure_block_binary hp a ha
    · exact ht a ha
  apply (no_tailWitness_iff_prefix_language _ d hb (by simp [hlen])).mpr
  simpa only [List.length_append, hlen, Nat.add_sub_cancel,
    List.take_left] using hp

def failureTailWord {d g : ℕ} : FailureTailSource d g → List ℕ
  | .inl s => binaryLengthWord s.2
  | .inr s => s.2.1.val ++ binaryLengthWord s.2.2

lemma failureTailWord_binary {d g : ℕ} (s : FailureTailSource d g) :
    OriginalReservoir.BinaryTail (failureTailWord s) := by
  cases s with
  | inl s => exact binaryLengthWord_binary s.2
  | inr s =>
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact failure_block_binary s.2.1.property.1 a ha
    · exact binaryLengthWord_binary s.2.2 a ha

lemma failureTailWord_weight {d g : ℕ} (s : FailureTailSource d g) :
    (failureTailWord s).sum = g := by
  cases s with
  | inl s => exact binaryLengthWord_weight s.2
  | inr s =>
    change (s.2.1.val ++ binaryLengthWord s.2.2).sum = g
    rw [List.sum_append, s.2.1.property.2, binaryLengthWord_weight]
    have := s.1.isLt
    omega

lemma failureTailWord_failed {d g : ℕ} (s : FailureTailSource d g) :
    ¬ OriginalReservoir.TailWitness (failureTailWord s) d := by
  cases s with
  | inl s =>
    apply no_tailWitness_of_short
    simpa only [failureTailWord, binaryLengthWord_length] using s.1.isLt
  | inr s =>
    exact no_tailWitness_append s.2.1.property.1 (binaryLengthWord_binary _) (binaryLengthWord_length _)

lemma failureTailWord_injective (d g : ℕ) :
    Function.Injective (@failureTailWord d g) := by
  intro a b h
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      have hlen := congrArg List.length h
      change (binaryLengthWord a.2).length = (binaryLengthWord b.2).length at hlen
      simp only [binaryLengthWord_length] at hlen
      have hab : a.1 = b.1 := Fin.ext hlen
      rcases a with ⟨i,a⟩
      rcases b with ⟨j,b⟩
      dsimp at hab
      subst j
      exact congrArg Sum.inl (congrArg (Sigma.mk i) (binaryLengthWord_injective _ _ h))
    | inr b =>
      have hh := congrArg List.length h
      change (binaryLengthWord a.2).length = (b.2.1.val++binaryLengthWord b.2.2).length at hh
      simp only [List.length_append, binaryLengthWord_length] at hh
      have := a.1.isLt
      omega
  | inr a =>
    cases b with
    | inl b =>
      have hh := congrArg List.length h
      change (a.2.1.val++binaryLengthWord a.2.2).length = (binaryLengthWord b.2).length at hh
      simp only [List.length_append, binaryLengthWord_length] at hh
      have := b.1.isLt
      omega
    | inr b =>
      have hlen := congrArg List.length h
      change (a.2.1.val++binaryLengthWord a.2.2).length =
        (b.2.1.val++binaryLengthWord b.2.2).length at hlen
      simp only [List.length_append, binaryLengthWord_length] at hlen
      have he := List.append_inj h (by omega)
      have hsum := congrArg List.sum he.1
      rw [a.2.1.property.2, b.2.1.property.2] at hsum
      have hij : a.1 = b.1 := Fin.ext hsum
      rcases a with ⟨i,a,t⟩
      rcases b with ⟨j,b,u⟩
      dsimp at hij
      subst j
      have hab : a = b := Subtype.ext he.1
      have htu : t = u := binaryLengthWord_injective _ _ he.2
      subst b; subst u; rfl

lemma exists_binaryLengthSource_at (w : List ℕ) (hw : OriginalReservoir.BinaryTail w)
    {d g : ℕ} (hlen : w.length = d) (hsum : w.sum = g) :
    ∃ a : BinaryLengthSource d g, binaryLengthWord a = w := by
  subst d
  subst g
  exact exists_binaryLengthSource w hw

lemma exists_failureTailSource {d g : ℕ} (t : FailedTail d g) :
    ∃ s : FailureTailSource d g, failureTailWord s = t.val := by
  by_cases hshort : t.val.length < d
  · obtain ⟨s,hs⟩ := exists_binaryLengthSource_at t.val t.property.1 rfl t.property.2.1
    exact ⟨.inl ⟨⟨t.val.length,hshort⟩,s⟩,hs⟩
  · have hlong : d ≤ t.val.length := by omega
    let p := t.val.take (t.val.length-d)
    let u := t.val.drop (t.val.length-d)
    have hpu : p++u=t.val := List.take_append_drop _ _
    have hsum : p.sum + u.sum = g := by rw [← List.sum_append,hpu]; exact t.property.2.1
    have hulen : u.length=d := by dsimp [u]; rw [List.length_drop]; omega
    have hub : OriginalReservoir.BinaryTail u := by
      intro a ha
      exact t.property.1 a (List.mem_of_mem_drop ha)
    obtain ⟨b,hb⟩ := exists_binaryLengthSource_at u hub hulen (show u.sum = g-p.sum by omega)
    have hp : Language failureSystem.pairAllowed failureSystem.centerAllowed p :=
      (no_tailWitness_iff_prefix_language _ d t.property.1 hlong).mp t.property.2.2
    refine ⟨.inr ⟨⟨p.sum,by omega⟩,⟨p,hp,rfl⟩,b⟩,?_⟩
    change p++binaryLengthWord b=t.val
    rw [hb,hpu]

def failureTailToActual (d g : ℕ) (s : FailureTailSource d g) : FailedTail d g :=
  ⟨failureTailWord s, failureTailWord_binary s, failureTailWord_weight s, failureTailWord_failed s⟩

noncomputable def failureTailEquiv (d g : ℕ) : FailureTailSource d g ≃ FailedTail d g :=
  Equiv.ofBijective (failureTailToActual d g) ⟨by
    intro a b h
    exact failureTailWord_injective d g (congrArg Subtype.val h), by
    intro t
    obtain ⟨s,hs⟩ := exists_failureTailSource t
    exact ⟨s,Subtype.ext hs⟩⟩

instance failedTailFintype (d g : ℕ) : Fintype (FailedTail d g) :=
  Fintype.ofEquiv (FailureTailSource d g) (failureTailEquiv d g)

/-- The original A_w, as an actual no-11 reflection-block series. -/
noncomputable def failureBlockSeries : PowerSeries ℤ := blockSeries failureSystem

/-- The original Q_d, including short tails and the empty constrained block. -/
noncomputable def failureTailSeries (d : ℕ) : PowerSeries ℤ := Graded.series (FailureTailSource d)

lemma failureTailSeries_coeff (d g : ℕ) :
    coeff g (failureTailSeries d) = (Fintype.card (FailedTail d g) : ℤ) := by
  rw [failureTailSeries,Graded.coeff_series]
  exact congrArg (fun n : ℕ => (n:ℤ)) (Fintype.card_congr (failureTailEquiv d g))

lemma failureTailSeries_identity (d : ℕ) :
    failureTailSeries d = (∑ ell : Fin d, c^ell.val) + c^d * failureBlockSeries := by
  unfold failureTailSeries FailureTailSource
  rw [Graded.sum_series, Graded.product_series]
  have hshort : Graded.series (ShortFailureSource d) = ∑ ell : Fin d, c^ell.val := by
    apply PowerSeries.ext
    intro n
    simp only [Graded.coeff_series, ShortFailureSource, Fintype.card_sigma, Nat.cast_sum,
      map_sum]
    apply Finset.sum_congr rfl
    intro ell _
    rw [← binaryLengthSeries_identity]
    exact (Graded.coeff_series (BinaryLengthSource ell.val) n).symm
  rw [hshort]
  change _ + failureBlockSeries * binaryLengthSeries d = _
  rw [binaryLengthSeries_identity,mul_comm]

lemma failureBlockSeries_identity :
    (1-2*X^3-X^4)*failureBlockSeries = 1+X^2 := by
  have h := bounded_block_identity 3 2
  have hp : pairPolynomial 3 2 = (2 : PowerSeries ℤ)*X^3+X^4 := by
    simp only [pairPolynomial,Fintype.sum_prod_type,Fin.sum_univ_succ]
    norm_num
    ring
  have hc : centerPolynomial 3 2 = (X : PowerSeries ℤ)^2 := by
    simp only [centerPolynomial,Fin.sum_univ_succ]
    norm_num
  rw [hp,hc] at h
  unfold failureBlockSeries
  convert h using 1 <;> ring

#print axioms failureTailEquiv
#print axioms failureTailSeries_coeff
#print axioms failureTailSeries_identity
#print axioms failureBlockSeries_identity
end SubmittedGenus.FiniteArithmetic.Reservoir
