import Results.Genus.CapFiveMass.SourceSummation

/-! Genuine B coefficients inject into the finite actual raw cap-five aggregate. -/
noncomputable section
open scoped BigOperators
namespace SubmittedGenus.FiniteComparison.FiveAggregate
open CapFiveMass RawGraph
attribute [local instance] Classical.propDecidable

abbrev FixedAt (m r p g : ℕ) :=
  {x : Fin (m-1)→Fin 6 // RawAdmissible r p 5 (boundedWord x) ∧ genus (boundedWord x)=g}
abbrev AggregateAt (g : ℕ) :=
  (m : Fin (g+2)) × (r : Fin (g+2)) × (p : Fin (g+2)) × FixedAt m.val r.val p.val g

lemma fixed_card (m r p g : ℕ) : Fintype.card (FixedAt m r p g)=
    (rawPolynomial m r p 5).coeff g := by
  rw [rawPolynomial_coeff]
  exact Fintype.card_subtype _

lemma aggregate_card (g : ℕ) : Fintype.card (AggregateAt g)=
    ∑ m : Fin (g+2),∑ r : Fin (g+2),∑ p : Fin (g+2),
      (rawPolynomial m.val r.val p.val 5).coeff g := by
  simp only [AggregateAt,Fintype.card_sigma,fixed_card]

def genuine (g : ℕ) (d : GenuineFiveAt g) : GenuineFive := ⟨d.val.val,d.property⟩
def pivots (g : ℕ) (d : GenuineFiveAt g) := genuineParameters (genuine g d)

lemma m_bound (g : ℕ) (d : GenuineFiveAt g) : (pivots g d).m < g+2 := by
  have h:=d.val.val.2.property.multiplicity_le_weight_succ
  have hg:=d.val.property
  change KunzWord.weight d.val.val.2.val=g at hg
  change d.val.val.1.val < g+2
  omega
lemma r_bound (g : ℕ) (d : GenuineFiveAt g) : (pivots g d).r < g+2 := by
  have h:=(pivots g d).valid
  have hm:=m_bound g d
  unfold Parameters at h
  omega
lemma p_bound (g : ℕ) (d : GenuineFiveAt g) : (pivots g d).p < g+2 := by
  have h:=(pivots g d).valid
  have hm:=m_bound g d
  unfold Parameters at h
  omega

def encode (g : ℕ) (d : GenuineFiveAt g) : AggregateAt g :=
  ⟨⟨(pivots g d).m,m_bound g d⟩,⟨(pivots g d).r,r_bound g d⟩,
   ⟨(pivots g d).p,p_bound g d⟩,
   ⟨fun i => ⟨d.val.val.2.val i,Nat.lt_succ_of_le (d.property.1 i)⟩,
    genuineParameters_raw (genuine g d),d.val.property⟩⟩

lemma encode_injective (g : ℕ) : Function.Injective (encode g) := by
  intro d e he
  have hh := congrArg (fun s : AggregateAt g =>
    (⟨s.1.val,boundedWord s.2.2.2.val⟩ : Σ m : ℕ,RawGraph.Word m)) he
  have hm : d.val.val.1.val=e.val.val.1.val := congrArg (fun s : AggregateAt g => s.1.val) he
  rcases d with ⟨⟨⟨⟨m,hmpos⟩,⟨x,hx⟩⟩,hg⟩,hd⟩
  rcases e with ⟨⟨⟨⟨n,hnpos⟩,⟨y,hy⟩⟩,hg'⟩,hd'⟩
  dsimp at hm
  subst n
  change (⟨m,x⟩ : Σ m : ℕ,RawGraph.Word m)=⟨m,y⟩ at hh
  have hw : x=y := eq_of_heq (Sigma.mk.inj_iff.mp hh).2
  subst y
  rfl

/-- The exact raw source aggregate, not the eventual imported JSON table. -/
theorem genuineFive_le_aggregate (g : ℕ) : CapFiveMass.count g ≤
    ∑ m : Fin (g+2),∑ r : Fin (g+2),∑ p : Fin (g+2),
      (rawPolynomial m.val r.val p.val 5).coeff g := by
  have h:=Fintype.card_le_of_injective (encode g) (encode_injective g)
  simpa only [aggregate_card,CapFiveMass.count] using h

#print axioms genuineFive_le_aggregate
end SubmittedGenus.FiniteComparison.FiveAggregate
