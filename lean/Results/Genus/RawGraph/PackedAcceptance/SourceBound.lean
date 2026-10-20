import Results.Genus.RawGraph.Packing
import Mathlib.Combinatorics.Enumerative.Composition

/-! Original carry-free width, proved from the actual positive source words.
The aggregate map retains multiplicity and the unique two rightmost pivots;
it is not a bound obtained by counting graph parameters independently. -/
noncomputable section
namespace SubmittedGenus.RawGraph.PackedAcceptance
open scoped BigOperators
attribute [local instance] Classical.propDecidable

abbrev FixedAt (m r p a g : ℕ) :=
  {x : Fin (m-1) → Fin (a+1) // RawAdmissible r p a (boundedWord x) ∧ genus (boundedWord x)=g}

abbrev AggregateAt (M R P a g : ℕ) :=
  (m : Fin M) × (r : Fin R) × (p : Fin P) × FixedAt m.val r.val p.val a g

lemma fixed_card (m r p a g : ℕ) : Fintype.card (FixedAt m r p a g)=
    (rawPolynomial m r p a).coeff g := by
  rw [rawPolynomial_coeff]
  exact Fintype.card_subtype _

lemma aggregate_card (M R P a g : ℕ) : Fintype.card (AggregateAt M R P a g)=
    ∑ m : Fin M,∑ r : Fin R,∑ p : Fin P,
      (rawPolynomial m.val r.val p.val a).coeff g := by
  simp only [AggregateAt,Fintype.card_sigma,fixed_card]

def aggregateComposition {M R P a g : ℕ} (s : AggregateAt M R P a g) : Composition g where
  blocks := List.ofFn (boundedWord s.2.2.2.val)
  blocks_pos := by
    intro v hv
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hv
    have ha : 1≤a := by rcases s.2.2.2.property.1.1.2.2.2 with h | h <;> omega
    exact alphabet_positive ha s.2.2.2.property.1.2.1 i
  blocks_sum := List.sum_ofFn.trans s.2.2.2.property.2

lemma aggregateComposition_injective {M R P a g : ℕ} :
    Function.Injective (@aggregateComposition M R P a g) := by
  rintro ⟨m,r,p,x⟩ ⟨n,s,q,y⟩ he
  have hl := congrArg Composition.blocks he
  change List.ofFn (boundedWord x.val)=List.ofFn (boundedWord y.val) at hl
  have hlen := congrArg List.length hl
  simp only [List.length_ofFn] at hlen
  have hm := x.property.1.1.2.2.1
  have hn := y.property.1.1.2.2.1
  have hmn : m=n := Fin.ext (by omega)
  subst n
  have hxy : boundedWord x.val=boundedWord y.val := List.ofFn_inj.mp hl
  have hy : RawAdmissible s.val q.val a (boundedWord x.val) := hxy.symm ▸ y.property.1
  obtain ⟨hrs,hpq⟩ := raw_parameters_unique x.property.1 hy
  have hrs' : r=s := Fin.ext hrs
  have hpq' : p=q := Fin.ext hpq
  subst s
  subst q
  have hxye : x=y := by
    apply Subtype.ext
    funext i
    exact Fin.ext (congrFun hxy i)
  subst y
  rfl

/-- The same original-width bound for one fixed raw source. -/
theorem fixed_coeff_le_compositions (m r p a g : ℕ) :
    (rawPolynomial m r p a).coeff g ≤ 2^(g-1) := by
  rw [←fixed_card,←composition_card]
  let f : FixedAt m r p a g → Composition g := fun x =>
    aggregateComposition (M:=m+1) (R:=r+1) (P:=p+1)
      ⟨⟨m,by omega⟩,⟨r,by omega⟩,⟨p,by omega⟩,x⟩
  apply Fintype.card_le_of_injective f
  intro x y he
  apply Subtype.ext
  have hl := congrArg Composition.blocks he
  exact funext fun i=>Fin.ext (congrFun (List.ofFn_inj.mp hl) i)

/-- Any finite rectangle of distinct original raw triples has at most one
source word per positive composition. This also bounds every sub-rectangle. -/
theorem aggregate_coeff_le_compositions (M R P a g : ℕ) :
    (∑ m : Fin M,∑ r : Fin R,∑ p : Fin P,
      (rawPolynomial m.val r.val p.val a).coeff g) ≤ 2^(g-1) := by
  rw [←aggregate_card,←composition_card]
  exact Fintype.card_le_of_injective _ aggregateComposition_injective

/-- The manuscript width H+2 rules out carries at every retained degree,
including after summing all distinct multiplicities and pivot pairs. -/
theorem aggregate_coeff_lt_digit_base (M R P a H g : ℕ) (hg : g≤H) :
    (∑ m : Fin M,∑ r : Fin R,∑ p : Fin P,
      (rawPolynomial m.val r.val p.val a).coeff g) < 2^(H+2) := by
  apply (aggregate_coeff_le_compositions M R P a g).trans_lt
  exact Nat.pow_lt_pow_right (by decide) (by omega)

#print axioms aggregateComposition_injective
#print axioms aggregate_coeff_le_compositions
#print axioms aggregate_coeff_lt_digit_base
end SubmittedGenus.RawGraph.PackedAcceptance
