import Results.Genus.RawGraph.PackedAcceptance.Coverage

noncomputable section
namespace SubmittedGenus.RawGraph.PackedAcceptance
open scoped BigOperators
open LayoutCompiler Packing
attribute [local instance] Classical.propDecidable

abbrev RangeSource (M P a g : ℕ) := Σt:Triple M P,FixedAt t.m t.r t.p a g

/-- The polynomial for precisely the submitted finite triple range. -/
def rangePolynomial (M P a : ℕ) : Polynomial ℕ :=
  ∑t:Triple M P,rawPolynomial t.m t.r t.p a

lemma rangePolynomial_coeff (M P a g : ℕ) :
    (rangePolynomial M P a).coeff g=Fintype.card (RangeSource M P a g) := by
  simp only [rangePolynomial,Polynomial.finsetSum_coeff,RangeSource,Fintype.card_sigma,fixed_card]

def rangeComposition {M P a g : ℕ} (s : RangeSource M P a g) : Composition g where
  blocks := List.ofFn (boundedWord s.2.val)
  blocks_pos := by
    intro v hv
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hv
    have ha : 1≤a := by rcases s.2.property.1.1.2.2.2 with h | h <;> omega
    exact alphabet_positive ha s.2.property.1.2.1 i
  blocks_sum := List.sum_ofFn.trans s.2.property.2

lemma rangeComposition_injective {M P a g : ℕ} : Function.Injective (@rangeComposition M P a g) := by
  rintro ⟨⟨m,p,r⟩,x⟩ ⟨⟨n,q,s⟩,y⟩ he
  have hl := congrArg Composition.blocks he
  change List.ofFn (boundedWord x.val)=List.ofFn (boundedWord y.val) at hl
  have hlen := congrArg List.length hl
  simp only [List.length_ofFn,Triple.m] at hlen
  have hmn : m=n := Fin.ext (by omega)
  subst n
  have hxy : boundedWord x.val=boundedWord y.val := List.ofFn_inj.mp hl
  have hy := hxy.symm ▸ y.property.1
  obtain ⟨hrs,hpq⟩ := raw_parameters_unique x.property.1 hy
  have hpq' : p=q := Fin.ext (by simpa [Triple.p] using hpq)
  subst q
  have hrs' : r=s := Fin.ext (by simpa [Triple.r] using hrs)
  subst s
  have hxye : x=y := by
    apply Subtype.ext
    exact funext fun i=>Fin.ext (congrFun hxy i)
  subst y
  rfl

theorem range_coeff_lt_digitBase (M P a H : ℕ) (g : Fin (H+1)) :
    (rangePolynomial M P a).coeff g.val<digitBase H := by
  have h := Fintype.card_le_of_injective _ (@rangeComposition_injective M P a g.val)
  rw [composition_card] at h
  rw [rangePolynomial_coeff]
  apply h.trans_lt
  exact Nat.pow_lt_pow_right (by decide) (by have := g.isLt; omega)

/-- All actual layout residues are accumulated in a single residue ring.
Every triple appears exactly once by the dependent range index. -/
def rangeResidue (M P a H : ℕ) (layouts : (t:Triple M P)→Layout t.m) : ℕ :=
  (∑t:Triple M P,scalarLayout (layouts t) t.r t.p a (digitBase H:ZMod (modulus H))).val

lemma rangeResidue_eq_eval (M P a H : ℕ) (layouts : (t:Triple M P)→Layout t.m)
    (ha : a=4 ∨ a=5) (hc : ∀t,Covers (layouts t) t.r t.p a) :
    rangeResidue M P a H layouts=(rangePolynomial M P a).eval (digitBase H)%modulus H := by
  unfold rangeResidue
  simp_rw [←eval_raw_eq_scalar _ (Triple.parameters _ ha) (hc _)]
  rw [←Polynomial.eval₂_finsetSum,Polynomial.eval₂_at_natCast]
  exact ZMod.val_natCast _ _

/-- A finite exact aggregate certificate is accepted only by equality of its
source-correct residue and its bounded proposed coefficient vector. -/
def RangeAccepts (M P a H : ℕ) (layouts : (t:Triple M P)→Layout t.m)
    (coeffs : Fin (H+1)→ℕ) : Prop :=
  rangeResidue M P a H layouts=pack (digitBase H) coeffs ∧ ∀i,coeffs i<digitBase H

/-- Complete coefficient soundness of the finite aggregate checker. -/
theorem accepted_range_coeff (M P a H : ℕ) (layouts : (t:Triple M P)→Layout t.m)
    (ha : a=4 ∨ a=5) (hc : ∀t,Covers (layouts t) t.r t.p a)
    (coeffs : Fin (H+1)→ℕ) (accepted : RangeAccepts M P a H layouts coeffs) (k:Fin (H+1)) :
    (rangePolynomial M P a).coeff k.val=coeffs k := by
  have hb : 0<digitBase H := by unfold digitBase; positivity
  have he := accepted.1
  rw [rangeResidue_eq_eval M P a H layouts ha hc] at he
  have hh := accepted_residue_coeff (rangePolynomial M P a) hb
    (range_coeff_lt_digitBase M P a H) he k
  exact hh.trans (digit_pack hb coeffs accepted.2 k)

#print axioms rangeComposition_injective
#print axioms range_coeff_lt_digitBase
#print axioms rangeResidue_eq_eval
#print axioms accepted_range_coeff
end SubmittedGenus.RawGraph.PackedAcceptance
