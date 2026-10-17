import Results.Genus.FiniteComparison.SourceBoxes
import Results.Genus.RawGraph.PackedAcceptance.Aggregation

noncomputable section
open scoped BigOperators
namespace SubmittedGenus.FiniteComparison.RangeSourceBridge
open RawGraph RawGraph.PackedAcceptance SourceBoxes
attribute [local instance] Classical.propDecidable

abbrev BoxIndex (M P : ℕ) := Fin (M+1) × Fin (P+1) × Fin (P+1)
abbrev ValidBox (M P a : ℕ) := {t : BoxIndex M P // Parameters t.1.val t.2.1.val t.2.2.val a}

def toBox {M P a : ℕ} (ha : a=4 ∨ a=5) (t : Triple M P) : ValidBox M P a := by
  have hb:=t.bounds
  have hp:=t.parameters ha
  refine ⟨(⟨t.m,by omega⟩,⟨t.r,?_⟩,⟨t.p,by omega⟩),hp⟩
  unfold Parameters at hp
  omega

def fromBox {M P a : ℕ} (t : ValidBox M P a) : Triple M P := by
  have hp:=t.property
  have hm:=t.val.1.isLt
  have hpp:=t.val.2.2.isLt
  unfold Parameters at hp
  let mi : Fin (M-2) := ⟨t.val.1.val-3,by omega⟩
  let pi : Fin (min P (mi.val+2)-1) := ⟨t.val.2.2.val-2,by dsimp [mi]; omega⟩
  let ri : Fin (pi.val+1) := ⟨t.val.2.1.val-1,by dsimp [pi]; omega⟩
  exact ⟨mi,pi,ri⟩

lemma toBox_injective {M P a : ℕ} (ha : a=4 ∨ a=5) : Function.Injective (toBox (M:=M) (P:=P) ha) := by
  intro t u h
  have h1:=congrArg (fun x : ValidBox M P a => x.val.1.val) h
  have h2:=congrArg (fun x : ValidBox M P a => x.val.2.2.val) h
  have h3:=congrArg (fun x : ValidBox M P a => x.val.2.1.val) h
  rcases t with ⟨⟨m,hm⟩,⟨p,hp⟩,⟨r,hr⟩⟩
  rcases u with ⟨⟨n,hn⟩,⟨q,hq⟩,⟨s,hs⟩⟩
  change m+3=n+3 at h1
  have hmn : m=n := by omega
  subst n
  change p+2=q+2 at h2
  have hpq : p=q := by omega
  subst q
  change r+1=s+1 at h3
  have hrs : r=s := by omega
  subst s
  rfl

lemma to_from {M P a : ℕ} (ha : a=4 ∨ a=5) (t : ValidBox M P a) :
    toBox ha (fromBox t)=t := by
  have hp:=t.property
  unfold Parameters at hp
  apply Subtype.ext
  apply Prod.ext
  · apply Fin.ext
    dsimp [toBox,fromBox,Triple.m]
    omega
  · apply Prod.ext
    · apply Fin.ext
      dsimp [toBox,fromBox,Triple.r]
      omega
    · apply Fin.ext
      dsimp [toBox,fromBox,Triple.p]
      omega

def tripleEquiv {M P a : ℕ} (ha : a=4 ∨ a=5) : Triple M P ≃ ValidBox M P a :=
  Equiv.ofBijective (toBox ha) ⟨toBox_injective ha,fun t => ⟨fromBox t,to_from ha t⟩⟩

lemma range_coeff_eq_box_sum (M P a g : ℕ) (ha : a=4 ∨ a=5) :
    (rangePolynomial M P a).coeff g =
      ∑ t : BoxIndex M P, (rawPolynomial t.1.val t.2.1.val t.2.2.val a).coeff g := by
  let f : BoxIndex M P → ℕ := fun t => (rawPolynomial t.1.val t.2.1.val t.2.2.val a).coeff g
  have he := (tripleEquiv (M:=M) (P:=P) ha).sum_comp (fun t : ValidBox M P a => f t.val)
  have hi : ∑ t : {t : BoxIndex M P // ¬Parameters t.1.val t.2.1.val t.2.2.val a}, f t.val=0 := by
    apply Finset.sum_eq_zero; intro t ht
    simp [f,rawPolynomial_invalid t.property]
  have hs := Fintype.sum_subtype_add_sum_subtype
    (fun t : BoxIndex M P => Parameters t.1.val t.2.1.val t.2.2.val a) f
  rw [hi,Nat.add_zero] at hs
  rw [rangePolynomial,Polynomial.finsetSum_coeff]
  exact he.trans hs

def rectBox (M P a g : ℕ) : ℕ :=
  ∑ m ∈ Finset.range (M+1), ∑ r ∈ Finset.range (P+1), ∑ p ∈ Finset.range (P+1),
    (rawPolynomial m r p a).coeff g

lemma range_coeff_eq_rectBox (M P a g : ℕ) (ha : a=4 ∨ a=5) :
    (rangePolynomial M P a).coeff g = rectBox M P a g := by
  rw [range_coeff_eq_box_sum M P a g ha]
  simp only [BoxIndex,Fintype.sum_prod_type]
  unfold rectBox
  calc
    _ = ∑ m : Fin (M+1), ∑ r : Fin (P+1), ∑ p ∈ Finset.range (P+1),
        (rawPolynomial m.val r.val p a).coeff g := by
      apply Finset.sum_congr rfl; intro m hm
      apply Finset.sum_congr rfl; intro r hr
      exact Fin.sum_univ_eq_sum_range (fun p : ℕ => (rawPolynomial m.val r.val p a).coeff g) (P+1)
    _ = ∑ m : Fin (M+1), ∑ r ∈ Finset.range (P+1), ∑ p ∈ Finset.range (P+1),
        (rawPolynomial m.val r p a).coeff g := by
      apply Finset.sum_congr rfl; intro m hm
      exact Fin.sum_univ_eq_sum_range (fun r : ℕ => ∑ p ∈ Finset.range (P+1),
        (rawPolynomial m.val r p a).coeff g) (P+1)
    _ = _ := Fin.sum_univ_eq_sum_range (fun m : ℕ => ∑ r ∈ Finset.range (P+1),
      ∑ p ∈ Finset.range (P+1), (rawPolynomial m r p a).coeff g) (M+1)

theorem originalFour_range (g : ℕ) :
    (rangePolynomial 597 300 4).coeff g = retainedFour g := by
  exact range_coeff_eq_rectBox 597 300 4 g (Or.inl rfl)

theorem originalFive_range (g : ℕ) :
    (rangePolynomial 293 293 5).coeff g = box 5 294 g := by
  exact range_coeff_eq_rectBox 293 293 5 g (Or.inr rfl)

theorem sufficientFive_range (g : ℕ) :
    (rangePolynomial 149 149 5).coeff g = box 5 150 g := by
  exact range_coeff_eq_rectBox 149 149 5 g (Or.inr rfl)

/-- The sufficient smaller original cap-five range and the retained file range
have equal low-degree coefficients for semantic support reasons. -/
theorem originalFive_eq_sufficient (g : ℕ) (hg : g ≤ 300) :
    (rangePolynomial 293 293 5).coeff g = (rangePolynomial 149 149 5).coeff g := by
  rw [originalFive_range,sufficientFive_range,originalFive_box g hg]

#print axioms originalFour_range
#print axioms originalFive_range
#print axioms originalFive_eq_sufficient

end SubmittedGenus.FiniteComparison.RangeSourceBridge
