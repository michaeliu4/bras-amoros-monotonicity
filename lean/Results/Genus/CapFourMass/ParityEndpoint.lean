import Results.Genus.CapFourMass.ParitySum
import Mathlib.Analysis.SpecificLimits.Normed

noncomputable section
open scoped BigOperators
namespace SubmittedGenus.CapFourMass

def parityEndpoint (A σ : ℝ) (u h : ℕ) : ℝ :=
  A/(1-A)^2 + ((u-h+1 : ℕ)+σ/(1-σ))/(1-A)

lemma parityRow_one_hasSum {A σ : ℝ} (hσ : 0≤σ) (hσ1 : σ<1)
    (u h a : ℕ) (hhu : h≤u) :
    HasSum (parityTerm A 1 σ u h a)
      (A^a*((a:ℝ)+(u-h+1:ℕ)+σ/(1-σ))) := by
  have hs := (stripRow_hasSum (B:=1) (by norm_num) hσ (by simpa using hσ1)
    (a+u-h)).mul_left (A^a)
  have he : a+u-h+1=a+(u-h+1) := by omega
  have hf : parityTerm A 1 σ u h a = fun j => A^a * stripRow 1 σ (a+u-h) j := by
    funext j
    simpa using parityTerm_row A 1 σ u h a j hhu
  rw [hf]
  simpa [he,Nat.cast_add] using hs

lemma parityRows_one_hasSum {A σ : ℝ} (hA : 0≤A) (hA1 : A<1)
    (u h : ℕ) :
    HasSum (fun a : ℕ => A^a*((a:ℝ)+(u-h+1:ℕ)+σ/(1-σ)))
      (parityEndpoint A σ u h) := by
  have hn := hasSum_coe_mul_geometric_of_norm_lt_one (r:=A)
    (by simpa [Real.norm_eq_abs,abs_of_nonneg hA] using hA1)
  have hg := (hasSum_geometric_of_lt_one hA hA1).mul_left
    ((u-h+1:ℕ)+σ/(1-σ):ℝ)
  convert! hn.add hg using 1
  · funext a; ring

 theorem parity_one_hasSum {A σ : ℝ} (hA : 0≤A) (hA1 : A<1)
    (hσ : 0≤σ) (hσ1 : σ<1) (u h : ℕ) (hhu : h≤u) :
    HasSum (fun q : ℕ×ℕ => parityTerm A 1 σ u h q.1 q.2)
      (parityEndpoint A σ u h) := by
  have hr := fun a => parityRow_one_hasSum (A:=A) hσ hσ1 u h a hhu
  have ho := parityRows_one_hasSum (σ:=σ) hA hA1 u h
  have hs : Summable (fun q : ℕ×ℕ => parityTerm A 1 σ u h q.1 q.2) := by
    apply (summable_prod_of_nonneg (fun q => parityTerm_nonneg hA (by norm_num) hσ u h q.1 q.2)).mpr
    exact ⟨fun a => (hr a).summable,by simpa only [(hr _).tsum_eq] using ho.summable⟩
  have ht : (∑' q : ℕ×ℕ,parityTerm A 1 σ u h q.1 q.2)=parityEndpoint A σ u h := by
    rw [hs.tsum_prod]
    simpa only [(hr _).tsum_eq] using ho.tsum_eq
  exact ht ▸ hs.hasSum

#print axioms parity_one_hasSum
end SubmittedGenus.CapFourMass
