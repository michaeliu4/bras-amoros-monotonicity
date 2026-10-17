import Results.Genus.CapFourMass.ParityEndpoint

noncomputable section
open scoped BigOperators Topology
namespace SubmittedGenus.CapFourMass

def parityRegular (A B σ : ℝ) (u h : ℕ) : ℝ :=
  B^h*((∑ i ∈ Finset.range (u+1-h), B^i)/(1-A*B^2)+
    A*B/((1-A*B)*(1-A*B^2)))+
    B^(u+1)*σ/((1-B*σ)*(1-A*B^2))

lemma parityRational_eq_regular {A B σ : ℝ} (u h : ℕ) (hhu : h≤u)
    (hB : B≠1) (hAB : 1-A*B≠0) (hAB2 : 1-A*B^2≠0)
    (hBs : 1-B*σ≠0) :
    parityRational A B σ u h = parityRegular A B σ u h := by
  have hs : (∑ i ∈ Finset.range (u+1-h), B^i)=(1-B^(u+1-h))/(1-B) := by
    apply (eq_div_iff (sub_ne_zero.mpr hB.symm)).mpr
    exact geom_sum_mul_neg B (u+1-h)
  have hp : B^(u+1)=B^h*B^(u+1-h) := by
    rw [←pow_add]; congr 1; omega
  unfold parityRegular parityRational
  rw [hs,hp]
  field_simp [hAB,hAB2,hBs,sub_ne_zero.mpr hB.symm]
  <;> ring_nf
  have h1 : 1-B*A≠0 := by simpa [mul_comm] using hAB
  have h2 : 1-B^2*A≠0 := by simpa [mul_comm] using hAB2
  field_simp [h1,h2]
  <;> ring

lemma parityRegular_one {A σ : ℝ} (u h : ℕ) (hhu : h≤u) :
    parityRegular A 1 σ u h=parityEndpoint A σ u h := by
  have he : u+1-h=u-h+1 := by omega
  simp [parityRegular,parityEndpoint,he,pow_two,div_eq_mul_inv]
  <;> ring

lemma parityRegular_continuousAt_one {A σ : ℝ} (hA : A≠1) (hσ : σ≠1)
    (u h : ℕ) : ContinuousAt (fun B => parityRegular A B σ u h) 1 := by
  have ha : (1:ℝ)-A≠0 := sub_ne_zero.mpr hA.symm
  have hs : (1:ℝ)-σ≠0 := sub_ne_zero.mpr hσ.symm
  unfold parityRegular
  fun_prop (disch := norm_num [ha,hs])

/-- The manuscript's removable B=1 interpretation, as an actual punctured limit. -/
theorem parityRational_tendsto_one {A σ : ℝ} (hA : A≠1) (hσ : σ≠1)
    (u h : ℕ) (hhu : h≤u) :
    Filter.Tendsto (fun B => parityRational A B σ u h)
      (nhdsWithin 1 ({1}ᶜ : Set ℝ)) (nhds (parityEndpoint A σ u h)) := by
  have ha : (1:ℝ)-A≠0 := sub_ne_zero.mpr hA.symm
  have hs : (1:ℝ)-σ≠0 := sub_ne_zero.mpr hσ.symm
  have hc1 : ContinuousAt (fun B : ℝ => 1-A*B) 1 := by fun_prop
  have hc2 : ContinuousAt (fun B : ℝ => 1-A*B^2) 1 := by fun_prop
  have hc3 : ContinuousAt (fun B : ℝ => 1-B*σ) 1 := by fun_prop
  have he1 := hc1.eventually_ne (by simpa using ha)
  have he2 := hc2.eventually_ne (by simpa using ha)
  have he3 := hc3.eventually_ne (by simpa using hs)
  have heq : (fun B => parityRational A B σ u h) =ᶠ[nhdsWithin 1 ({1}ᶜ : Set ℝ)]
      (fun B => parityRegular A B σ u h) := by
    filter_upwards [self_mem_nhdsWithin,he1.filter_mono nhdsWithin_le_nhds,
      he2.filter_mono nhdsWithin_le_nhds,he3.filter_mono nhdsWithin_le_nhds] with B hb h1 h2 h3
    exact parityRational_eq_regular u h hhu (by simpa using hb) h1 h2 h3
  have ht : Filter.Tendsto (fun B => parityRegular A B σ u h)
      (nhdsWithin 1 ({1}ᶜ : Set ℝ)) (nhds (parityRegular A 1 σ u h)) :=
    (parityRegular_continuousAt_one hA hσ u h).tendsto.mono_left nhdsWithin_le_nhds
  rw [parityRegular_one u h hhu] at ht
  exact ht.congr' heq.symm

#print axioms parityRational_tendsto_one
end SubmittedGenus.CapFourMass
