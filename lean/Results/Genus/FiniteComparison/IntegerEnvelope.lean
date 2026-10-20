import Results.Genus.FiniteComparison.Envelope

/-! Arbitrary integer upper inputs, exactly as in the submitted comparison lemma. -/
noncomputable section
namespace SubmittedGenus.FiniteComparison
open OriginalPopulations OriginalSources FiniteArithmetic
attribute [local instance] Classical.propDecidable

 def signedResidual (g : ℕ) (Ug Uprev Vg : ℤ) : ℤ :=
  Ug-Fintype.card (NWords g)-Fintype.card (NWords (g-3))-
    Fintype.card (NWords (g-4))+Uprev-Fintype.card (NWords (g-1))+Vg

/-- Actual-count upper hypotheses force all supplied integers to be nonnegative,
so no hypothesis or case is lost by transport through Int.toNat. -/
theorem exceptional_le_signed_envelope (g : ℕ) (Ug Uprev Vg : ℤ)
    (hU : (rawFourCount g:ℤ)≤Ug) (hUp : (rawFourCount (g-1):ℤ)≤Uprev)
    (hV : (CapFiveMass.count g:ℤ)≤Vg) :
    (Fintype.card (SourceClass g .E):ℤ)≤signedResidual g Ug Uprev Vg := by
  have hu : 0≤Ug := le_trans (Int.natCast_nonneg _) hU
  have hp : 0≤Uprev := le_trans (Int.natCast_nonneg _) hUp
  have hv : 0≤Vg := le_trans (Int.natCast_nonneg _) hV
  have huc : (Ug.toNat:ℤ)=Ug := Int.toNat_of_nonneg hu
  have hpc : (Uprev.toNat:ℤ)=Uprev := Int.toNat_of_nonneg hp
  have hvc : (Vg.toNat:ℤ)=Vg := Int.toNat_of_nonneg hv
  have hun : rawFourCount g≤Ug.toNat := by
    exact_mod_cast (show (rawFourCount g:ℤ)≤(Ug.toNat:ℤ) from huc.symm ▸ hU)
  have hpn : rawFourCount (g-1)≤Uprev.toNat := by
    exact_mod_cast (show (rawFourCount (g-1):ℤ)≤(Uprev.toNat:ℤ) from hpc.symm ▸ hUp)
  have hvn : CapFiveMass.count g≤Vg.toNat := by
    exact_mod_cast (show (CapFiveMass.count g:ℤ)≤(Vg.toNat:ℤ) from hvc.symm ▸ hV)
  have h:=exceptional_le_integer_envelope g Ug.toNat Uprev.toNat Vg.toNat hun hpn hvn
  simpa only [residualUpper,signedResidual,huc,hpc,hvc] using h

#print axioms exceptional_le_signed_envelope
end SubmittedGenus.FiniteComparison
