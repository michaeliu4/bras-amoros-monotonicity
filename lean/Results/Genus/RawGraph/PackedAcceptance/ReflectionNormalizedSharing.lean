import Results.Genus.RawGraph.PackedAcceptance.ReflectionNormalizedSignature
import Results.Genus.RawGraph.PackedAcceptance.ReflectionChunkClosure
import Results.Genus.RawGraph.PackedAcceptance.ReflectionChunkMacros

/-! All nonzero paired components at fixed original pivots use at most two
normalized full signatures. Multiplicities are not asserted here. -/
namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord
open SourceModel ReflectionPairedOrbit ReflectionFullLayout
open ReflectionPairedPhysicalLabels

variable {g : ℕ} [NeZero g]

theorem physicalSignature_normalized (n r p δ cap : ℕ) (hr : 0<r) (hδ : 0<δ)
    (hc : Nat.Coprime δ (n+2)) (hp : p=r+g*δ)
    (hp0 : 0<p) (hpm : p<g*(n+2)) (c : Fin (count (g:=g) r))
    (hpair : representative r c≠mate r (representative r c))
    (ha0 : representative r c≠0) :
    physicalSignature (layout n r p δ hc hp hp0 hpm) r p cap c=
      normalizedSignature n δ cap (cut g (representative r c).val r) := by
  rw [physicalSignature_eq_canonical n r p δ cap hc hp hp0 hpm c hpair ha0]
  exact canonicalSignature_normalized n r p δ cap hr hδ hp hpm hc
    (representative r c) (representative_le r c) ha0 hpair

theorem physicalSignature_two_keys (n r p δ cap : ℕ) (hr : 0<r) (hδ : 0<δ)
    (hc : Nat.Coprime δ (n+2)) (hp : p=r+g*δ)
    (hp0 : 0<p) (hpm : p<g*(n+2)) (c : Fin (count (g:=g) r))
    (hpair : representative r c≠mate r (representative r c))
    (ha0 : representative r c≠0) :
    physicalSignature (layout n r p δ hc hp hp0 hpm) r p cap c=
      normalizedSignature n δ cap (r/g+(if (representative r c).val<r%g then 1 else 0)) := by
  rw [physicalSignature_normalized n r p δ cap hr hδ hc hp hp0 hpm c hpair ha0,
    cut_residue_formula g (representative r c).val r (NeZero.pos g) (representative r c).isLt]

#print axioms physicalSignature_normalized
#print axioms physicalSignature_two_keys
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord
