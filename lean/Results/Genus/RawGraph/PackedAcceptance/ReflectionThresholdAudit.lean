import Results.Genus.RawGraph.PackedAcceptance.ReflectionDeltaOneProduct

namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord.Audit
open ReflectionPairedOrbit CompressedSignature

/-- A long actual-source cycle. Only scalar parameter facts are decided;
its 200 masks and 200 edges are discharged by the uniform source theorem. -/
def longCanonical : ComponentSignature 4 :=
  canonicalSignature (g:=4) 98 1 5 1 4 rfl (by decide) 2
    (by decide +kernel) (by decide) (by decide +kernel)

theorem long_original_signature : longCanonical=deltaOneSignature 98 4 0 := by
  exact canonicalSignature_delta_one (g:=4) 98 1 5 4 (by omega) rfl (by omega)
    (by decide) 2 (by decide +kernel) (by decide) (by decide +kernel)

theorem long_original_word : sourceSteps longCanonical=List.replicate 199 (carryStep 4) := by
  rw [long_original_signature,deltaOneSignature_sourceSteps 98 4 0 (by omega)]
  rfl

/-- A source cycle with both ordinary runs nonempty. -/
def mixedCanonical : ComponentSignature 4 :=
  canonicalSignature (g:=4) 5 9 13 1 4 rfl (by decide) 2
    (by decide +kernel) (by decide) (by decide +kernel)

theorem mixed_original_signature : mixedCanonical=deltaOneSignature 5 4 2 := by
  exact canonicalSignature_delta_one (g:=4) 5 9 13 4 (by omega) rfl (by omega)
    (by decide) 2 (by decide +kernel) (by decide) (by decide +kernel)

theorem mixed_original_word : sourceSteps mixedCanonical=
    List.replicate 4 (fullStep 4) ++ List.replicate 9 (carryStep 4) := by
  rw [mixed_original_signature,deltaOneSignature_sourceSteps 5 4 2 (by omega)]

end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord.Audit

#print axioms SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord.no_self_pair
#print axioms SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord.vertex_no_loops
#print axioms SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord.vertex_domain
#print axioms SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord.paired_arithmetic
#print axioms SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord.paired_source_letter
#print axioms SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord.lt_cut_iff
#print axioms SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord.delta_one_letter
#print axioms SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord.delta_one_word
#print axioms SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord.delta_one_product
#print axioms SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord.canonicalSignature_delta_one
#print axioms SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord.deltaOneSignature_sourceSteps
#print axioms SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord.deltaOneSignature_matrix_product
#print axioms SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord.deltaOneSignature_terminal
#print axioms SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord.canonicalSignature_matrix_value
#print axioms SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord.Audit.long_original_signature
#print axioms SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord.Audit.long_original_word
#print axioms SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord.Audit.mixed_original_signature
#print axioms SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord.Audit.mixed_original_word
