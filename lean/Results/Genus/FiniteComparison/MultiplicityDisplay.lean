import Results.Genus.RawGraph.PackedAcceptance.Coverage

/-! The submitted retained cap-four range has595 disjoint multiplicity classes.
This is the outer index of the original Triple597300 source, not a graph-table
acceptance statement. The two graph-triple counts are proved in Coverage. -/
namespace SubmittedGenus.FiniteComparison

lemma original_multiplicity_class_count : Fintype.card (Fin (597-2)) = 595 := by norm_num
lemma original_multiplicity_interval_count : (Finset.Icc 3 597).card = 595 := by norm_num

end SubmittedGenus.FiniteComparison
