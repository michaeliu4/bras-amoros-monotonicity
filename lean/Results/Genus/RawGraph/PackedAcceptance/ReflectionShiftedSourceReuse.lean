import Results.Genus.RawGraph.PackedAcceptance.ReflectionShiftedSourceSummary

namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord

/-- Reuse one materialized summary for many component windows. The no-wrap
branch avoids constructing a doubled whole-word value that is never queried. -/
def PowerSummary.cyclicSlice {M : Type*} [Monoid M] (s : PowerSummary M) (k0 N : ℕ) : M :=
  if k0+N≤s.length then s.slice k0 N
  else s.slice k0 (s.length-k0)*s.slice 0 (N-(s.length-k0))

lemma PowerSummary.cyclicSlice_rep {A M : Type*} [Monoid M] (f : A→M)
    (s : PowerSummary M) (w : List A) (hs : s.Rep f w) (k0 N : ℕ) (hk : k0≤w.length) :
    s.cyclicSlice k0 N=((((w++w).drop k0).take N).map f).prod := by
  rcases hs with ⟨hlen,hval,hquery⟩
  unfold cyclicSlice
  rw [hlen,List.drop_append_of_le_length hk,List.take_append,List.length_drop,
    List.map_append,List.prod_append]
  split
  · rename_i hn
    rw [hquery,show N-(w.length-k0)=0 by omega]
    simp
  · rename_i hn
    rw [hquery,hquery,List.drop_zero]
    have he : ((w.drop k0).take (w.length-k0))=((w.drop k0).take N) := by
      rw [List.take_of_length_le (by simp),List.take_of_length_le (by simp only [List.length_drop];omega)]
    rw [he]

/-- Exact shifted product with one summary already built and ready to share. -/
theorem sourceSummary_cyclicSlice {M : Type*} [Monoid M] (f : Letter→M)
    (L d q k0 N : ℕ) (hd : 0<d) (hdL : d<L) (hq : q≤L-d)
    (hk : k0<L) (hN : N≤L) :
    (sourceSummary f L d q).cyclicSlice k0 N=
      (((List.range N).map (fun k=>reducedLetter L d q ((d*(k0+k))%L))).map f).prod := by
  rw [PowerSummary.cyclicSlice_rep f _ _ (sourceSummary_rep f L d q hd hdL hq) k0 N
    (by simp;omega),modular_word_window (reducedLetter L d q) L d k0 N hk hN]

lemma sourceSummary_cyclicSlice_eq {M : Type*} [Monoid M] (f : Letter→M)
    (L d q k0 N : ℕ) (hd : 0<d) (hdL : d<L) (hq : q≤L-d)
    (hk : k0<L) (hN : N≤L) :
    (sourceSummary f L d q).cyclicSlice k0 N=shiftedSourceValue f L d q k0 N := by
  rw [sourceSummary_cyclicSlice f L d q k0 N hd hdL hq hk hN,
    shiftedSourceValue_eq f L d q k0 N hd hdL hq hk hN]

#print axioms sourceSummary_cyclicSlice
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord
