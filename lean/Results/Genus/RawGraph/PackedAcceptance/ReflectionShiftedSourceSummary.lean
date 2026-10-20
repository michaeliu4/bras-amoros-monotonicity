import Results.Genus.RawGraph.PackedAcceptance.ReflectionSourcePowerSummary

namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord

/-- Exact phase-aligned window in two copies of a modular source word. -/
lemma modular_word_window {A : Type*} (F : ℕ→A) (L d k0 N : ℕ)
    (hk : k0<L) (hN : N≤L) :
    ((((List.range L).map (fun k=>F ((d*k)%L))) ++
      ((List.range L).map (fun k=>F ((d*k)%L)))).drop k0).take N=
        (List.range N).map (fun k=>F ((d*(k0+k))%L)) := by
  have ht : (List.range (L+L)).map (fun k=>F ((d*k)%L))=
      (List.range L).map (fun k=>F ((d*k)%L)) ++
        (List.range L).map (fun k=>F ((d*k)%L)) := by
    rw [List.range_add,List.map_append,List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    simp [Function.comp_def,Nat.mul_add,Nat.add_mod,Nat.mul_mod]
  rw [←ht,←List.map_drop,←List.map_take,List.range_eq_range',List.drop_range']
  simp only [Nat.zero_add,Nat.mul_one]
  rw [List.take_range'_of_length_ge (by omega : L+L-k0≥N),List.range'_eq_map_range,List.map_map]
  rfl

/-- Reusable full-word summary followed by an arbitrary phase-aligned
subword query; no expanded source list is constructed by this evaluator. -/
def shiftedSourceValue {M : Type*} [Monoid M] (f : Letter→M)
    (L d q k0 N : ℕ) : M :=
  let s:=sourceSummary f L d q
  (s.mul s).slice k0 N

theorem shiftedSourceValue_eq {M : Type*} [Monoid M] (f : Letter→M)
    (L d q k0 N : ℕ) (hd : 0<d) (hdL : d<L) (hq : q≤L-d)
    (hk : k0<L) (hN : N≤L) :
    shiftedSourceValue f L d q k0 N=
      (((List.range N).map (fun k=>reducedLetter L d q ((d*(k0+k))%L))).map f).prod := by
  have hs:=sourceSummary_rep f L d q hd hdL hq
  have hm:=PowerSummary.mul_rep f _ _ _ _ hs hs
  have hv:=hm.2.2 k0 N
  rw [modular_word_window (reducedLetter L d q) L d k0 N hk hN] at hv
  exact hv

/-- Alternate phase presentation used by the fixed raw source adapter. -/
theorem shiftedSourceValue_phase {M : Type*} [Monoid M] (f : Letter→M)
    (L d q k0 N t0 : ℕ) (hd : 0<d) (hdL : d<L) (hq : q≤L-d)
    (hk : k0<L) (hN : N≤L) (ht : t0=(d*k0)%L) :
    shiftedSourceValue f L d q k0 N=
      (((List.range N).map (fun k=>reducedLetter L d q ((t0+d*k)%L))).map f).prod := by
  rw [shiftedSourceValue_eq f L d q k0 N hd hdL hq hk hN,ht]
  congr 2
  apply List.map_congr_left
  intro k _
  congr 1
  simp [Nat.mul_add,Nat.add_mod]

#print axioms shiftedSourceValue_eq
#print axioms shiftedSourceValue_phase
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionThresholdWord
