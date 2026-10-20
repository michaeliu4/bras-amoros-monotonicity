import Results.Genus.CapFourMass.RunGeometry
import Results.Genus.CapFiveMass.StrongIncidenceBound
import Results.Genus.CapFiveMass.MissingCount

/-! Exact original source counts in the computed D/E/C word convention. -/
noncomputable section
open scoped BigOperators
namespace SubmittedGenus.CapFourMass.ActualComponent
open RawGraph RawGraph.SourceModel RawGraph.Topology RawGraph.Incidence

/-- Include the closing edge once exactly when the component is a cycle. -/
def sourceWord {m r p : ℕ} (c : Component m r p) : List EdgeKind :=
  if (freeComponentOrder m r p c).cycle=true then closedWord c else pathWord c

def strongLength (l : List EdgeKind) : ℕ := (l.map (fun k => if k=.carry then 0 else 1)).sum
def carryLength (l : List EdgeKind) : ℕ := (l.map (fun k => if k=.carry then 1 else 0)).sum
def restrictedLength (l : List EdgeKind) : ℕ := (l.map (fun k => if k=.restricted then 1 else 0)).sum

def totalStrongLength (m r p : ℕ) : ℕ := ∑ c : Component m r p,strongLength (sourceWord c)
def totalCarryLength (m r p : ℕ) : ℕ := ∑ c : Component m r p,carryLength (sourceWord c)
def totalRestrictedLength (m r p : ℕ) : ℕ := ∑ c : Component m r p,restrictedLength (sourceWord c)

lemma length_eq_strong_add_carry (l : List EdgeKind) : l.length=strongLength l+carryLength l := by
  induction l with
  | nil => rfl
  | cons k l ih =>
    simp only [List.length_cons,strongLength,carryLength,List.map_cons,List.sum_cons] at *
    split_ifs <;> omega

lemma strong_kind_indicator {m r p : ℕ} (i j : Fin (m-1)) :
    (if kind r p i j=.carry then 0 else 1) =
      (if physical i+physical j=r ∨ physical i+physical j=p then 1 else 0) := by
  unfold kind
  split_ifs <;> simp_all
lemma carry_kind_indicator {m r p : ℕ} (i j : Fin (m-1)) :
    (if kind r p i j=.carry then 1 else 0) =
      (if physical i+physical j=r ∨ physical i+physical j=p then 0 else 1) := by
  unfold kind
  split_ifs <;> simp_all
lemma restricted_kind_indicator {m r p : ℕ} (i j : Fin (m-1)) :
    (if kind r p i j=.restricted then 1 else 0) =
      (if (physical i+physical j=r ∨ physical i+physical j=p) ∧ r<physical i ∧ r<physical j then 1 else 0) := by
  unfold kind
  split_ifs <;> simp_all

lemma word_strong_count {m r p : ℕ} (c : Component m r p) :
    strongLength (sourceWord c)=CapFiveMass.ActualComponent.strongCount c := by
  have hpath : strongLength (pathWord c)=CapFiveMass.ActualComponent.pathStrongCount c := by
    unfold strongLength pathWord CapFiveMass.ActualComponent.pathStrongCount
    simp only [List.map_ofFn,Function.comp_def,List.sum_ofFn,strong_kind_indicator]
    rw [Finset.card_filter]
    rfl
  unfold sourceWord
  split_ifs with hc
  · simp only [closedWord,strongLength,List.map_append,List.map_cons,List.map_nil,List.sum_append,
      List.sum_cons,List.sum_nil,add_zero]
    change strongLength (pathWord c)+_= _
    rw [hpath,strong_kind_indicator]
    unfold CapFiveMass.ActualComponent.strongCount
    simp only [hc,true_and,CapFiveMass.LocalSource.StrongEdge]
    rfl
  · rw [hpath]
    simp only [CapFiveMass.ActualComponent.strongCount,hc,Bool.false_eq_true,false_and,if_false,add_zero]

lemma word_carry_count {m r p : ℕ} (c : Component m r p) :
    carryLength (sourceWord c)=CapFiveMass.ActualComponent.carryCount c := by
  have hpath : carryLength (pathWord c)=CapFiveMass.ActualComponent.pathCarryCount c := by
    unfold carryLength pathWord CapFiveMass.ActualComponent.pathCarryCount
    simp only [List.map_ofFn,Function.comp_def,List.sum_ofFn,carry_kind_indicator]
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro j _
    simp only [ite_not]
    rfl
  unfold sourceWord
  split_ifs with hc
  · simp only [closedWord,carryLength,List.map_append,List.map_cons,List.map_nil,List.sum_append,
      List.sum_cons,List.sum_nil,add_zero]
    change carryLength (pathWord c)+_= _
    rw [hpath,carry_kind_indicator]
    unfold CapFiveMass.ActualComponent.carryCount
    simp only [hc,true_and,ite_not]
    rfl
  · rw [hpath]
    simp only [CapFiveMass.ActualComponent.carryCount,hc,Bool.false_eq_true,false_and,if_false,add_zero]

lemma total_strong_eq (m r p : ℕ) : totalStrongLength m r p=CapFiveMass.ActualComponent.totalStrongCount m r p := by
  unfold totalStrongLength CapFiveMass.ActualComponent.totalStrongCount
  simp_rw [word_strong_count]
lemma total_carry_eq (m r p : ℕ) : totalCarryLength m r p=CapFiveMass.ActualComponent.totalCarryCount m r p := by
  unfold totalCarryLength CapFiveMass.ActualComponent.totalCarryCount
  simp_rw [word_carry_count]

/-- The all-parameter exact e_D formula applies to the compiled source words,
not merely an external graph edge set. -/
theorem total_strong_formula {m r p : ℕ} (hp : Parameters m r p 4) :
    totalStrongLength m r p=(r-1)/2+(p-1)/2-(if p=2*r then 0 else 1) := by
  rw [total_strong_eq,← CapFiveMass.ActualComponent.strong_edges_match]
  exact StrongEdgeCounts.strong_edges_formula hp

/-- The exponent enlargement in the paper uses the actual global edge count. -/
theorem total_carry_le_vertices_sub_strong {m r p : ℕ} (hp : Parameters m r p 4) :
    totalCarryLength m r p≤m-3-totalStrongLength m r p := by
  have hh := CapFiveMass.ActualComponent.total_incidence_count m r p
  have hf := freeVertex_card hp
  rw [hf] at hh
  rw [total_carry_eq,total_strong_eq]
  omega

/-- All at-most-two free endpoint incidences belong to the same actual graph
used by the cap-four source and its endpoint vectors. -/
theorem free_endpoint_count_le_two {m r p : ℕ} (hp : Parameters m r p 4) :
    CapFiveMass.ActualComponent.totalEndpointCount m r p .free≤2 :=
  CapFiveMass.MissingGeometry.free_endpoint_count_le_two hp

/-- Maximal-run compilation preserves each exponent, including the E count. -/
theorem run_exponents_preserved (l : List EdgeKind) :
    strongLength l=((RunSegmentation.runs id l).map strongLength).sum ∧
    carryLength l=((RunSegmentation.runs id l).map carryLength).sum ∧
    restrictedLength l=((RunSegmentation.runs id l).map restrictedLength).sum := by
  exact ⟨RunSegmentation.sum_runs id l _,RunSegmentation.sum_runs id l _,RunSegmentation.sum_runs id l _⟩

end SubmittedGenus.CapFourMass.ActualComponent
