import Results.Genus.CapFourMass.OrderedModeCoverage
import Results.Genus.CapFourMass.SourceAllPlus

/-! Complete source mode sums bounded by a finitely checked supplied run code.
The topology, signed physical normalization, and shared-label coverage are
consumed explicitly; no executable ordering is identified by mere signatures. -/
noncomputable section
open scoped BigOperators Matrix
namespace SubmittedGenus.CapFourMass.ExecutableModes
open RawGraph RawGraph.Topology FixedPivot SourceCoreFactorization CarryLocalization ActualComponent
attribute [local instance] Classical.propDecidable Classical.decEq

section Source
variable {r N d : ℕ} (hr : 0<r) (hd : 0<d) (hN : d<N) (hbig : 2*d<N)
variable (c : SourceComponent r N d) (O : OrderedComponent c.toSimpleGraph)

include hr in
lemma ordered_path_mass_eq_code (choice : Option (CarryRepresentative N d hN)→Mode)
    (hc : O.cycle=false) (q : TaggedPathCode (Option (CarryRepresentative N d hN)))
    (hcheck : pathCodeCheck (pathTags hd hN (orderedVertex c O)) q=true) :
    orderedMass c O (sourceSignedKernel hd hN choice)=
      orderedHalf c O 0 ⬝ᵥ ((q.matrixWith (labelledModeMatrix choice))*ᵥ orderedHalf c O (Fin.last _)) := by
  rw [orderedMass_path_eq_tags hr hd hN choice c O hc,
    pathCodeCheck_sound (labelledModeMatrix choice) _ q hcheck]

include hr in
lemma ordered_cycle_mass_eq_code (choice : Option (CarryRepresentative N d hN)→Mode)
    (hc : O.cycle=true) (rotation : ℕ)
    (bs : List (TaggedBlock (Option (CarryRepresentative N d hN))))
    (hcheck : cycleCodeCheck (cycleTags hd hN (orderedVertex c O)) rotation bs=true) :
    orderedMass c O (sourceSignedKernel hd hN choice)=
      ((bs.map (TaggedBlock.matrixWith (labelledModeMatrix choice))).prod).trace := by
  rw [orderedMass_cycle_eq_tags hr hd hN choice c O hc,
    ←matrix_word_trace_rotate (TaggedEdge.matrixWith (labelledModeMatrix choice))
      (cycleTags hd hN (orderedVertex c O)) rotation,
    cycleCodeCheck_sound_rotated (labelledModeMatrix choice) _ rotation bs hcheck]

/-- Empty mode fibers include the genuine zero-edge low/core branch. -/
lemma ordered_path_empty_absolute_le (hc : O.cycle=false)
    (hempty : IsEmpty (ModeFiber hr hN hbig c))
    (q : TaggedPathCode (Option (CarryRepresentative N d hN)))
    (hcheck : pathCodeCheck (pathTags hd hN (orderedVertex c O)) q=true) :
    (∑ b : ModeFiber hr hN hbig c→Bool,
      |orderedMass c O (sourceSignedKernel hd hN (componentChoice hr hN hbig c b))|)≤
      q.erase.absolute (orderedHalf c O 0) (orderedHalf c O (Fin.last _)) := by
  letI := hempty
  simp_rw [ordered_path_mass_eq_code hr hd hN c O _ hc q hcheck]
  cases q with
  | pure s => simp [TaggedPathCode.matrixWith,TaggedPathCode.erase,PathCode.absolute]
  | carried pre tag n hn bs post =>
    exact tagged_path_absolute_sum_le (componentChoice hr hN hbig c)
      pre post tag n hn bs (orderedHalf c O 0) (orderedHalf c O (Fin.last _))
      (fun _ _ _ => Subsingleton.elim _ _)

/-- Positive-edge source variables inject into the actual checked carry slots. -/
lemma ordered_path_positive_absolute_le (hc : O.cycle=false) (hn : O.edges≠0)
    (q : TaggedPathCode (Option (CarryRepresentative N d hN)))
    (hcheck : pathCodeCheck (pathTags hd hN (orderedVertex c O)) q=true) :
    (∑ b : ModeFiber hr hN hbig c→Bool,
      |orderedMass c O (sourceSignedKernel hd hN (componentChoice hr hN hbig c b))|)≤
      q.erase.absolute (orderedHalf c O 0) (orderedHalf c O (Fin.last _)) := by
  cases q with
  | pure s =>
    exact ordered_path_empty_absolute_le hr hd hN hbig c O hc
      (ordered_pure_fiber_empty hr hd hN hbig c O hc hn s hcheck) (.pure s) hcheck
  | carried pre tag n hn' bs post =>
    simp_rw [ordered_path_mass_eq_code hr hd hN c O _ hc (.carried pre tag n hn' bs post) hcheck]
    exact tagged_path_absolute_sum_le (componentChoice hr hN hbig c)
      pre post tag n hn' bs (orderedHalf c O 0) (orderedHalf c O (Fin.last _))
      (component_slot_injective hr hN hbig c bs tag
        (ordered_path_slot_coverage hr hd hN hbig c O hc hn pre post tag n hn' bs hcheck))

/-- Every ordinary supplied path branch. The isolated high carry-loop branch
uses its separate free/loop source convention and is deliberately excluded. -/
theorem ordered_path_absolute_le (hc : O.cycle=false)
    (hcase : O.edges≠0 ∨ physical (orderedVertex c O 0)≤r)
    (q : TaggedPathCode (Option (CarryRepresentative N d hN)))
    (hcheck : pathCodeCheck (pathTags hd hN (orderedVertex c O)) q=true) :
    (∑ b : ModeFiber hr hN hbig c→Bool,
      |orderedMass c O (sourceSignedKernel hd hN (componentChoice hr hN hbig c b))|)≤
      q.erase.absolute (orderedHalf c O 0) (orderedHalf c O (Fin.last _)) := by
  by_cases hn : O.edges≠0
  · exact ordered_path_positive_absolute_le hr hd hN hbig c O hc hn q hcheck
  · have hz : O.edges=0 := not_ne_iff.mp hn
    exact ordered_path_empty_absolute_le hr hd hN hbig c O hc
      (ordered_zero_low_fiber_empty hr hd hN hbig c O hz (hcase.resolve_left hn)) q hcheck

/-- The cycle retains the supplied rotation and its checked closing slot. -/
theorem ordered_cycle_absolute_le (hc : O.cycle=true) (rotation : ℕ)
    (bs : List (TaggedBlock (Option (CarryRepresentative N d hN))))
    (hcheck : cycleCodeCheck (cycleTags hd hN (orderedVertex c O)) rotation bs=true) :
    (∑ b : ModeFiber hr hN hbig c→Bool,
      |orderedMass c O (sourceSignedKernel hd hN (componentChoice hr hN hbig c b))|)≤
      coupledCycleAbsolute (bs.map TaggedBlock.run) := by
  have hne:=((cycleCodeCheck_eq_true _ _ _).mp hcheck).1
  simp_rw [ordered_cycle_mass_eq_code hr hd hN c O _ hc rotation bs hcheck]
  cases bs with
  | nil => contradiction
  | cons b bs =>
    have hinj:=component_slot_injective hr hN hbig c bs b.label
      (ordered_cycle_slot_coverage hr hd hN hbig c O hc rotation b bs hcheck)
    simpa only [List.map_cons,List.prod_cons] using
      tagged_cycle_absolute_sum_le (componentChoice hr hN hbig c) b bs hinj

include hr in
lemma ordered_allPlus_nonneg :
    0≤orderedMass c O (sourceSignedKernel hd hN (fun _ => 0)) := by
  rw [orderedMass_eq_physical c O _ (sourceSignedKernel_symmetric hr hd hN (fun _ => 0))]
  exact physical_allPlus_nonneg hd hN c

/-- The exact distinguished coefficient is subtracted after the complete
source scalar sum. All non-all-plus assignments, including all-minus, remain. -/
theorem ordered_path_mixed_le (hc : O.cycle=false)
    (hcase : O.edges≠0 ∨ physical (orderedVertex c O 0)≤r)
    (q : TaggedPathCode (Option (CarryRepresentative N d hN)))
    (hcheck : pathCodeCheck (pathTags hd hN (orderedVertex c O)) q=true) :
    (∑ b : ModeFiber hr hN hbig c→Bool,if b=(fun _ => false) then 0 else
      |orderedMass c O (sourceSignedKernel hd hN (componentChoice hr hN hbig c b))|)≤
      q.erase.absolute (orderedHalf c O 0) (orderedHalf c O (Fin.last _))-
        orderedHalf c O 0 ⬝ᵥ ((q.matrixWith (labelledModeMatrix (fun _ => 0)))*ᵥ
          orderedHalf c O (Fin.last _)) := by
  have hh:=mixed_le_sub_of_total_le
    (fun b : ModeFiber hr hN hbig c→Bool =>
      orderedMass c O (sourceSignedKernel hd hN (componentChoice hr hN hbig c b)))
    (fun _ => false) _ (ordered_path_absolute_le hr hd hN hbig c O hc hcase q hcheck)
  rw [componentChoice_allPlus,abs_of_nonneg (ordered_allPlus_nonneg hr hd hN c O),
    ordered_path_mass_eq_code hr hd hN c O (fun _ => 0) hc q hcheck] at hh
  convert hh using 1
  apply Finset.sum_congr rfl
  intro b _
  split_ifs <;> rfl

theorem ordered_cycle_mixed_le (hc : O.cycle=true) (rotation : ℕ)
    (bs : List (TaggedBlock (Option (CarryRepresentative N d hN))))
    (hcheck : cycleCodeCheck (cycleTags hd hN (orderedVertex c O)) rotation bs=true) :
    (∑ b : ModeFiber hr hN hbig c→Bool,if b=(fun _ => false) then 0 else
      |orderedMass c O (sourceSignedKernel hd hN (componentChoice hr hN hbig c b))|)≤
      coupledCycleAbsolute (bs.map TaggedBlock.run)-
        ((bs.map (TaggedBlock.matrixWith (labelledModeMatrix (fun _ => 0)))).prod).trace := by
  have hh:=mixed_le_sub_of_total_le
    (fun b : ModeFiber hr hN hbig c→Bool =>
      orderedMass c O (sourceSignedKernel hd hN (componentChoice hr hN hbig c b)))
    (fun _ => false) _ (ordered_cycle_absolute_le hr hd hN hbig c O hc rotation bs hcheck)
  rw [componentChoice_allPlus,abs_of_nonneg (ordered_allPlus_nonneg hr hd hN c O),
    ordered_cycle_mass_eq_code hr hd hN c O (fun _ => 0) hc rotation bs hcheck] at hh
  convert hh using 1
  apply Finset.sum_congr rfl
  intro b _
  split_ifs <;> rfl

end Source
end SubmittedGenus.CapFourMass.ExecutableModes
