import Results.Genus.Injection.ReservoirSources

noncomputable section
namespace SubmittedGenus.OriginalReservoir
open FiniteArithmetic.Reservoir OriginalMaps
attribute [local instance] Classical.propDecidable

/-- A package of proved literal properties, used uniformly for the two
submitted families. This adds no new family and no counting premise. -/
structure PrefixFamily (C : Type) where
  decode : C → List ℕ
  weight : C → ℕ
  weight_eq : ∀ c, (decode c).sum = weight c
  decode_injective : Function.Injective decode
  admissible : ∀ c, PrefixAdmissible (decode c)
  terminal : ∀ c, ∃ q, decode c = q ++ [3]

def safeFamily : PrefixFamily SafeCode :=
  ⟨SafeCode.decode, SafeCode.weight, SafeCode.decode_weight,
    SafeCode.decode_injective, safe_admissible, safe_terminal⟩

def earlyFamily : PrefixFamily EarlyCode :=
  ⟨EarlyCode.decode, EarlyCode.weight, EarlyCode.decode_weight,
    EarlyCode.decode_injective, early_admissible, early_terminal⟩

/-- All physical prefix/tail candidates at the source-genus index `g`.
The `+1` is the manuscript's shift from base weight to source genus. -/
def Candidate {C : Type} (F : PrefixFamily C) (g : ℕ) :=
  {s : C × List ℕ // BinaryTail s.2 ∧ F.weight s.1 + s.2.sum + 1 = g}

abbrev SafeBaseAt (g : ℕ) := Candidate safeFamily g
abbrev EarlyBaseAt (g : ℕ) := Candidate earlyFamily g

def Candidate.data {C : Type} {F : PrefixFamily C} {g : ℕ} (s : Candidate F g) : KunzData :=
  baseData (F.decode s.val.1) s.val.2 (F.admissible _) s.property.1

lemma Candidate.data_weight {C : Type} {F : PrefixFamily C} {g : ℕ} (s : Candidate F g) :
    s.data.weight + 1 = g := by
  rw [Candidate.data, baseData_weight, F.weight_eq]
  exact s.property.2

lemma Candidate.data_depth {C : Type} {F : PrefixFamily C} {g : ℕ} (s : Candidate F g) :
    s.data.depth = 3 := by
  apply baseData_depth
  obtain ⟨q,hq⟩ := F.terminal s.val.1
  simp [hq]

lemma Candidate.data_injective {C : Type} {F : PrefixFamily C} {g : ℕ} :
    Function.Injective (@Candidate.data C F g) := by
  intro a b h
  have he := baseData_injective (F.admissible _) (F.admissible _)
    a.property.1 b.property.1 (F.terminal _) (F.terminal _) h
  exact Subtype.ext (Prod.ext (F.decode_injective he.1) he.2)

def candidateIntoWeight {C : Type} (F : PrefixFamily C) (g : ℕ) :
    Candidate F g ↪ KunzData.WeightFibre (g-1) where
  toFun s := ⟨s.data, by have := s.data_weight; omega⟩
  inj' a b h := Candidate.data_injective (congrArg Subtype.val h)

instance {C : Type} (F : PrefixFamily C) (g : ℕ) : Finite (Candidate F g) :=
  Finite.of_injective (candidateIntoWeight F g) (candidateIntoWeight F g).injective

instance {C : Type} (F : PrefixFamily C) (g : ℕ) : Fintype (Candidate F g) := Fintype.ofFinite _

/-- Good and bad bases are kept separately within each original family. -/
abbrev GoodCandidate {C : Type} (F : PrefixFamily C) (g : ℕ) :=
  {s : Candidate F g // FullyWitnessed (F.decode s.val.1) s.val.2}

abbrev BadCandidate {C : Type} (F : PrefixFamily C) (g : ℕ) :=
  {s : Candidate F g // ¬ FullyWitnessed (F.decode s.val.1) s.val.2}

/-- A failed mark records an actual occurrence, hence multiplicities of
failures in one bad base are retained exactly as in `U_s` and `U_e`. -/
abbrev FailedMark {C : Type} (F : PrefixFamily C) (g : ℕ) :=
  Σ s : Candidate F g, {i : Fin (F.decode s.val.1).length //
    (F.decode s.val.1)[i.val] = 3 ∧
      ¬ TailWitness s.val.2 ((F.decode s.val.1).length - 1 - i.val)}

lemma bad_has_failed_mark {C : Type} {F : PrefixFamily C} {g : ℕ} (s : BadCandidate F g) :
    ∃ i : Fin (F.decode s.val.val.1).length,
      (F.decode s.val.val.1)[i.val] = 3 ∧
        ¬ TailWitness s.val.val.2 ((F.decode s.val.val.1).length - 1 - i.val) := by
  have h := s.property
  unfold FullyWitnessed at h
  push_neg at h
  exact h

def badIntoFailed {C : Type} (F : PrefixFamily C) (g : ℕ) :
    BadCandidate F g ↪ FailedMark F g where
  toFun s := ⟨s.val, Classical.choose (bad_has_failed_mark s),
    Classical.choose_spec (bad_has_failed_mark s)⟩
  inj' a b h := Subtype.ext (congrArg Sigma.fst h)

/-- The original union bound, applied to one actual family. -/
lemma bad_card_le_failed {C : Type} (F : PrefixFamily C) (g : ℕ) :
    Fintype.card (BadCandidate F g) ≤ Fintype.card (FailedMark F g) :=
  Fintype.card_le_of_embedding (badIntoFailed F g)

/-- Natural subtraction is the separately clipped integer difference. -/
def familyLowerBound {C : Type} (F : PrefixFamily C) (g : ℕ) : ℕ :=
  Fintype.card (Candidate F g) - Fintype.card (FailedMark F g)

lemma familyLowerBound_eq_clip {C : Type} (F : PrefixFamily C) (g : ℕ) :
    (familyLowerBound F g : ℤ) =
      max 0 ((Fintype.card (Candidate F g) : ℤ) - Fintype.card (FailedMark F g)) := by
  unfold familyLowerBound
  omega

lemma familyLowerBound_le_good {C : Type} (F : PrefixFamily C) (g : ℕ) :
    familyLowerBound F g ≤ Fintype.card (GoodCandidate F g) := by
  have hbad := bad_card_le_failed F g
  have hc := Fintype.card_subtype_compl
    (fun s : Candidate F g => FullyWitnessed (F.decode s.val.1) s.val.2)
  have hg := Fintype.card_subtype_le
    (fun s : Candidate F g => FullyWitnessed (F.decode s.val.1) s.val.2)
  change Fintype.card (BadCandidate F g) = Fintype.card (Candidate F g) -
    Fintype.card (GoodCandidate F g) at hc
  unfold familyLowerBound
  omega

def goodIntoWitnessed {C : Type} (F : PrefixFamily C) (g : ℕ) :
    GoodCandidate F g ↪ WitnessedBase g where
  toFun s := ⟨s.val.data, s.val.data_weight, s.val.data_depth,
    baseData_carryWitnessed _ _ _ _ s.property⟩
  inj' a b h := Subtype.ext (Candidate.data_injective (congrArg Subtype.val h))

lemma safe_early_data_disjoint {g : ℕ} (s : SafeBaseAt g) (e : EarlyBaseAt g) :
    s.data ≠ e.data := by
  intro h
  have hh := baseData_injective (safe_admissible _) (early_admissible _)
    s.property.1 e.property.1 (safe_terminal _) (early_terminal _) h
  exact safe_early_disjoint s.val.1 e.val.1 hh.1

lemma good_safe_early_disjoint {g : ℕ} (s : GoodCandidate safeFamily g)
    (e : GoodCandidate earlyFamily g) :
    goodIntoWitnessed safeFamily g s ≠ goodIntoWitnessed earlyFamily g e := by
  intro h
  exact safe_early_data_disjoint s.val e.val (congrArg Subtype.val h)

/-- The two original, separately clipped lower bounds can be added because
the actual base families are proved disjoint. -/
def nonbinaryLowerBound (g : ℕ) : ℕ :=
  familyLowerBound safeFamily g + familyLowerBound earlyFamily g

def goodJointEmbedding (g : ℕ) :
    GoodCandidate safeFamily g ⊕ GoodCandidate earlyFamily g ↪ WitnessedBase g :=
  Allocation.joinEmbeddings (goodIntoWitnessed safeFamily g) (goodIntoWitnessed earlyFamily g)
    (fun e s h => good_safe_early_disjoint s e h.symm)

lemma nonbinaryLowerBound_le_good_sum (g : ℕ) :
    nonbinaryLowerBound g ≤
      Fintype.card (GoodCandidate safeFamily g ⊕ GoodCandidate earlyFamily g) := by
  rw [Fintype.card_sum]
  exact Nat.add_le_add (familyLowerBound_le_good safeFamily g)
    (familyLowerBound_le_good earlyFamily g)

#print axioms bad_card_le_failed
#print axioms familyLowerBound_eq_clip
#print axioms goodJointEmbedding
end SubmittedGenus.OriginalReservoir
