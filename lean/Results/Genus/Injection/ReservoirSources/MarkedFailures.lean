import Results.Genus.Injection.ReservoirSources.FailureTails
import Mathlib.Data.Subtype

noncomputable section
namespace SubmittedGenus.OriginalReservoir
open FiniteArithmetic FiniteArithmetic.Reservoir
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Literal prefix codes of an exact weight, independently of tail marks. -/
abbrev PrefixAt {C : Type} (F : PrefixFamily C) (n : ℕ) := {c : C // F.weight c=n}

def prefixIntoCandidate {C : Type} (F : PrefixFamily C) (n : ℕ) :
    PrefixAt F n ↪ Candidate F (n+1) where
  toFun c := ⟨(c.val,[]),by simp [BinaryTail],by simpa using c.property⟩
  inj' a b h := Subtype.ext (congrArg (fun x : Candidate F (n+1) => x.val.1) h)

instance {C : Type} (F : PrefixFamily C) (n : ℕ) : Finite (PrefixAt F n) :=
  Finite.of_injective (prefixIntoCandidate F n) (prefixIntoCandidate F n).injective

instance {C : Type} (F : PrefixFamily C) (n : ℕ) : Fintype (PrefixAt F n) := Fintype.ofFinite _

/-- An actual occurrence of `3`, retaining its physical prefix position.
Several occurrences in one prefix remain distinct objects. -/
abbrev PrefixOccurrence {C : Type} (F : PrefixFamily C) (n : ℕ) :=
  Σ c : PrefixAt F n, {i : Fin (F.decode c.val).length // (F.decode c.val)[i.val]=3}

def PrefixOccurrence.distance {C : Type} {F : PrefixFamily C} {n : ℕ}
    (p : PrefixOccurrence F n) : ℕ := (F.decode p.1.val).length-1-p.2.val.val

/-- Exact convolution of a physical marked prefix and an actual failing tail;
the outer index handles the original extra source-genus weight of one. -/
abbrev MarkedFailureSource {C : Type} (F : PrefixFamily C) (g : ℕ) :=
  Σ n : Fin g, Σ p : PrefixOccurrence F n.val, FailureTailSource p.distance (g-1-n.val)

def markedFailureToActual {C : Type} (F : PrefixFamily C) (g : ℕ)
    (s : MarkedFailureSource F g) : FailedMark F g :=
  ⟨⟨(s.2.1.1.val,failureTailWord s.2.2), failureTailWord_binary s.2.2,by
    rw [s.2.1.1.property,failureTailWord_weight]
    have := s.1.isLt
    omega⟩,
    ⟨s.2.1.2.val,s.2.1.2.property,failureTailWord_failed s.2.2⟩⟩

lemma markedFailureToActual_injective {C : Type} (F : PrefixFamily C) (g : ℕ) :
    Function.Injective (markedFailureToActual F g) := by
  rintro ⟨n,⟨c,i⟩,a⟩ ⟨m,⟨d,j⟩,b⟩ h
  have hc := congrArg (fun x : FailedMark F g => x.1.val.1) h
  have ht := congrArg (fun x : FailedMark F g => x.1.val.2) h
  have hi := congrArg (fun x : FailedMark F g => x.2.val.val) h
  change c.val=d.val at hc
  have hn : n=m := Fin.ext (by rw [←c.property,←d.property,hc])
  subst m
  have hcd : c=d := Subtype.ext hc
  subst d
  have hij : i=j := Subtype.ext (Fin.ext hi)
  subst j
  have hab : a=b := failureTailWord_injective _ _ ht
  subst b
  rfl

lemma markedFailureToActual_surjective {C : Type} (F : PrefixFamily C) (g : ℕ) :
    Function.Surjective (markedFailureToActual F g) := by
  rintro ⟨s,i,hi,hfailed⟩
  let n : Fin g := ⟨F.weight s.val.1,by have := s.property.2; omega⟩
  let p : PrefixOccurrence F n.val := ⟨⟨s.val.1,rfl⟩,⟨i,hi⟩⟩
  have hs : s.val.2.sum=g-1-n.val := by have := s.property.2; dsimp [n]; omega
  let t : FailedTail p.distance (g-1-n.val) := ⟨s.val.2,s.property.1,hs,hfailed⟩
  obtain ⟨a,ha⟩ := exists_failureTailSource t
  refine ⟨⟨n,p,a⟩,?_⟩
  have he : (markedFailureToActual F g ⟨n,p,a⟩).1=s := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact ha
  apply Sigma.ext he
  apply (Subtype.heq_iff_coe_eq (by
    intro x
    simp only [markedFailureToActual,p,ha,t])).mpr
  rfl

/-- Actual marked-failure populations, with no erased marks and no assumed
rational series identity. -/
def markedFailureEquiv {C : Type} (F : PrefixFamily C) (g : ℕ) :
    MarkedFailureSource F g ≃ FailedMark F g :=
  Equiv.ofBijective (markedFailureToActual F g)
    ⟨markedFailureToActual_injective F g,markedFailureToActual_surjective F g⟩

lemma failedMark_card_convolution {C : Type} (F : PrefixFamily C) (g : ℕ) :
    Fintype.card (FailedMark F g) =
      ∑ n : Fin g, ∑ p : PrefixOccurrence F n.val,
        Fintype.card (FailureTailSource p.distance (g-1-n.val)) := by
  rw [←Fintype.card_congr (markedFailureEquiv F g)]
  simp only [MarkedFailureSource,Fintype.card_sigma]

lemma failedMark_coeff_convolution {C : Type} (F : PrefixFamily C) (g : ℕ) :
    (Fintype.card (FailedMark F g) : ℤ) =
      ∑ n : Fin g, ∑ p : PrefixOccurrence F n.val,
        PowerSeries.coeff (g-1-n.val) (failureTailSeries p.distance) := by
  rw [failedMark_card_convolution]
  simp only [Nat.cast_sum,failureTailSeries,Graded.coeff_series]

#print axioms markedFailureEquiv
#print axioms failedMark_card_convolution
#print axioms failedMark_coeff_convolution
end SubmittedGenus.OriginalReservoir
