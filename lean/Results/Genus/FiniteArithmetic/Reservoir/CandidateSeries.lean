import Results.Genus.FiniteArithmetic.Reservoir.Presentations
import Results.Genus.FiniteArithmetic.Reservoir.BinaryLength
import Results.Genus.Injection.ReservoirSources.Candidates

namespace SubmittedGenus.FiniteArithmetic.Reservoir

open PowerSeries
open scoped BigOperators
set_option synthInstance.maxSize 1000

abbrev binaryAlphabet := finiteAlphabet (fun a : Fin 2 => a.val + 1) (by intro a; omega)
abbrev BinaryTailSource := LocallyFinite.Words binaryAlphabet
abbrev BinaryWord := {w : List ℕ // OriginalReservoir.BinaryTail w}

def binaryTailWord {g : ℕ} (a : BinaryTailSource g) : BinaryWord :=
  ⟨a.val.map (fun a => a.val+1), by
    intro x hx
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hx
    have := b.isLt
    omega⟩

theorem binaryTailWord_weight {g : ℕ} (a : BinaryTailSource g) :
    (binaryTailWord a).val.sum = g := a.property

theorem binaryTailWord_injective (g : ℕ) : Function.Injective (@binaryTailWord g) := by
  intro a b h
  apply Subtype.ext
  apply (List.map_injective_iff.mpr (show Function.Injective (fun a : Fin 2 => a.val+1) from by
    intro a b h; apply Fin.ext; dsimp at h; omega))
  exact congrArg Subtype.val h

theorem exists_binaryTailSource (w : BinaryWord) :
    ∃ a : BinaryTailSource w.val.sum, binaryTailWord a = w := by
  obtain ⟨a,ha⟩ := exists_binaryLengthSource w.val w.property
  let l := List.ofFn a.val
  have hl : l.map (fun x : Fin 2 => x.val+1) = w.val := by
    simpa only [l, List.map_ofFn, binaryLengthWord, Function.comp_def] using ha
  refine ⟨⟨l, ?_⟩, Subtype.ext hl⟩
  change (l.map (fun x : Fin 2 => x.val+1)).sum = w.val.sum
  rw [hl]

noncomputable def binaryPresentation : Presentation BinaryTailSource BinaryWord :=
  presentationOfDecode (fun w => w.val.sum) binaryTailWord binaryTailWord_weight
    binaryTailWord_injective exists_binaryTailSource

noncomputable def binaryTailSeries : PowerSeries ℤ := Graded.series BinaryTailSource

theorem binaryTailSeries_identity : (1-c)*binaryTailSeries = 1 := by
  have h := LocallyFinite.wordSeries_identity binaryAlphabet
  have hc : LocallyFinite.letterSeries binaryAlphabet = c := by
    rw [finiteAlphabet_letters]
    simp only [Fin.sum_univ_succ]
    norm_num [c]
  simpa only [hc, LocallyFinite.wordSeries, LocallyFinite.wordCount, binaryTailSeries, Graded.series] using h

abbrev SafeCandidateSource := Graded.Shift 1 (Graded.Product SafeSource BinaryTailSource)
abbrev EarlyCandidateSource := Graded.Shift 1 (Graded.Product EarlySource BinaryTailSource)

noncomputable def candidateEquiv {C : Type} {F : ℕ → Type}
    (p : Presentation F C) (family : OriginalReservoir.PrefixFamily C)
    (h : p.weight = family.weight) (g : ℕ) :
    Graded.Shift 1 (Graded.Product F BinaryTailSource) g ≃ OriginalReservoir.Candidate family g :=
  ((p.product binaryPresentation).shift 1).equiv g |>.trans {
    toFun := fun a => ⟨(a.val.1,a.val.2.val), a.val.2.property, by
      have ha := a.property
      change p.weight a.val.1 + a.val.2.val.sum + 1 = g at ha
      simpa only [h] using ha⟩
    invFun := fun a => ⟨(a.val.1,⟨a.val.2,a.property.1⟩), by
      change p.weight a.val.1 + a.val.2.sum + 1 = g
      simpa only [h] using a.property.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

noncomputable def safeCandidateEquiv (g : ℕ) :
    SafeCandidateSource g ≃ OriginalReservoir.SafeBaseAt g :=
  candidateEquiv safePresentation OriginalReservoir.safeFamily rfl g

noncomputable def earlyCandidateEquiv (g : ℕ) :
    EarlyCandidateSource g ≃ OriginalReservoir.EarlyBaseAt g :=
  candidateEquiv earlyPresentation OriginalReservoir.earlyFamily rfl g

noncomputable def safeCandidateSeries : PowerSeries ℤ := Graded.series SafeCandidateSource
noncomputable def earlyCandidateSeries : PowerSeries ℤ := Graded.series EarlyCandidateSource

/-- The original T_s counts the actual physical safe-family bases. -/
theorem safeCandidateSeries_coeff (g : ℕ) :
    coeff g safeCandidateSeries = (Fintype.card (OriginalReservoir.SafeBaseAt g) : ℤ) := by
  rw [safeCandidateSeries, Graded.coeff_series]
  exact congrArg (fun x : ℕ => (x : ℤ)) (Fintype.card_congr (safeCandidateEquiv g))

/-- The original T_e counts the actual physical early-one-family bases. -/
theorem earlyCandidateSeries_coeff (g : ℕ) :
    coeff g earlyCandidateSeries = (Fintype.card (OriginalReservoir.EarlyBaseAt g) : ℤ) := by
  rw [earlyCandidateSeries, Graded.coeff_series]
  exact congrArg (fun x : ℕ => (x : ℤ)) (Fintype.card_congr (earlyCandidateEquiv g))

theorem safeCandidateSeries_factorization :
    safeCandidateSeries = X * safeSeries * binaryTailSeries := by
  unfold safeCandidateSeries SafeCandidateSource
  rw [Graded.shift_series, Graded.product_series]
  change X^1 * (safeSeries * binaryTailSeries) = _
  ring

theorem earlyCandidateSeries_factorization :
    earlyCandidateSeries = X * earlySeries * binaryTailSeries := by
  unfold earlyCandidateSeries EarlyCandidateSource
  rw [Graded.shift_series, Graded.product_series]
  change X^1 * (earlySeries * binaryTailSeries) = _
  ring

theorem safeCandidateSeries_identity : (1-c)*safeCandidateSeries = X*safeSeries := by
  rw [safeCandidateSeries_factorization]
  calc
    _ = X*safeSeries*((1-c)*binaryTailSeries) := by ring
    _ = _ := by rw [binaryTailSeries_identity, mul_one]

theorem earlyCandidateSeries_identity : (1-c)*earlyCandidateSeries = X*earlySeries := by
  rw [earlyCandidateSeries_factorization]
  calc
    _ = X*earlySeries*((1-c)*binaryTailSeries) := by ring
    _ = _ := by rw [binaryTailSeries_identity, mul_one]

#print axioms safeCandidateSeries_coeff
#print axioms earlyCandidateSeries_identity
end SubmittedGenus.FiniteArithmetic.Reservoir
