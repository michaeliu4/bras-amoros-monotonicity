import Results.Genus.CapFiveMass.ComponentCounts
import Results.Genus.RawGraph.Incidence

/-!
# Complete free reflection-incidence accounting

Each free physical coordinate has two target incidences. An incidence is
either missing after pivot deletion, an ordinary-edge orientation, or a
self-pair. This is proved on the actual source graph before component counts
are substituted.
-/

noncomputable section
open scoped BigOperators
namespace SubmittedGenus.CapFiveMass
namespace MissingGeometry
open RawGraph RawGraph.SourceModel RawGraph.Topology RawGraph.Incidence ActualComponent

abbrev V (m r p : ℕ) := FreeVertex m r p

def Retained {m : ℕ} (r p : ℕ) (b : Bool) (i : V m r p) : Prop :=
  ∃ j : V m r p, TargetPair (target r p b) i.val j.val

def AllPair {m : ℕ} (r p : ℕ) (i j : V m r p) : Prop :=
  TargetPair r i.val j.val ∨ TargetPair p i.val j.val

def Loop {m : ℕ} (r p : ℕ) (i : V m r p) : Prop := StrongLoop r p i.val ∨ CarryLoop r p i.val

def retained (m r p : ℕ) : Finset (Bool × V m r p) := by classical exact Finset.univ.filter (fun bi => Retained r p bi.1 bi.2)
def missing (m r p : ℕ) : Finset (Bool × V m r p) := by classical exact Finset.univ.filter (fun bi => Missing r p bi.1 bi.2.val)
def allPairs (m r p : ℕ) : Finset (V m r p × V m r p) := by classical exact Finset.univ.filter (fun ij => AllPair r p ij.1 ij.2)
def ordinaryPairs (m r p : ℕ) : Finset (V m r p × V m r p) := by classical exact Finset.univ.filter (fun ij => (freeGraph m r p).Adj ij.1 ij.2)
def loops (m r p : ℕ) : Finset (V m r p) := by classical exact Finset.univ.filter (Loop r p)

lemma missing_iff_not_retained {m r p : ℕ} (b : Bool) (i : V m r p) :
    Missing r p b i.val ↔ ¬ Retained r p b i := by
  constructor
  · rintro h ⟨j, hj⟩
    exact h.2 j.val j.property hj
  · intro h
    refine ⟨i.property, ?_⟩
    intro j hj hp
    exact h ⟨⟨j, hj⟩, hp⟩

lemma missing_card (m r p : ℕ) : (missing m r p).card = (missingIncidences m r p).card := by
  classical
  apply Finset.card_bij (fun bi _ => (bi.1, bi.2.val))
  · intro bi hbi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hbi).2⟩
  · intro bi hbi cj hcj he
    have hb : bi.1 = cj.1 := congrArg (fun x : Bool × Fin (m - 1) => x.1) he
    have hv : bi.2.val = cj.2.val := congrArg (fun x : Bool × Fin (m - 1) => x.2) he
    exact Prod.ext hb (Subtype.ext hv)
  · intro bi hbi
    have hh := (Finset.mem_filter.mp hbi).2
    exact ⟨(bi.1, ⟨bi.2, hh.1⟩), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩, rfl⟩

lemma retained_missing_partition (m r p : ℕ) :
    (retained m r p).card + (missing m r p).card = 2 * Fintype.card (V m r p) := by
  classical
  have he : missing m r p = Finset.univ.filter (fun bi : Bool × V m r p => ¬ Retained r p bi.1 bi.2) := by
    ext bi
    simp only [missing, Finset.mem_filter, Finset.mem_univ, true_and, missing_iff_not_retained]
  rw [he]
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Bool × V m r p)))
    (fun bi => Retained r p bi.1 bi.2)
  simpa only [retained, Finset.card_univ, Fintype.card_prod, Fintype.card_bool] using h

lemma target_bool_unique {m r p a : ℕ} (hp : Parameters m r p a)
    {b c : Bool} {i j : Fin (m - 1)}
    (hb : TargetPair (target r p b) i j) (hc : TargetPair (target r p c) i j) : b = c := by
  cases b <;> cases c
  · rfl
  · exact (targets_disjoint hp i j ⟨hb, hc⟩).elim
  · exact (targets_disjoint hp i j ⟨hc, hb⟩).elim
  · rfl

lemma retained_card {m r p a : ℕ} (hp : Parameters m r p a) :
    (retained m r p).card = (allPairs m r p).card := by
  classical
  let f (bi : Bool × V m r p) (h : bi ∈ retained m r p) :=
    (bi.2, Classical.choose ((Finset.mem_filter.mp h).2))
  have hf (bi : Bool × V m r p) (h : bi ∈ retained m r p) :
      TargetPair (target r p bi.1) bi.2.val (f bi h).2.val :=
    Classical.choose_spec ((Finset.mem_filter.mp h).2)
  apply Finset.card_bij f
  · intro bi hbi
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have hh := hf bi hbi
    cases hb : bi.1
    · exact Or.inl (by simpa [target, hb] using hh)
    · exact Or.inr (by simpa [target, hb] using hh)
  · intro bi hbi cj hcj he
    have hi : bi.2 = cj.2 := congrArg Prod.fst he
    have hj : (f bi hbi).2 = (f cj hcj).2 := congrArg Prod.snd he
    have hb := hf bi hbi
    rw [hi, hj] at hb
    exact Prod.ext (target_bool_unique hp hb (hf cj hcj)) hi
  · rintro ⟨i, j⟩ hij
    have hh := (Finset.mem_filter.mp hij).2
    have hpre (b : Bool) (hb : TargetPair (target r p b) i.val j.val) :
        ∃ bi, ∃ hbi : bi ∈ retained m r p, f bi hbi = (i, j) := by
      have hbi : (b, i) ∈ retained m r p := Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, hb⟩
      refine ⟨(b, i), hbi, Prod.ext rfl ?_⟩
      exact Subtype.ext (target_partner_unique (hf (b, i) hbi) hb)
    rcases hh with hr | hp
    · exact hpre false hr
    · exact hpre true hp

lemma allPair_self_iff {m r p : ℕ} (i : V m r p) : AllPair r p i i ↔ Loop r p i := by
  unfold AllPair Loop TargetPair StrongLoop CarryLoop
  omega

lemma allPair_offdiag_iff {m r p : ℕ} (i j : V m r p) (hne : i ≠ j) :
    AllPair r p i j ↔ (freeGraph m r p).Adj i j := by
  constructor
  · intro h
    exact ⟨fun he => hne (Subtype.ext he), i.property, j.property, h⟩
  · intro h
    exact h.2.2.2

lemma allPairs_card_split (m r p : ℕ) :
    (allPairs m r p).card = (ordinaryPairs m r p).card + (loops m r p).card := by
  classical
  let diag := Finset.univ.filter (fun ij : V m r p × V m r p => ij.1 = ij.2 ∧ Loop r p ij.1)
  have hd : diag.card = (loops m r p).card := by
    apply Finset.card_bij (fun ij _ => ij.1)
    · intro ij hij
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hij).2.2⟩
    · intro ij hij kl hkl he
      have hij' := (Finset.mem_filter.mp hij).2.1
      have hkl' := (Finset.mem_filter.mp hkl).2.1
      exact Prod.ext he (hij'.symm.trans (he.trans hkl'))
    · intro i hi
      exact ⟨(i, i), Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, (Finset.mem_filter.mp hi).2⟩, rfl⟩
  have hpoint (ij : V m r p × V m r p) :
      (if AllPair r p ij.1 ij.2 then 1 else 0 : ℕ) =
        (if (freeGraph m r p).Adj ij.1 ij.2 then 1 else 0) +
        (if ij.1 = ij.2 ∧ Loop r p ij.1 then 1 else 0) := by
    by_cases he : ij.1 = ij.2
    · simp [he, allPair_self_iff]
    · simp only [allPair_offdiag_iff _ _ he, he, false_and, if_false, add_zero]
  have hs := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun ij _ => hpoint ij)
  simp only [Finset.sum_add_distrib, Finset.sum_boole] at hs
  change (allPairs m r p).card = (ordinaryPairs m r p).card + diag.card at hs
  rw [hd] at hs
  exact hs

/-- Complete two-target accounting on actual free vertices. Loops contribute
one target incidence, and each ordinary edge contributes its two orientations. -/
lemma source_incidence_partition {m r p a : ℕ} (hp : Parameters m r p a) :
    (missingIncidences m r p).card + (ordinaryPairs m r p).card + (loops m r p).card =
      2 * Fintype.card (V m r p) := by
  have h := retained_missing_partition m r p
  rw [missing_card, retained_card hp, allPairs_card_split] at h
  omega

end MissingGeometry
end SubmittedGenus.CapFiveMass
