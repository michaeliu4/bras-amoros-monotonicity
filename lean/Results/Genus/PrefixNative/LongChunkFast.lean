import Results.Genus.PrefixNative.LongChunk
import Results.Genus.PrefixNative.LongFast
import Results.Genus.PrefixNative.Assembly

/-! Block-table versions of the long chunk Booleans (same statements as `LongChunk`,
faster evaluation).  Soundness theorems have only the Boolean as hypothesis. -/
namespace SubmittedGenus.CapFourMass.Interval.PrefixNativeLong
open ActualComponent ExecutableModes RationalTables ModeSignatures MatrixTables
open CompactOriginalBatchV3 IndexedModePrefix
open SubmittedGenus.CapFourMass.ExecutableModes.PrefixNative
open SourceSyntax Expr
open scoped BigOperators

/-- Largest `full n` strong-run length occurring in the family. -/
def maxStrong (F : CompactModeFamily) : ℕ :=
  let sr : Option StrongRun → ℕ := fun o => match o with | some (.full n _) => n | _ => 0
  F.foldl (fun acc B => B.programs.foldl (fun acc pr =>
    match pr with
    | .path (.pure s) => max acc (sr s)
    | .path (.carried pre _ _ _ bs post) =>
        bs.foldl (fun a b => max a (match b.run.strong with | .full n _ => n | _ => 0))
          (max acc (max (sr pre) (sr post)))
    | .cycle _ b bs => (b::bs).foldl (fun a b => max a (match b.run.strong with | .full n _ => n | _ => 0)) acc
    | .isolated => acc) acc) 0

structure Prepared (F : CompactModeFamily) where
  C : CachedContext
  es : Array Entry
  keys : Array (Array ℕ)

def prepare (F : CompactModeFamily) (hF : F.check = true) : Option (Prepared F) :=
  if maxStrong F ≤ 400 then
    let codes := blockCodes F
    let t : BlockTable := mkBlockTable RationalStrongPowers.context (codes.foldl max 0 + 1) codes
    if hv : BlockTable.validCheck RationalStrongPowers.context t = true then
      let hv' := BlockTable.validCheck_sound hv
      let st := genState F hF
      some ⟨ctxT t hv', st.sigs.map (entryOfSigT t hv'), st.keys⟩
    else none
  else none

/-! ### pure -/

def pureChunkCheckFWith (fin : Box → Bool) (a b : ℕ) : Bool :=
  match hden : pureDenOpt with
  | none => false
  | some den =>
    if hpos : 0 < den.lo then
      let F : CompactModeFamily := familyOf (pureTriples a b)
      if hF : F.check = true then
        if hs : 0 < F.size then
          match prepare F hF with
          | none => false
          | some P =>
            let entries : Fin P.es.size → Entry := fun i => P.es[i]
            let A : NumericPacket := ⟨P.keys,
              (Array.range F.size).map (fun i => (seriesBoxes P.C F P.es P.keys i).1),
              (Array.range F.size).map (fun _ => none)⟩
            let lookup : NumericPacket.Lookup F := fun p r n => ⟨min (purePos a p r n) (F.size-1), by omega⟩
            let bb : BaseBoxes := fun r d n =>
              ((A.pure[purePos a (r+d) r n]?).getD none).getD (point 0)
            A.check F hF P.C entries && A.pureCoverageCheck F lookup bb a b &&
              fin (pureChunk bb den a b)
        else false
      else false
    else false

theorem pureChunkCheckFWith_sound {fin : Box → Bool} {a b : ℕ}
    (h : pureChunkCheckFWith fin a b = true) :
    ∃ bx, Contains bx (∑ p ∈ Finset.Ico a b, pureSourceRow p) ∧ fin bx = true := by
  unfold pureChunkCheckFWith at h
  split at h
  · contradiction
  · rename_i den hden
    split at h
    · rename_i hpos
      dsimp only at h
      split at h
      · rename_i hF
        split at h
        · rename_i hs
          split at h
          · contradiction
          · rename_i P hP
            simp only [Bool.and_eq_true] at h
            obtain ⟨⟨hc, hcov⟩, hfin⟩ := h
            exact ⟨_, NumericPacket.pure_chunk_contains hc hcov (pureDen_contains hden) hpos, hfin⟩
        · contradiction
      · contradiction
    · contradiction

def pureChunkCheckF (a b : ℕ) (box : Box) : Bool :=
  pureChunkCheckFWith (fun bx => decide (bx = box)) a b

theorem pureChunkCheckF_sound {a b : ℕ} {box : Box} (h : pureChunkCheckF a b box = true) :
    Contains box (∑ p ∈ Finset.Ico a b, pureSourceRow p) := by
  obtain ⟨bx, hc, hf⟩ := pureChunkCheckFWith_sound h
  rw [← of_decide_eq_true hf]
  exact hc

def pureChunkCheckFLe (a b : ℕ) (N : ℤ) : Bool := pureChunkCheckFWith (PrefixNative.Assembly.leCheck N) a b

theorem pureChunkCheckFLe_sound {a b : ℕ} {N : ℤ} (h : pureChunkCheckFLe a b N = true) :
    (∑ p ∈ Finset.Ico a b, pureSourceRow p) ≤ (N:ℝ) / 72057594037927936 := by
  obtain ⟨bx, hc, hf⟩ := pureChunkCheckFWith_sound h
  exact PrefixNative.Assembly.le_of_contains_leCheck hc hf

/-! ### mixed -/

def mixedChunkCheckFWith (fin : Box → Bool) (a b : ℕ) : Bool :=
  if hden : mixedDenCheck b = true then
    let F : CompactModeFamily := familyOf (mixedTriples a b)
    if hF : F.check = true then
      if hs : 0 < F.size then
        match prepare F hF with
        | none => false
        | some P =>
          let entries : Fin P.es.size → Entry := fun i => P.es[i]
          let A : NumericPacket := ⟨P.keys,
            (Array.range F.size).map (fun _ => none),
            (Array.range F.size).map (fun i => (seriesBoxes P.C F P.es P.keys i).2)⟩
          let lookup : NumericPacket.Lookup F := fun p r n => ⟨min (mixedPos a p r n) (F.size-1), by omega⟩
          let bb : BaseBoxes := fun r d n =>
            ((A.mixed[mixedPos a (r+d) r n]?).getD none).getD (point 0)
          A.check F hF P.C entries && A.mixedCoverageCheck F lookup bb a b &&
            fin (mixedChunk bb mixedDen a b)
      else false
    else false
  else false

theorem mixedChunkCheckFWith_sound {fin : Box → Bool} {a b : ℕ}
    (h : mixedChunkCheckFWith fin a b = true) :
    ∃ bx, Contains bx (∑ p ∈ Finset.Ico a b, mixedSourceRow p) ∧ fin bx = true := by
  unfold mixedChunkCheckFWith at h
  split at h
  · rename_i hden
    dsimp only at h
    split at h
    · rename_i hF
      split at h
      · rename_i hs
        split at h
        · contradiction
        · rename_i P hP
          simp only [Bool.and_eq_true] at h
          obtain ⟨⟨hc, hcov⟩, hfin⟩ := h
          have hd : ∀ p ∈ Finset.Ico a b, ∀ r ∈ Finset.Ico 1 p,
              Contains (mixedDen (p-r)) (1-(normalizer*lam)^(2*(p-r))*rho^2) := by
            intro p hp r hr
            have hp' := Finset.mem_Ico.mp hp
            have hr' := Finset.mem_Ico.mp hr
            exact (mixedDenCheck_sound hden (d := p-r) (by omega) (by omega)).1
          have hpos : ∀ p ∈ Finset.Ico a b, ∀ r ∈ Finset.Ico 1 p, 0 < (mixedDen (p-r)).lo := by
            intro p hp r hr
            have hp' := Finset.mem_Ico.mp hp
            have hr' := Finset.mem_Ico.mp hr
            exact (mixedDenCheck_sound hden (d := p-r) (by omega) (by omega)).2
          exact ⟨_, NumericPacket.mixed_chunk_contains hc hcov hd hpos, hfin⟩
      · contradiction
    · contradiction
  · contradiction

def mixedChunkCheckF (a b : ℕ) (box : Box) : Bool :=
  mixedChunkCheckFWith (fun bx => decide (bx = box)) a b

theorem mixedChunkCheckF_sound {a b : ℕ} {box : Box} (h : mixedChunkCheckF a b box = true) :
    Contains box (∑ p ∈ Finset.Ico a b, mixedSourceRow p) := by
  obtain ⟨bx, hc, hf⟩ := mixedChunkCheckFWith_sound h
  rw [← of_decide_eq_true hf]
  exact hc

def mixedChunkCheckFLe (a b : ℕ) (N : ℤ) : Bool := mixedChunkCheckFWith (PrefixNative.Assembly.leCheck N) a b

theorem mixedChunkCheckFLe_sound {a b : ℕ} {N : ℤ} (h : mixedChunkCheckFLe a b N = true) :
    (∑ p ∈ Finset.Ico a b, mixedSourceRow p) ≤ (N:ℝ) / 72057594037927936 := by
  obtain ⟨bx, hc, hf⟩ := mixedChunkCheckFWith_sound h
  exact PrefixNative.Assembly.le_of_contains_leCheck hc hf

/-! ### box-returning versions -/

def pureChunkBoxOfF (a b : ℕ) : Option Box :=
  match pureDenOpt with
  | none => none
  | some den =>
    let F : CompactModeFamily := familyOf (pureTriples a b)
    if hF : F.check = true then
      match prepare F hF with
      | none => none
      | some P =>
        let pureOpts : Array (Option Box) :=
          (Array.range F.size).map (fun i => (seriesBoxes P.C F P.es P.keys i).1)
        let bb : BaseBoxes := fun r d n => ((pureOpts[purePos a (r+d) r n]?).getD none).getD (point 0)
        some (pureChunk bb den a b)
    else none

def mixedChunkBoxOfF (a b : ℕ) : Option Box :=
  let F : CompactModeFamily := familyOf (mixedTriples a b)
  if hF : F.check = true then
    match prepare F hF with
    | none => none
    | some P =>
      let mixedOpts : Array (Option Box) :=
        (Array.range F.size).map (fun i => (seriesBoxes P.C F P.es P.keys i).2)
      let bb : BaseBoxes := fun r d n => ((mixedOpts[mixedPos a (r+d) r n]?).getD none).getD (point 0)
      some (mixedChunk bb mixedDen a b)
  else none

end SubmittedGenus.CapFourMass.Interval.PrefixNativeLong
