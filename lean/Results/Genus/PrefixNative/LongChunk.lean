import Results.Genus.PrefixNative.LongNumeric

/-! Chunk Booleans for the original pure (p ≤ 400, 2 bases per pair) and mixed
(p ≤ 100, 2(p-r) bases per pair) prefixes, with soundness theorems whose only
hypothesis is the Boolean (discharged by `native_decide` in the chunk files). -/
namespace SubmittedGenus.CapFourMass.Interval.PrefixNativeLong
open ActualComponent ExecutableModes RationalTables ModeSignatures MatrixTables
open CompactOriginalBatchV3 IndexedModePrefix
open SubmittedGenus.CapFourMass.ExecutableModes.PrefixNative
open SourceSyntax Expr
open scoped BigOperators

/-! ### denominators -/

def pureDenOpt : Option Box := (1-(w*l)^2 : Expr).eval inputs

theorem pureDen_contains {den : Box} (h : pureDenOpt = some den) :
    Contains den (1-(normalizer*lam)^2) := by
  have h2 := Expr.eval_sound _ inputs_contain h
  simpa only [Expr.real_sub, Expr.real_mul, Expr.real_pow, Expr.real_one, w_real, l_real] using h2

def mixedDenOpt (d : ℕ) : Option Box := (1-(w*l)^(2*d)*(0-m/l)^2 : Expr).eval inputs

theorem mixedDen_contains {d : ℕ} {den : Box} (h : mixedDenOpt d = some den) :
    Contains den (1-(normalizer*lam)^(2*d)*rho^2) := by
  have h2 := Expr.eval_sound _ inputs_contain h
  simpa only [Expr.real_sub, Expr.real_mul, Expr.real_div, Expr.real_pow, Expr.real_zero,
    Expr.real_one, w_real, l_real, m_real, rho, abs_of_neg mu_neg, neg_div, zero_sub] using h2

def mixedDen (d : ℕ) : Box := (mixedDenOpt d).getD (point 0)

/-- Every denominator d in [1, bound) evaluates to a box with positive lower end. -/
def mixedDenCheck (bound : ℕ) : Bool :=
  (List.range bound).all fun d =>
    d == 0 || (match mixedDenOpt d with | some bx => decide (0 < bx.lo) | none => false)

theorem mixedDenCheck_sound {bound : ℕ} (h : mixedDenCheck bound = true) {d : ℕ}
    (hd0 : 1 ≤ d) (hd : d < bound) :
    Contains (mixedDen d) (1-(normalizer*lam)^(2*d)*rho^2) ∧ 0 < (mixedDen d).lo := by
  have h1 := List.all_eq_true.mp h d (List.mem_range.mpr hd)
  have hne : (d == 0) = false := by
    cases hh : (d == 0) with
    | false => rfl
    | true => exact absurd (beq_iff_eq.mp hh) (by omega)
  rw [hne, Bool.false_or] at h1
  unfold mixedDen
  cases hm : mixedDenOpt d with
  | none => rw [hm] at h1; exact absurd h1 (by simp)
  | some bx =>
    rw [hm] at h1
    exact ⟨mixedDen_contains hm, of_decide_eq_true h1⟩

/-! ### index arithmetic -/

/-- Number of pure bases with pivot < p. -/
def pureBefore (p : ℕ) : ℕ := (p-1)*(p-2)

def purePos (a p r n : ℕ) : ℕ := pureBefore p - pureBefore a + (r-1)*2 + n

/-- Number of mixed bases with pivot < p. -/
def mixedBefore (p : ℕ) : ℕ := (p-2)*(p-1)*p/3

def mixedPos (a p r n : ℕ) : ℕ := mixedBefore p - mixedBefore a + (r-1)*(2*p-r) + n

def pureTriples (a b : ℕ) : Array (ℕ × ℕ × ℕ) := Id.run do
  let mut out := #[]
  for p in [a:b] do
    for r in [1:p] do
      for n in [0:2] do
        out := out.push (r, p-r, n)
  return out

def mixedTriples (a b : ℕ) : Array (ℕ × ℕ × ℕ) := Id.run do
  let mut out := #[]
  for p in [a:b] do
    for r in [1:p] do
      for n in [0:2*(p-r)] do
        out := out.push (r, p-r, n)
  return out

def familyOf (ts : Array (ℕ × ℕ × ℕ)) : CompactModeFamily :=
  ts.map fun t => genBase t.1 t.2.1 t.2.2

instance : Inhabited Box := ⟨point 0⟩

/-! ### the pure chunk Boolean -/

def pureChunkCheck (a b : ℕ) (box : Box) : Bool :=
  match hden : pureDenOpt with
  | none => false
  | some den =>
    if hpos : 0 < den.lo then
      let F : CompactModeFamily := familyOf (pureTriples a b)
      if hF : F.check = true then
        if hs : 0 < F.size then
          let st := genState F hF
          let es : Array Entry := st.sigs.map (entryOfSig ctx)
          let entries : Fin es.size → Entry := fun i => es[i]
          let A : NumericPacket := ⟨st.keys,
            (Array.range F.size).map (fun i => (seriesBoxes ctx F es st.keys i).1),
            (Array.range F.size).map (fun _ => none)⟩
          let lookup : NumericPacket.Lookup F := fun p r n => ⟨min (purePos a p r n) (F.size-1), by omega⟩
          let bb : BaseBoxes := fun r d n =>
            ((A.pure[purePos a (r+d) r n]?).getD none).getD (point 0)
          A.check F hF ctx entries && A.pureCoverageCheck F lookup bb a b &&
            decide (pureChunk bb den a b = box)
        else false
      else false
    else false

theorem pureChunkCheck_sound {a b : ℕ} {box : Box} (h : pureChunkCheck a b box = true) :
    Contains box (∑ p ∈ Finset.Ico a b, pureSourceRow p) := by
  unfold pureChunkCheck at h
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
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h
          obtain ⟨⟨hc, hcov⟩, hbox⟩ := h
          have := NumericPacket.pure_chunk_contains hc hcov (pureDen_contains hden) hpos
          rw [← hbox]
          exact this
        · contradiction
      · contradiction
    · contradiction

/-! ### the mixed chunk Boolean -/

def mixedChunkCheck (a b : ℕ) (box : Box) : Bool :=
  if hden : mixedDenCheck b = true then
    let F : CompactModeFamily := familyOf (mixedTriples a b)
    if hF : F.check = true then
      if hs : 0 < F.size then
        let st := genState F hF
        let es : Array Entry := st.sigs.map (entryOfSig ctx)
        let entries : Fin es.size → Entry := fun i => es[i]
        let A : NumericPacket := ⟨st.keys,
          (Array.range F.size).map (fun _ => none),
          (Array.range F.size).map (fun i => (seriesBoxes ctx F es st.keys i).2)⟩
        let lookup : NumericPacket.Lookup F := fun p r n => ⟨min (mixedPos a p r n) (F.size-1), by omega⟩
        let bb : BaseBoxes := fun r d n =>
          ((A.mixed[mixedPos a (r+d) r n]?).getD none).getD (point 0)
        A.check F hF ctx entries && A.mixedCoverageCheck F lookup bb a b &&
          decide (mixedChunk bb mixedDen a b = box)
      else false
    else false
  else false

theorem mixedChunkCheck_sound {a b : ℕ} {box : Box} (h : mixedChunkCheck a b box = true) :
    Contains box (∑ p ∈ Finset.Ico a b, mixedSourceRow p) := by
  unfold mixedChunkCheck at h
  split at h
  · rename_i hden
    dsimp only at h
    split at h
    · rename_i hF
      split at h
      · rename_i hs
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨hc, hcov⟩, hbox⟩ := h
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
        have := NumericPacket.mixed_chunk_contains hc hcov hd hpos
        rw [← hbox]
        exact this
      · contradiction
    · contradiction
  · contradiction

/-! ### box-returning versions (for oracle comparison and for producing chunk literals) -/

def pureChunkBoxOf (a b : ℕ) : Option Box :=
  match pureDenOpt with
  | none => none
  | some den =>
    let F : CompactModeFamily := familyOf (pureTriples a b)
    if hF : F.check = true then
      let st := genState F hF
      let es : Array Entry := st.sigs.map (entryOfSig ctx)
      let pureOpts : Array (Option Box) :=
        (Array.range F.size).map (fun i => (seriesBoxes ctx F es st.keys i).1)
      let bb : BaseBoxes := fun r d n => ((pureOpts[purePos a (r+d) r n]?).getD none).getD (point 0)
      some (pureChunk bb den a b)
    else none

def mixedChunkBoxOf (a b : ℕ) : Option Box :=
  let F : CompactModeFamily := familyOf (mixedTriples a b)
  if hF : F.check = true then
    let st := genState F hF
    let es : Array Entry := st.sigs.map (entryOfSig ctx)
    let mixedOpts : Array (Option Box) :=
      (Array.range F.size).map (fun i => (seriesBoxes ctx F es st.keys i).2)
    let bb : BaseBoxes := fun r d n => ((mixedOpts[mixedPos a (r+d) r n]?).getD none).getD (point 0)
    some (mixedChunk bb mixedDen a b)
  else none

end SubmittedGenus.CapFourMass.Interval.PrefixNativeLong
