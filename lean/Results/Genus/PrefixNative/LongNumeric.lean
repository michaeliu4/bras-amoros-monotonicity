import Results.Genus.PrefixNative.LongGen
import Results.Genus.CapFourMass.IntervalRationalStrongPowers
import Results.Genus.CapFourMass.IntervalSourceSyntax

/-! Strict numeric layer for the native long-source check.

* `strictCtx` : a `CachedContext` whose block chain is materialised eagerly
  (the lazy `Fin → Fin → Box` chain of `CachedContext.direct` is exponential in compiled code).
* entries are `certify`-d with `rfl`, so they are valid by construction.
* the generator hash-conses ordered component signatures and builds all keys. -/
namespace SubmittedGenus.CapFourMass.Interval.PrefixNativeLong
open ActualComponent ExecutableModes RationalTables ModeSignatures MatrixTables
open CompactOriginalBatchV3 IndexedModePrefix
open SubmittedGenus.CapFourMass.ExecutableModes.PrefixNative

/-! ### strict 2x2 matrices -/

structure M2 where
  a : Box
  b : Box
  c : Box
  d : Box

def M2.ofBoxes (A : Boxes 2) : M2 := ⟨A 0 0, A 0 1, A 1 0, A 1 1⟩

def M2.toBoxes (M : M2) : Boxes 2 := fun i j =>
  if i = 0 then (if j = 0 then M.a else M.b) else (if j = 0 then M.c else M.d)

def M2.prod (X Y : M2) : M2 :=
  ⟨add (mul X.a Y.a) (add (mul X.b Y.c) (point 0)),
   add (mul X.a Y.b) (add (mul X.b Y.d) (point 0)),
   add (mul X.c Y.a) (add (mul X.d Y.c) (point 0)),
   add (mul X.c Y.b) (add (mul X.d Y.d) (point 0))⟩

theorem M2.toBoxes_ofBoxes (A : Boxes 2) : (M2.ofBoxes A).toBoxes = A := by
  funext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem M2.toBoxes_prod (X Y : M2) : (X.prod Y).toBoxes = product X.toBoxes Y.toBoxes := by
  funext i j
  fin_cases i <;> fin_cases j <;> rfl

def strictBlocks (C : Context) : List CoupledRun → M2
  | [] => M2.ofBoxes (identity 2)
  | b::bs => M2.prod (M2.ofBoxes (matrixAbsolute (C.block b))) (strictBlocks C bs)

theorem strictBlocks_eq (C : Context) (bs : List CoupledRun) :
    (strictBlocks C bs).toBoxes = listProduct (bs.map (fun b => matrixAbsolute (C.block b))) := by
  induction bs with
  | nil => exact M2.toBoxes_ofBoxes _
  | cons b bs ih =>
    simp only [strictBlocks, M2.toBoxes_prod, M2.toBoxes_ofBoxes, ih, List.map_cons, listProduct]

def strictCtx (C : Context) : CachedContext where
  toContext := C
  chain := fun bs => (strictBlocks C bs).toBoxes
  chain_contains := fun bs => by
    rw [strictBlocks_eq]
    exact (CachedContext.direct C).chain_contains bs

/-- The context used by all native checks. -/
def ctx : CachedContext := strictCtx RationalStrongPowers.context

/-! ### signature keys and entries -/

def encStrong : StrongRun → List ℕ
  | .full n _ => [1, n]
  | .restricted => [0]

def encOpt : Option StrongRun → List ℕ
  | none => [2]
  | some s => 3 :: encStrong s

def encBlock (b : TaggedBlock Unit) : List ℕ := encStrong b.run.strong ++ [b.run.carryLength]

def encProgram : ModeProgram Unit → List ℕ
  | .path (.pure s) => 0 :: encOpt s
  | .path (.carried pre _ n _ bs post) =>
      [1] ++ encOpt pre ++ [n, bs.length] ++ bs.flatMap encBlock ++ encOpt post
  | .cycle _ b bs => [4, bs.length + 1] ++ (b::bs).flatMap encBlock
  | .isolated => [5]

def encMask (m : Mask) : List ℕ := (List.finRange 4).map fun i => if m i then 1 else 0

def sigKey (s : Signature) : List ℕ := encProgram s.program ++ [9] ++ encMask s.leftMask ++ encMask s.rightMask

def dummySig : Signature := ⟨.isolated, fun _ => false, fun _ => false⟩

/-- Always-valid entry: the boxes are by definition the context evaluations. -/
def entryOfSig (C : CachedContext) (s : Signature) : Entry :=
  certify C s (C.pure s.program (maskBoxes s.leftMask) (maskBoxes s.rightMask))
    (C.absolute s.program (maskBoxes s.leftMask) (maskBoxes s.rightMask)) rfl rfl

structure GenState where
  index : Std.HashMap (List ℕ) ℕ := {}
  sigs : Array Signature := #[]
  keys : Array (Array ℕ) := #[]

/-- Register all components of base `i` of an accepted family. -/
def GenState.addBase (st : GenState) (F : CompactModeFamily) (hF : F.check = true)
    (i : Fin F.size) : GenState :=
  let L := F[i].acceptedLayout (F.accepted hF i)
  let (st, ks) := (List.finRange L.count).foldl (fun (acc : GenState × Array ℕ) c =>
    let (st, ks) := acc
    let s := physicalSignature L F[i].program c
    let key := sigKey s
    match st.index[key]? with
    | some idx => (st, ks.push idx)
    | none =>
      let idx := st.sigs.size
      ({ st with index := st.index.insert key idx, sigs := st.sigs.push s }, ks.push idx))
    (st, #[])
  { st with keys := st.keys.push ks }

def genState (F : CompactModeFamily) (hF : F.check = true) : GenState :=
  (List.finRange F.size).foldl (fun st i => st.addBase F hF i) {}

/-- Right-nested product of the component boxes (as `prodBoxes`). -/
def prodList (bs : List Box) : Box := bs.foldr (fun b acc => mul b acc) (point 1)

def seriesBoxes (C : CachedContext) (F : CompactModeFamily) (entries : Array Entry)
    (keys : Array (Array ℕ)) (i : ℕ) : Option Box × Option Box :=
  match F[i]?, keys[i]? with
  | some B, some ks =>
    let es := ks.toList.map fun k => entries[k]?.getD (entryOfSig C dummySig)
    let pure := mul C.pivot (prodList (es.map (·.pureBox)))
    let abs := mul C.pivot (prodList (es.map (·.absoluteBox)))
    (normalized B.r B.d B.n pure, normalized B.r B.d B.n (zeroLower (sub abs pure)))
  | _, _ => (none, none)

end SubmittedGenus.CapFourMass.Interval.PrefixNativeLong
