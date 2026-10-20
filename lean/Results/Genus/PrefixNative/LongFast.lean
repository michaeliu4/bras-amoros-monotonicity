import Results.Genus.PrefixNative.LongNumeric

/-! Block-table acceleration of the long-source entries.

`Context.block` (a 2x2 matrix of boxes, ~176 interval multiplications) is the dominant cost of
evaluating a component.  Distinct (strong run, carry length) pairs are few, so a table indexed by
an injective code stores the blocks once.  The table is *checked* (`TableValid`: every stored
block equals the direct evaluation), so lookups are provably equal to `Context.block`. -/
namespace SubmittedGenus.CapFourMass.Interval.PrefixNativeLong
open ActualComponent ExecutableModes RationalTables ModeSignatures MatrixTables
open CompactOriginalBatchV3 IndexedModePrefix
open SubmittedGenus.CapFourMass.ExecutableModes.PrefixNative

deriving instance DecidableEq for M2

/-- Injective code of a coupled run. -/
def encodeRun (b : CoupledRun) : ℕ :=
  match b.strong with
  | .restricted => 2 * b.carryLength
  | .full n _ => 2 * Nat.pair n b.carryLength + 1

def dfltRun : CoupledRun := ⟨.restricted, 1, le_refl 1⟩

def decodeRun (code : ℕ) : CoupledRun :=
  if code % 2 = 0 then
    if h : 1 ≤ code / 2 then ⟨.restricted, code / 2, h⟩ else dfltRun
  else
    if h1 : 1 ≤ (Nat.unpair (code / 2)).1 then
      if h2 : 1 ≤ (Nat.unpair (code / 2)).2 then
        ⟨.full (Nat.unpair (code / 2)).1 h1, (Nat.unpair (code / 2)).2, h2⟩
      else dfltRun
    else dfltRun

theorem decode_encode (b : CoupledRun) : decodeRun (encodeRun b) = b := by
  obtain ⟨s, cn, hcn⟩ := b
  cases s with
  | restricted =>
    simp only [encodeRun, decodeRun]
    have h1 : (2 * cn) % 2 = 0 := by omega
    have h2 : 2 * cn / 2 = cn := by omega
    simp only [h1, h2, if_true, dif_pos hcn]
  | full n hn =>
    simp only [encodeRun, decodeRun]
    have h1 : ¬ ((2 * Nat.pair n cn + 1) % 2 = 0) := by omega
    have h2 : (2 * Nat.pair n cn + 1) / 2 = Nat.pair n cn := by omega
    simp only [h1, h2, if_false, Nat.unpair_pair, dif_pos hn, dif_pos hcn]

/-- Signed block as a strict 2x2 matrix. -/
def blockM2 (C : Context) (b : CoupledRun) : M2 := M2.ofBoxes (C.block b)

def absM2 (M : M2) : M2 := ⟨absolute M.a, absolute M.b, absolute M.c, absolute M.d⟩

theorem absM2_ofBoxes (A : Boxes 2) : (absM2 (M2.ofBoxes A)).toBoxes = matrixAbsolute A := by
  funext i j
  fin_cases i <;> fin_cases j <;> rfl

abbrev BlockTable := Array (Option M2)

def BlockTable.lookup (C : Context) (t : BlockTable) (b : CoupledRun) : M2 :=
  match t[encodeRun b]? with
  | some (some v) => v
  | _ => blockM2 C b

def BlockTable.Valid (C : Context) (t : BlockTable) : Prop :=
  ∀ i : Fin t.size, ∀ v, t[i] = some v → v = blockM2 C (decodeRun i.val)

theorem BlockTable.lookup_eq {C : Context} {t : BlockTable} (hv : BlockTable.Valid C t)
    (b : CoupledRun) : BlockTable.lookup C t b = blockM2 C b := by
  unfold BlockTable.lookup
  cases hget : t[encodeRun b]? with
  | none => rfl
  | some o =>
    cases o with
    | none => rfl
    | some v =>
      have hlt := (Array.getElem?_eq_some_iff.mp hget).1
      have he := (Array.getElem?_eq_some_iff.mp hget).2
      have := hv ⟨encodeRun b, hlt⟩ v he
      simp only [decode_encode] at this
      exact this

/-- Boolean version of `Valid`, evaluated by native code. -/
def BlockTable.validCheck (C : Context) (t : BlockTable) : Bool :=
  (List.range t.size).all fun i =>
    match t[i]? with
    | some (some v) => decide (v = blockM2 C (decodeRun i))
    | _ => true

theorem BlockTable.validCheck_sound {C : Context} {t : BlockTable}
    (h : BlockTable.validCheck C t = true) : BlockTable.Valid C t := by
  intro i v hv
  have h1 := List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)
  have hv' : t[i.val]? = some (some v) := by
    rw [Array.getElem?_eq_getElem i.isLt]
    simp only [Fin.getElem_fin] at hv
    rw [hv]
  rw [hv'] at h1
  exact of_decide_eq_true h1

/-- Build the table for a list of run codes (each filled once). -/
def mkBlockTable (C : Context) (size : ℕ) (codes : List ℕ) : BlockTable :=
  codes.foldl (fun t code =>
    if code < size then
      match t[code]? with
      | some none => t.set! code (some (blockM2 C (decodeRun code)))
      | _ => t
    else t) (Array.replicate size none)

/-- All run codes appearing in the programs of a family. -/
def blockCodes (F : CompactModeFamily) : List ℕ :=
  F.toList.flatMap fun B => B.programs.toList.flatMap fun pr =>
    match pr with
    | .path (.carried _ _ _ _ bs _) => bs.map fun b => encodeRun b.run
    | .cycle _ b bs => (b::bs).map fun b => encodeRun b.run
    | _ => []

/-! ### table-backed contexts -/

def strictBlocksT (C : Context) (t : BlockTable) : List CoupledRun → M2
  | [] => M2.ofBoxes (identity 2)
  | b::bs => M2.prod (absM2 (BlockTable.lookup C t b)) (strictBlocksT C t bs)

theorem strictBlocksT_eq {C : Context} {t : BlockTable} (hv : BlockTable.Valid C t)
    (bs : List CoupledRun) :
    (strictBlocksT C t bs).toBoxes = listProduct (bs.map (fun b => matrixAbsolute (C.block b))) := by
  induction bs with
  | nil => exact M2.toBoxes_ofBoxes _
  | cons b bs ih =>
    simp only [strictBlocksT, M2.toBoxes_prod, ih, List.map_cons, listProduct,
      BlockTable.lookup_eq hv, blockM2, absM2_ofBoxes]

def ctxT (t : BlockTable) (hv : BlockTable.Valid RationalStrongPowers.context t) : CachedContext where
  toContext := RationalStrongPowers.context
  chain := fun bs => (strictBlocksT RationalStrongPowers.context t bs).toBoxes
  chain_contains := fun bs => by
    rw [strictBlocksT_eq hv]
    exact (CachedContext.direct RationalStrongPowers.context).chain_contains bs

/-! ### table-backed pure evaluation -/

section Pure
variable {B : Type*}

def scalarsT (C : Context) (t : BlockTable) (bs : List CoupledRun) : Box :=
  scalarProduct (bs.map fun b => (BlockTable.lookup C t b).a)

theorem scalarsT_eq {C : Context} {t : BlockTable} (hv : BlockTable.Valid C t)
    (bs : List CoupledRun) : scalarsT C t bs = scalarProduct (bs.map fun b => C.block b 0 0) := by
  unfold scalarsT
  simp only [BlockTable.lookup_eq hv, blockM2, M2.ofBoxes]

def pureT (C : Context) (t : BlockTable) (q : ModeProgram B) (x y : Vector 4) : Box :=
  match q with
  | .path (.pure s) => C.weightedDot x (action (C.frame s) y)
  | .path (.carried pre _ n _ bs post) =>
    mul (mul (C.start pre n x 0) (scalarsT C t (bs.map TaggedBlock.run))) (C.finish post y 0)
  | .cycle _ b bs => scalarsT C t ((b::bs).map TaggedBlock.run)
  | .isolated => mul (C.start none 0 CachedContext.freeBoxes 0) (C.finish none CachedContext.loopBoxes 0)

theorem pureT_eq {C : CachedContext} {t : BlockTable} (hv : BlockTable.Valid C.toContext t)
    (q : ModeProgram B) (x y : Vector 4) : pureT C.toContext t q x y = C.pure q x y := by
  cases q with
  | path p =>
    cases p with
    | pure s => rfl
    | carried pre tag n hn bs post =>
      simp only [pureT, CachedContext.pure, CachedContext.pathPure, scalarsT_eq hv, List.map_map]
      rfl
  | cycle k b bs =>
    simp only [pureT, CachedContext.pure, CachedContext.cyclePure, scalarsT_eq hv, List.map_map]
    rfl
  | isolated => rfl

end Pure

/-- Always-valid entry using the block table. -/
def entryOfSigT (t : BlockTable) (hv : BlockTable.Valid RationalStrongPowers.context t)
    (s : Signature) : Entry :=
  certify (ctxT t hv) s
    (pureT RationalStrongPowers.context t s.program (maskBoxes s.leftMask) (maskBoxes s.rightMask))
    ((ctxT t hv).absolute s.program (maskBoxes s.leftMask) (maskBoxes s.rightMask))
    (pureT_eq (C := ctxT t hv) hv _ _ _).symm rfl

end SubmittedGenus.CapFourMass.Interval.PrefixNativeLong
