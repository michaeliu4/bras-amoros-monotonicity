import Results.Genus.CapFourMass.CompactReflectionProposal
import Results.Genus.CapFourMass.IntervalCompactOriginalBatchCheckV3

/-! Lean-side producer of the compact long-source bases (layout + typed programs).
Port of the untrusted python producer (`groups`/`program`).  Nothing here is trusted:
every base is accepted only through `CompactModeBase.check`. -/
namespace SubmittedGenus.CapFourMass.ExecutableModes.PrefixNative
open FixedPivot ActualComponent

/-- Edge kinds: 0 = E (restricted strong), 1 = D (full strong), 2 = C (carry). -/
structure Atom where
  kind : ℕ
  len : ℕ
  tag : Option ℕ
  deriving Repr, BEq

def edgeWord (m r p : ℕ) (seq : Array ℕ) (cyc : Bool) : List (ℕ × Option ℕ) :=
  let N := m - r
  let d := p - r
  let l := seq.toList
  let es : List (ℕ × ℕ) := (l.zip l.tail) ++
    (if cyc then (match l.getLast?, l.head? with | some a, some b => [(a,b)] | _, _ => []) else [])
  es.map fun (u,v) =>
    if u+v = r ∨ u+v = p then ((if min u v > r then 0 else 1), none)
    else (2, if u > r then
      let a := (u-r-1) % d
      some (max a ((N-2-a) % d)) else none)

def groupAtoms : List (ℕ × Option ℕ) → List Atom
  | [] => []
  | (k,t)::rest =>
    match groupAtoms rest with
    | a::as => if a.kind = k then ⟨k, a.len+1, t⟩ :: as else ⟨k,1,t⟩ :: a :: as
    | [] => [⟨k,1,t⟩]

/-- Untyped program shape. -/
inductive RawProg
  | isolated
  | pure (atom : Option (ℕ × ℕ))
  | carried (pre : Option (ℕ × ℕ)) (tag : Option ℕ) (len : ℕ)
      (blocks : List (ℕ × ℕ × Option ℕ × ℕ)) (post : Option (ℕ × ℕ))
  | cycle (rot : ℕ) (blocks : List (ℕ × ℕ × Option ℕ × ℕ))
  deriving Repr

/-- blocks (kind, run length, carry tag, carry length) from consecutive atom pairs. -/
def pairBlocks : List Atom → List (ℕ × ℕ × Option ℕ × ℕ)
  | a::b::rest => (a.kind, a.len, b.tag, b.len) :: pairBlocks rest
  | _ => []

def rawProgram (m r p : ℕ) (seq : Array ℕ) (cyc : Bool) : RawProg :=
  if seq.size = 1 ∧ seq[0]! > r then .isolated else
  let word := edgeWord m r p seq cyc
  let rot : ℕ :=
    if cyc then
      let n := word.length
      ((List.range n).find? fun i =>
        (word[i]?.map (·.1)).getD 2 ≠ 2 ∧
          (word[(i + n - 1) % n]?.map (·.1)).getD 0 = 2).getD 0
    else 0
  let word := if cyc then word.rotate rot else word
  let atoms := groupAtoms word
  match atoms with
  | [] => .pure none
  | [a] => if a.kind ≠ 2 then .pure (some (a.kind, a.len)) else
      .carried none a.tag a.len [] none
  | a::rest =>
    if cyc then .cycle rot (pairBlocks atoms) else
    let pre : Option (ℕ × ℕ) := if a.kind ≠ 2 then some (a.kind, a.len) else none
    let atoms1 := if a.kind ≠ 2 then rest else atoms
    let post : Option (ℕ × ℕ) := match atoms1.getLast? with
      | some z => if z.kind ≠ 2 then some (z.kind, z.len) else none
      | none => none
    let atoms2 := match atoms1.getLast? with
      | some z => if z.kind ≠ 2 then atoms1.dropLast else atoms1
      | none => atoms1
    match atoms2 with
    | f::bs => .carried pre f.tag f.len (pairBlocks bs) post
    | [] => .isolated

section Typed
variable (N d : ℕ) (hN : d < N)

def tagOf (t : Option ℕ) : Option (CarryRepresentative N d hN) :=
  match t with
  | none => none
  | some a =>
    if h : a < d then
      if h2 : FixedPivot.portPartner N d hN ⟨a,h⟩ ≤ ⟨a,h⟩ then some ⟨⟨a,h⟩,h2⟩ else none
    else none

def strongOf (k len : ℕ) : StrongRun :=
  if k = 0 then .restricted else
  if h : 1 ≤ len then .full len h else .restricted

def optStrong : Option (ℕ × ℕ) → Option StrongRun
  | none => none
  | some (k,len) => some (strongOf k len)

def blockOf (b : ℕ × ℕ × Option ℕ × ℕ) : TaggedBlock (Option (CarryRepresentative N d hN)) :=
  let (k, len, t, cn) := b
  if h : 1 ≤ cn then ⟨⟨strongOf k len, cn, h⟩, tagOf N d hN t⟩
  else ⟨⟨.restricted, 1, le_refl 1⟩, none⟩

def typed : RawProg → ModeProgram (Option (CarryRepresentative N d hN))
  | .isolated => .isolated
  | .pure a => .path (.pure (optStrong a))
  | .carried pre tag len bs post =>
    if h : 1 ≤ len then
      .path (.carried (optStrong pre) (tagOf N d hN tag) len h (bs.map (blockOf N d hN)) (optStrong post))
    else .isolated
  | .cycle rot bs =>
    match bs with
    | b::bs => .cycle rot (blockOf N d hN b) (bs.map (blockOf N d hN))
    | [] => .isolated

end Typed

/-- The generated compact base for the original (r, d, n). -/
def genBase (r d n : ℕ) : CompactModeBase :=
  let m := longMultiplicity r d n
  let layout := CompactReflection.propose m r (r+d)
  ⟨r, d, n, layout,
    layout.components.map fun c =>
      typed (longTailN r d n) d (compactLongN_lt r d n) (rawProgram m r (r+d) c.vertices c.cycle)⟩

end SubmittedGenus.CapFourMass.ExecutableModes.PrefixNative
