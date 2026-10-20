import Results.Genus.CapFourMass.CompactModeFamily

/-! A shared bounded executable proposal, not a correctness premise. It builds
natural physical arrays using the original two reflections. Every consumer
still accepts the result with CompactLayout.check and ModeProgram.check.
The deterministic ordering matches the existing untrusted Python producer:
components by least free coordinate, paths from their least endpoint, cycles
from their least coordinate, and reflection r before reflection p. -/
namespace SubmittedGenus.CapFourMass.ExecutableModes
namespace CompactReflection

/-- Total natural physical free-coordinate test, excluding residue zero. -/
def free (m r p v : ℕ) : Bool := decide (0<v ∧ v<m ∧ v≠r ∧ v≠p)

/-- The r-reflection precedes the p-reflection, exactly as in the existing
producer adjacency lists. Invalid indices and self-pairs are omitted. -/
def neighbors (m r p v : ℕ) : List ℕ :=
  ([r,p].map fun t => (m+t-v)%m).filter fun u => free m r p u && decide (u≠v)

/-- Fuel bounds every traversal, including malformed parameter requests.
Repeated vertices stop the proposal; no topology theorem is assumed here. -/
def walk (m r p : ℕ) : ℕ → Option ℕ → ℕ → List ℕ → List ℕ
  | 0,_,_,_ => []
  | fuel+1,previous,current,seen =>
      if seen.contains current then [] else
        current :: match (neighbors m r p current).find? (fun u => previous != some u) with
          | none => []
          | some next => walk m r p fuel (some current) next (current::seen)

/-- A trial walk detects the first endpoint. If its seed was internal, a
second bounded walk finds the other endpoint; the final path starts at their
minimum. Cycles retain the initial least-coordinate walk and orientation. -/
def component (m r p seed : ℕ) : CompactComponent :=
  let trial:=walk m r p m none seed []
  let last:=trial.getLast?.getD seed
  if (neighbors m r p last).length≤1 then
    let other:=match neighbors m r p seed with
      | first::_::_ => (walk m r p m (some first) seed []).getLast?.getD seed
      | _ => seed
    ⟨(walk m r p m none (min last other) []).toArray,false⟩
  else ⟨trial.toArray,true⟩

/-- Iterate possible component minima in original natural order. The seen
set is merely executable proposal state and is not trusted by acceptance. -/
def components (m r p : ℕ) : Array CompactComponent :=
  ((List.range (m-1)).foldl (fun (state : List ℕ × Array CompactComponent) i =>
    let v:=i+1
    if free m r p v && !state.1.contains v then
      let c:=component m r p v
      (c.vertices.toList++state.1,state.2.push c)
    else state) ([],#[])).2

/-- Construct a bounded inverse proposal. modify leaves invalid positions
unchanged; the existing shape and two-sided inverse checks remain mandatory. -/
def inverse (m : ℕ) (cs : Array CompactComponent) : Array (ℕ × ℕ) :=
  cs.toList.zipIdx.foldl (fun inv entry =>
    entry.1.vertices.toList.zipIdx.foldl
      (fun inv slot => inv.modify (slot.1-1) (fun _ => (entry.2,slot.2))) inv)
    (Array.replicate (m-1) (0,0))

/-- One shared finite definition replaces all literal physical arrays. Its
output has no accepted source meaning until the original checker succeeds. -/
def propose (m r p : ℕ) : CompactLayout :=
  let cs:=components m r p
  ⟨cs,inverse m cs⟩

theorem acceptedLayout_valid (m r p : ℕ)
    (h : (propose m r p).check m r p=true) :
    ((propose m r p).acceptedLayout h).Valid :=
  (propose m r p).acceptedLayout_valid h

end CompactReflection

namespace CompactModeBase

/-- Reuses every original typed program and canonical label unchanged. -/
def withProposedLayout (B : CompactModeBase) : CompactModeBase :=
  {B with layout:=CompactReflection.propose (longMultiplicity B.r B.d B.n) B.r (B.r+B.d)}

theorem withProposedLayout_eq (B : CompactModeBase)
    (h : CompactReflection.propose (longMultiplicity B.r B.d B.n) B.r (B.r+B.d)=B.layout) :
    B.withProposedLayout=B := by
  unfold withProposedLayout
  rw [h]

end CompactModeBase

namespace CompactModeFamily

def withProposedLayouts (F : CompactModeFamily) : CompactModeFamily :=
  F.map CompactModeBase.withProposedLayout

/-- Optional finite equality regression against already accepted physical
arrays. Source acceptance itself continues to use the independent checker. -/
def proposalMatches (F : CompactModeFamily) : Bool := decide (∀i : Fin F.size,
  CompactReflection.propose (longMultiplicity F[i].r F[i].d F[i].n) F[i].r (F[i].r+F[i].d)=F[i].layout)

@[simp] theorem proposalMatches_eq_true (F : CompactModeFamily) :
    F.proposalMatches=true ↔ ∀i : Fin F.size,
      CompactReflection.propose (longMultiplicity F[i].r F[i].d F[i].n) F[i].r (F[i].r+F[i].d)=F[i].layout := by
  simp [proposalMatches]

end CompactModeFamily
end SubmittedGenus.CapFourMass.ExecutableModes
