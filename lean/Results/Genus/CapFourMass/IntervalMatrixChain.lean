import Results.Genus.CapFourMass.IntervalRationalTables

/-! Local matrix-chain checks replace exponential recursive expansion with a
supplied suffix table. Every entry, including the final identity, is checked. -/
open scoped Matrix
namespace SubmittedGenus.CapFourMass.Interval.MatrixTables

def ChainValid {n N : ℕ} (as : Fin N→Boxes n) (ts : Fin (N+1)→Boxes n) : Prop :=
  (∀i j,ts (Fin.last N) i j=identity n i j) ∧
  ∀k : Fin N,∀i j,ts k.castSucc i j=product (as k) (ts k.succ) i j

instance {n N : ℕ} (as : Fin N→Boxes n) (ts : Fin (N+1)→Boxes n) :
    Decidable (ChainValid as ts) := by unfold ChainValid; infer_instance

theorem chain_contains {n N : ℕ} (as : Fin N→Boxes n)
    (A : Fin N→Matrix (Fin n) (Fin n) ℝ) (ha : ∀k,Encloses (as k) (A k))
    (ts : Fin (N+1)→Boxes n) (ht : ChainValid as ts) :
    Encloses (ts 0) (List.ofFn A).prod := by
  induction N with
  | zero =>
    intro i j
    rw [show (0:Fin (0+1))=Fin.last 0 from rfl,ht.1]
    simpa using identity_contains n i j
  | succ N ih =>
    let tail : Fin (N+1)→Boxes n := fun k=>ts k.succ
    have hv : ChainValid (fun k : Fin N=>as k.succ) tail :=
      ⟨ht.1,fun k i j=>ht.2 k.succ i j⟩
    have hh:=ih (fun k=>as k.succ) (fun k=>A k.succ) (fun k=>ha k.succ) tail hv
    intro i j
    rw [show (0:Fin (N+1+1))=(0:Fin (N+1)).castSucc from rfl,ht.2]
    simpa only [List.ofFn_succ,List.prod_cons] using product_contains (ha 0) hh i j

end SubmittedGenus.CapFourMass.Interval.MatrixTables

namespace SubmittedGenus.CapFourMass.Interval.RationalTables
open MatrixTables

/-- A certified total cache can use its proved fallback outside its literal
finite entries. In-range finite acceptance still checks the supplied entries. -/
structure CachedContext extends Context where
  chain : List CoupledRun→Boxes 2
  chain_contains : ∀bs,Encloses (chain bs)
    (bs.map (fun b=>absoluteMatrix (RationalRuns.block b))).prod

namespace CachedContext

def direct (C : Context) : CachedContext where
  toContext:=C
  chain:=fun bs=>listProduct (bs.map (fun b=>matrixAbsolute (C.block b)))
  chain_contains:=fun bs=>listProduct_contains bs (fun b=>matrixAbsolute (C.block b))
    (fun b=>absoluteMatrix (RationalRuns.block b))
    (fun b=>matrixAbsolute_contains (C.block_contains b))

variable (C : CachedContext)

def pathAbsolute (pre post : Option StrongRun) (n : ℕ) (bs : List CoupledRun)
    (x y : Vector 4) : Box :=
  dot (vectorAbsolute (C.toContext.start pre n x))
    (action (C.chain bs) (vectorAbsolute (C.toContext.finish post y)))

def cycleAbsolute (bs : List CoupledRun) : Box := trace (C.chain bs)

theorem pathAbsolute_contains (pre post : Option StrongRun) (n : ℕ) (bs : List CoupledRun)
    {xb yb : Vector 4} {x y : State→ℝ} (hx : VContains xb x) (hy : VContains yb y) :
    Contains (C.pathAbsolute pre post n bs xb yb) (RationalRuns.pathAbsolute pre post n bs x y) :=
  dot_contains (vectorAbsolute_contains (C.toContext.start_contains pre n hx))
    (action_contains (C.chain_contains bs) (vectorAbsolute_contains (C.toContext.finish_contains post hy)))

theorem cycleAbsolute_contains (bs : List CoupledRun) :
    Contains (C.cycleAbsolute bs) (RationalRuns.cycleAbsolute bs) :=
  trace_contains (C.chain_contains bs)

end CachedContext
end SubmittedGenus.CapFourMass.Interval.RationalTables
