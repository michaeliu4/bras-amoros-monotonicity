import Results.Genus.CapFourMass.IntervalRationalRunSyntax
import Results.Genus.CapFourMass.IntervalRationalTables

namespace SubmittedGenus.CapFourMass.Interval.RationalTableInputs
open MatrixTables RationalTables Expr SourceSyntax
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000


def weights : Vector 4 := ![⟨3237397091296465026388764461268729, 3237397091296465026388764461268730⟩, ⟨2018517086423345943953394641601051, 2018517086423345943953394641601054⟩, ⟨1258545403384956196054941559038254, 1258545403384956196054941559038258⟩, ⟨784703059010520188240256062060351, 784703059010520188240256062060354⟩]

def rights : Mode→Vector 4 := ![![⟨3219813865494605260192479227673111, 3219813865494605260192479227673119⟩, ⟨5192296858534827628530496329220096, 5192296858534827628530496329220096⟩, ⟨5192296858534827628530496329220096, 5192296858534827628530496329220096⟩, ⟨0, 0⟩], ![⟨8475728043214416230534638330542897, 8475728043214416230534638330542903⟩, ⟨-5192296858534827628530496329220096, -5192296858534827628530496329220096⟩, ⟨-5192296858534827628530496329220096, -5192296858534827628530496329220096⟩, ⟨0, 0⟩]]

def norms : Mode→Box := ![⟨4521973981656426736390614578019061, 4521973981656426736390614578019077⟩, ⟨11903489856275837733545983562391748, 11903489856275837733545983562391772⟩]

def roots : Mode→Box := ![⟨5284616434944188519738346999093497, 5284616434944188519738346999093498⟩, ⟨-2007553945135886379730010798454193, -2007553945135886379730010798454185⟩]

def full : Boxes 4 := ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1258545403384956196054941559038254, 1258545403384956196054941559038258⟩, ⟨784703059010520188240256062060351, 784703059010520188240256062060354⟩], ![⟨0, 0⟩, ⟨2018517086423345943953394641601051, 2018517086423345943953394641601054⟩, ⟨1258545403384956196054941559038254, 1258545403384956196054941559038258⟩, ⟨784703059010520188240256062060351, 784703059010520188240256062060354⟩], ![⟨3237397091296465026388764461268729, 3237397091296465026388764461268730⟩, ⟨2018517086423345943953394641601051, 2018517086423345943953394641601054⟩, ⟨1258545403384956196054941559038254, 1258545403384956196054941559038258⟩, ⟨784703059010520188240256062060351, 784703059010520188240256062060354⟩], ![⟨3237397091296465026388764461268729, 3237397091296465026388764461268730⟩, ⟨2018517086423345943953394641601051, 2018517086423345943953394641601054⟩, ⟨1258545403384956196054941559038254, 1258545403384956196054941559038258⟩, ⟨784703059010520188240256062060351, 784703059010520188240256062060354⟩]]

def restricted : Boxes 4 := ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1258545403384956196054941559038254, 1258545403384956196054941559038258⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨2018517086423345943953394641601051, 2018517086423345943953394641601054⟩, ⟨1258545403384956196054941559038254, 1258545403384956196054941559038258⟩, ⟨0, 0⟩], ![⟨3237397091296465026388764461268729, 3237397091296465026388764461268730⟩, ⟨2018517086423345943953394641601051, 2018517086423345943953394641601054⟩, ⟨1258545403384956196054941559038254, 1258545403384956196054941559038258⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem weights_eval : ∀i : State,(z^(i.val+1)).eval inputs=some (weights i) := by decide +kernel

theorem rights_eval : ∀j i,(RationalRunSyntax.rightVector j i).eval inputs=some (rights j i) := by decide +kernel

theorem norms_eval : ∀j,(RationalRunSyntax.norm j).eval inputs=some (norms j) := by decide +kernel

theorem roots_eval : ∀j,(RationalRunSyntax.root j).eval inputs=some (roots j) := by decide +kernel

theorem full_eval : ∀i j,(RationalRunSyntax.transfer 4 4 i j).eval inputs=some (full i j) := by decide +kernel

theorem restricted_eval : ∀i j,(RationalRunSyntax.transfer 4 3 i j).eval inputs=some (restricted i j) := by decide +kernel

theorem weights_contains (i : State) : Contains (weights i) (radius^(i.val+1)) := by
  have h:=Expr.eval_sound _ inputs_contain (weights_eval i)
  simpa only [Expr.real_pow,z_real] using h

theorem rights_contains (j : Mode) : VContains (rights j) (RationalRuns.rightVector j) := by
  intro i
  have he : (RationalRunSyntax.rightVector j i).real values=RationalRuns.rightVector j i :=
    congrFun (RationalRunSyntax.rightVector_real j) i
  rw [←he]
  exact Expr.eval_sound _ inputs_contain (rights_eval j i)

theorem norms_contains (j : Mode) : Contains (norms j) (RationalRuns.norm j) := by
  have h:=Expr.eval_sound _ inputs_contain (norms_eval j)
  simpa only [RationalRunSyntax.norm_real] using h

theorem norms_positive : ∀j,0<(norms j).lo := by decide +kernel

theorem roots_contains (j : Mode) : Contains (roots j) (modeRoot j) := by
  have h:=Expr.eval_sound _ inputs_contain (roots_eval j)
  simpa only [RationalRunSyntax.root_real] using h

theorem full_contains : Encloses full (rationalTransfer 4 4) := by
  intro i j
  have he : (RationalRunSyntax.transfer 4 4 i j).real values=rationalTransfer 4 4 i j :=
    congrFun (congrFun (RationalRunSyntax.transfer_real 4 4) i) j
  rw [←he]
  exact Expr.eval_sound _ inputs_contain (full_eval i j)

theorem restricted_contains : Encloses restricted (rationalTransfer 4 3) := by
  intro i j
  have he : (RationalRunSyntax.transfer 4 3 i j).real values=rationalTransfer 4 3 i j :=
    congrFun (congrFun (RationalRunSyntax.transfer_real 4 3) i) j
  rw [←he]
  exact Expr.eval_sound _ inputs_contain (restricted_eval i j)

end SubmittedGenus.CapFourMass.Interval.RationalTableInputs
