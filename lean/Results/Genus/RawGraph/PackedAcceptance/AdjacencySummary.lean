import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! Ordered adjacent-transition products as an ordinary monoid. Empty
words have no endpoints; singleton words have identity internal product. -/
namespace SubmittedGenus.RawGraph.PackedAcceptance.AdjacencySummary
variable {A M : Type*}

inductive Summary (transition : A → A → M) where
  | empty
  | nonempty (first last : A) (value : M)
  deriving DecidableEq, Repr

variable (transition : A → A → M) [Monoid M]

def combine : Summary transition → Summary transition → Summary transition
  | .empty,b => b
  | a,.empty => a
  | .nonempty a b x,.nonempty c d y => .nonempty a d (x * transition b c * y)

instance : Monoid (Summary transition) where
  one := .empty
  mul := combine transition
  one_mul a := by cases a <;> rfl
  mul_one a := by cases a <;> rfl
  mul_assoc a b c := by
    change combine transition (combine transition a b) c = combine transition a (combine transition b c)
    cases a <;> cases b <;> cases c <;>
      simp [combine, mul_assoc]

def singleton (a : A) : Summary transition := .nonempty a a 1

def ofList (xs : List A) : Summary transition := (xs.map (singleton transition)).prod

lemma ofList_append (xs ys : List A) :
    ofList transition (xs++ys) = ofList transition xs * ofList transition ys := by
  simp [ofList]

/-- Empty cycle value is one; a singleton still has its one self-transition. -/
def close : Summary transition → M
  | .empty => 1
  | .nonempty first last value => value * transition last first

/-- Continue from previous through the remaining word, then close to first. -/
def chain (first previous : A) : List A → M
  | [] => transition previous first
  | a::xs => transition previous a * chain first a xs

def closedWord : List A → M
  | [] => 1
  | a::xs => chain transition a a xs

private def extend (first previous : A) : Summary transition → M
  | .empty => transition previous first
  | .nonempty a b value => transition previous a * value * transition b first

private lemma extend_singleton_mul (first previous a : A) (s : Summary transition) :
    extend transition first previous (singleton transition a * s) =
      transition previous a * extend transition first a s := by
  change extend transition first previous (combine transition (singleton transition a) s) = _
  cases s <;> simp [singleton, combine, extend, mul_assoc]

private lemma extend_ofList (first previous : A) (xs : List A) :
    extend transition first previous (ofList transition xs) = chain transition first previous xs := by
  induction xs generalizing previous with
  | nil => rfl
  | cons a xs ih =>
    change extend transition first previous (singleton transition a * ofList transition xs) = _
    rw [extend_singleton_mul, ih]
    rfl

private lemma close_singleton_mul (a : A) (s : Summary transition) :
    close transition (singleton transition a * s) = extend transition a a s := by
  change close transition (combine transition (singleton transition a) s) = _
  cases s <;> simp [singleton, combine, close, extend]

/-- No commutativity assumption on transition values; order and closure
are exact, including the empty and singleton cases. -/
theorem close_ofList (xs : List A) :
    close transition (ofList transition xs) = closedWord transition xs := by
  cases xs with
  | nil => rfl
  | cons a xs =>
    change close transition (singleton transition a * ofList transition xs) = _
    rw [close_singleton_mul, extend_ofList]
    rfl

lemma singleton_internal (a : A) : ofList transition [a] = .nonempty a a 1 := by
  simp [ofList, singleton]
lemma singleton_close (a : A) : close transition (ofList transition [a]) = transition a a := by
  rw [close_ofList]
  rfl

#print axioms close_ofList
end SubmittedGenus.RawGraph.PackedAcceptance.AdjacencySummary
