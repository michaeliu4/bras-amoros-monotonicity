import Results.Genus.RawGraph.RunSegmentation

/-! Mapping a source word through its color erasure commutes with the exact
primary splitBy run computation. -/
namespace SubmittedGenus.RawGraph.RunSegmentation

lemma splitBy_loop_map {A B : Type*} (f : A→B) (r : B→B→Bool) (l : List A)
    (a : A) (g : List A) (gs : List (List A)) :
    (List.splitBy.loop (fun x y => r (f x) (f y)) l a g gs).map (List.map f)=
      List.splitBy.loop r (l.map f) (f a) (g.map f) (gs.map (List.map f)) := by
  induction l generalizing a g gs with
  | nil => simp [List.splitBy.loop,List.map_reverse]
  | cons b l ih =>
    simp only [List.splitBy.loop,List.map_cons]
    cases h : r (f a) (f b) <;> simp [h,ih,List.map_reverse]

lemma splitBy_map {A B : Type*} (f : A→B) (r : B→B→Bool) (l : List A) :
    (l.map f).splitBy r=(l.splitBy (fun a b => r (f a) (f b))).map (List.map f) := by
  cases l with
  | nil => rfl
  | cons a l => exact (splitBy_loop_map f r l a [] []).symm

lemma runs_map {A K : Type*} [DecidableEq K] (color : A→K) (l : List A) :
    runs id (l.map color)=(runs color l).map (List.map color) :=
  splitBy_map color (fun a b => decide (a=b)) l

end SubmittedGenus.RawGraph.RunSegmentation
