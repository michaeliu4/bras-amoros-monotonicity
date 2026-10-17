import Results.Genus.RawGraph.Transfer
import Mathlib.Data.List.SplitBy

/-! Source-order-preserving maximal constant-color runs, using the pinned
primary List.splitBy API rather than an assumed run-layout certificate. -/
namespace SubmittedGenus.RawGraph.RunSegmentation

variable {A K : Type*} [DecidableEq K]

def runs (color : A→K) (l : List A) : List (List A) :=
  l.splitBy (fun a b => decide (color a=color b))

@[simp] theorem flatten_runs (color : A→K) (l : List A) : (runs color l).flatten=l :=
  List.flatten_splitBy _ _

lemma run_nonempty (color : A→K) (l : List A) {g : List A} (hg : g∈runs color l) : g≠[] :=
  List.ne_nil_of_mem_splitBy hg

lemma run_constant (color : A→K) (l : List A) {g : List A} (hg : g∈runs color l)
    (a : A) (ha : a∈g) : color a=color (g.head (run_nonempty color l hg)) := by
  have hc : g.IsChain (fun a b => color a=color b) := by
    simpa only [decide_eq_true_eq] using List.isChain_of_mem_splitBy hg
  letI : Trans (fun a b => color a=color b) (fun a b => color a=color b)
      (fun a b => color a=color b) := ⟨fun h1 h2 => h1.trans h2⟩
  cases g with
  | nil => simp at ha
  | cons x xs =>
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · rfl
    · exact (hc.rel_cons ha).symm

/-- Adjacent maximal runs have different colors at their touching boundary. -/
lemma runs_alternate (color : A→K) (l : List A) :
    (runs color l).IsChain (fun g h => ∃ hg : g≠[], ∃ hh : h≠[],
      color (g.getLast hg) ≠ color (h.head hh)) := by
  have hc := List.isChain_getLast_head_splitBy (fun a b => decide (color a=color b)) l
  apply hc.imp
  intro g h hh
  obtain ⟨hg,hh,hne⟩ := hh
  exact ⟨hg,hh,of_decide_eq_false hne⟩

lemma runs_head_alternate (color : A→K) (l : List A) :
    (runs color l).IsChain (fun g h => ∃ hg : g≠[], ∃ hh : h≠[],
      color (g.head hg) ≠ color (h.head hh)) := by
  apply (runs_alternate color l).imp_of_mem_imp
  intro g h hg _ hh
  obtain ⟨hgn,hhn,hne⟩ := hh
  refine ⟨hgn,hhn,?_⟩
  have he := run_constant color l hg (g.getLast hgn) (List.getLast_mem hgn)
  exact fun hh => hne (he.trans hh)

/-- Grouping does not change a noncommutative product or its order. -/
theorem product_runs {M : Type*} [Monoid M] (color : A→K) (l : List A) (f : A→M) :
    (l.map f).prod = ((runs color l).map (fun g => (g.map f).prod)).prod := by
  conv_lhs => rw [← flatten_runs color l, List.map_flatten, List.prod_flatten]
  simp only [List.map_map,Function.comp_def]

/-- Every additive source count is conserved by the same run compilation. -/
theorem sum_runs {M : Type*} [AddMonoid M] (color : A→K) (l : List A) (f : A→M) :
    (l.map f).sum = ((runs color l).map (fun g => (g.map f).sum)).sum := by
  conv_lhs => rw [← flatten_runs color l, List.map_flatten, List.sum_flatten]
  simp only [List.map_map,Function.comp_def]

lemma run_product {M : Type*} [Monoid M] (color : A→K) (l : List A) (f : K→M)
    {g : List A} (hg : g∈runs color l) :
    (g.map (fun a => f (color a))).prod = (f (color (g.head (run_nonempty color l hg))))^g.length := by
  have hm : g.map (fun a => f (color a)) = List.replicate g.length (f (color (g.head (run_nonempty color l hg)))) := by
    have hc : ∀ x∈g.map (fun a => f (color a)), x=f (color (g.head (run_nonempty color l hg))) := by
      intro x hx
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
      rw [run_constant color l hg a ha]
    simpa only [List.length_map] using List.eq_replicate_length.mpr hc
  rw [hm,List.prod_replicate]

end SubmittedGenus.RawGraph.RunSegmentation
