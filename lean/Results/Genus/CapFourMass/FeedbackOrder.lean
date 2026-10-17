import Results.Genus.CapFourMass.ContractionGeometry
import Mathlib.Data.List.Sort

/-! Finite feedback ordering for the original submitted self-pair contraction.
The indegree-one argument is constructive finite induction: a source is free;
otherwise a three-vertex predecessor chain costs one postponed vertex. -/
namespace SubmittedGenus.CapFourMass.FeedbackOrder

open ContractionGeometry

/-- In a complete distinct list, a later nonpostponed center never points back. -/
def GoodOrder {α : Type*} [DecidableEq α] (R : α → α → Prop)
    (s f : Finset α) (l : List α) : Prop :=
  f ⊆ s ∧ l.Nodup ∧ l.toFinset = s ∧
    l.Pairwise (fun a b => b ∉ f → ¬ R b a)

/-- The generic finite indegree-one feedback bound; no cycle or SCC existence
result is assumed. The list includes every vertex, including postponed ones. -/
theorem indegree_one_feedback {α : Type*} [DecidableEq α]
    (R : α → α → Prop) (s : Finset α)
    (hirr : ∀ a ∈ s, ¬ R a a)
    (hanti : ∀ a ∈ s, ∀ b ∈ s, R a b → ¬ R b a)
    (hin : ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, R a c → R b c → a = b) :
    ∃ f l, GoodOrder R s f l ∧ 3 * f.card ≤ s.card := by
  classical
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    by_cases he : s = ∅
    · subst s
      exact ⟨∅, [], by simp [GoodOrder], by simp⟩
    have hs : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr he
    by_cases hsource : ∃ a ∈ s, ∀ b ∈ s, ¬ R b a
    · obtain ⟨a, ha, has⟩ := hsource
      have hsub : s.erase a ⊆ s := Finset.erase_subset _ _
      obtain ⟨f, l, ⟨hfs, hln, hls, hlp⟩, hfc⟩ :=
        ih (s.erase a) (Finset.erase_ssubset ha)
          (fun b hb => hirr b (hsub hb))
          (fun b hb c hc => hanti b (hsub hb) c (hsub hc))
          (fun b hb c hc d hd => hin b (hsub hb) c (hsub hc) d (hsub hd))
      have hla : a ∉ l := by
        intro h
        have := hls ▸ (List.mem_toFinset.mpr h)
        exact (Finset.mem_erase.mp this).1 rfl
      refine ⟨f, a :: l, ⟨fun b hb => hsub (hfs hb), ?_, ?_, ?_⟩, ?_⟩
      · exact List.nodup_cons.mpr ⟨hla, hln⟩
      · simp [hls, Finset.insert_erase ha]
      · apply List.pairwise_cons.mpr
        refine ⟨?_, hlp⟩
        intro b hb _
        exact has b (hsub (hls ▸ List.mem_toFinset.mpr hb))
      · exact hfc.trans (Finset.card_le_card hsub)
    · have hpred : ∀ a ∈ s, ∃ b ∈ s, R b a := by
        intro a ha
        by_contra hn
        exact hsource ⟨a, ha, fun b hb hr => hn ⟨b, hb, hr⟩⟩
      obtain ⟨w, hw⟩ := hs
      obtain ⟨v, hv, hvw⟩ := hpred w hw
      obtain ⟨u, hu, huv⟩ := hpred v hv
      have huvne : u ≠ v := by intro h; subst v; exact hirr u hu huv
      have hvwne : v ≠ w := by intro h; subst w; exact hirr v hv hvw
      have huwne : u ≠ w := by intro h; subst w; exact hanti u hu v hv huv hvw
      let t := ((s.erase u).erase v).erase w
      have ht : t ⊆ s := fun a ha =>
        Finset.mem_of_mem_erase (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ha))
      have htproper : t ⊂ s := by
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨ht, ?_⟩
        intro h
        have : w ∈ t := h.symm ▸ hw
        exact (Finset.mem_erase.mp this).1 rfl
      obtain ⟨f, l, ⟨hfs, hln, hls, hlp⟩, hfc⟩ :=
        ih t htproper
          (fun a ha => hirr a (ht ha))
          (fun a ha b hb => hanti a (ht ha) b (ht hb))
          (fun a ha b hb c hc => hin a (ht ha) b (ht hb) c (ht hc))
      have hmem : ∀ a, a ∈ l ↔ a ∈ s ∧ a ≠ u ∧ a ≠ v ∧ a ≠ w := by
        intro a
        rw [← List.mem_toFinset, hls]
        simp only [t, Finset.mem_erase]
        tauto
      have hlu : u ∉ l := by simp [hmem]
      have hlv : v ∉ l := by simp [hmem]
      have hlw : w ∉ l := by simp [hmem]
      have hfu : u ∉ f := by
        intro h
        have := hfs h
        simp only [t, Finset.mem_erase] at this
        exact this.2.2.1 rfl
      have hcard : t.card + 3 = s.card := by
        have hv' : v ∈ s.erase u := Finset.mem_erase.mpr ⟨huvne.symm, hv⟩
        have hw' : w ∈ (s.erase u).erase v :=
          Finset.mem_erase.mpr ⟨hvwne.symm, Finset.mem_erase.mpr ⟨huwne.symm, hw⟩⟩
        have h1 := Finset.card_erase_add_one hu
        have h2 := Finset.card_erase_add_one hv'
        have h3 := Finset.card_erase_add_one hw'
        dsimp [t]
        omega
      refine ⟨insert u f, v :: w :: (l ++ [u]), ⟨?_, ?_, ?_, ?_⟩, ?_⟩
      · intro a ha
        rcases Finset.mem_insert.mp ha with rfl | ha
        · exact hu
        · exact ht (hfs ha)
      · simp [List.nodup_cons, List.nodup_append, hln, hlv, hlw,
          huvne.symm, hvwne, huwne.symm]
        intro a ha hae
        exact hlu (hae ▸ ha)
      · ext a
        simp only [List.toFinset_cons, List.toFinset_append, List.toFinset_nil,
          Finset.mem_insert, Finset.mem_union, Finset.notMem_empty, or_false, hls]
        simp only [t, Finset.mem_erase]
        constructor
        · intro h
          rcases h with rfl | rfl | h | rfl
          · exact hv
          · exact hw
          · exact h.2.2.2
          · exact hu
        · intro ha
          by_cases h1 : a = v
          · exact Or.inl h1
          by_cases h2 : a = w
          · exact Or.inr (Or.inl h2)
          by_cases h3 : a = u
          · exact Or.inr (Or.inr (Or.inr h3))
          exact Or.inr (Or.inr (Or.inl ⟨h2, h1, h3, ha⟩))
      · apply List.pairwise_cons.mpr
        constructor
        · intro a ha hnf hrev
          simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | ha | rfl
          · exact hanti _ hv _ hw hvw hrev
          · have hae := hin a ((hmem a).mp ha).1 u hu v hv hrev huv
            exact ((hmem a).mp ha).2.1 hae
          · exact hnf (Finset.mem_insert_self _ _)
        · apply List.pairwise_cons.mpr
          constructor
          · intro a ha hnf hrev
            simp only [List.mem_append, List.mem_singleton] at ha
            rcases ha with ha | rfl
            · have hae := hin a ((hmem a).mp ha).1 v hv w hw hrev hvw
              exact ((hmem a).mp ha).2.2.1 hae
            · exact hnf (Finset.mem_insert_self _ _)
          · apply List.pairwise_append.mpr
            refine ⟨?_, by simp, ?_⟩
            · exact hlp.imp (fun {a b} hab hnf => hab (fun hb => hnf (Finset.mem_insert_of_mem hb)))
            · intro a _ b hb hnf
              have hb' : b = u := by simpa using hb
              subst b
              exact (hnf (Finset.mem_insert_self _ _)).elim
      · rw [Finset.card_insert_of_notMem hfu]
        omega


/-- Concatenating disjoint orders is valid if no later nonpostponed source
points into the earlier block. -/
theorem GoodOrder.append {α : Type*} [DecidableEq α]
    {R : α → α → Prop} {s t f g : Finset α} {l k : List α}
    (hl : GoodOrder R s f l) (hk : GoodOrder R t g k)
    (hd : Disjoint s t)
    (hcross : ∀ a ∈ s, ∀ b ∈ t, b ∉ g → ¬ R b a) :
    GoodOrder R (s ∪ t) (f ∪ g) (l ++ k) := by
  classical
  rcases hl with ⟨hfs, hln, hls, hlp⟩
  rcases hk with ⟨hgt, hkn, hkt, hkp⟩
  refine ⟨Finset.union_subset_union hfs hgt, ?_, ?_, ?_⟩
  · apply List.nodup_append.mpr
    refine ⟨hln, hkn, ?_⟩
    intro a ha b hb hab
    subst b
    exact Finset.disjoint_left.mp hd
      (hls ▸ List.mem_toFinset.mpr ha) (hkt ▸ List.mem_toFinset.mpr hb)
  · simp [hls, hkt]
  · apply List.pairwise_append.mpr
    refine ⟨?_, ?_, ?_⟩
    · exact hlp.imp (fun hab hnf => hab (fun hf => hnf (Finset.mem_union_left _ hf)))
    · exact hkp.imp (fun hab hnf => hab (fun hg => hnf (Finset.mem_union_right _ hg)))
    · intro a ha b hb hnf
      exact hcross a (hls ▸ List.mem_toFinset.mpr ha)
        b (hkt ▸ List.mem_toFinset.mpr hb)
        (fun hg => hnf (Finset.mem_union_right _ hg))

/-- A completely postponed block permits any distinct enumeration. -/
theorem all_postponed {α : Type*} [DecidableEq α]
    (R : α → α → Prop) (s : Finset α) : GoodOrder R s s s.toList := by
  refine ⟨fun _ h => h, Finset.nodup_toList _, Finset.toList_toFinset _, ?_⟩
  apply List.pairwise_of_forall_mem_list
  intro a ha b hb hnf
  exact (hnf (Finset.mem_toList.mp hb)).elim

/-- Removing at most one endpoint of an integer set of diameter at most d
leaves at most d integers and diameter strictly less than d. -/
theorem trim_endpoint (s : Finset ℕ) (d : ℕ) (_hd : 0 < d)
    (hdiam : ∀ i ∈ s, ∀ j ∈ s, |(i : ℤ) - (j : ℤ)| ≤ (d : ℤ)) :
    ∃ t e : Finset ℕ, Disjoint t e ∧ t ∪ e = s ∧ e.card ≤ 1 ∧
      t.card ≤ d ∧
      (∀ i ∈ t, ∀ j ∈ t, |(i : ℤ) - (j : ℤ)| < (d : ℤ)) := by
  classical
  by_cases he : s = ∅
  · subst s
    exact ⟨∅, ∅, by simp, by simp, by simp, by simp, by simp⟩
  have hs : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr he
  let a := s.min' hs
  have ha : a ∈ s := Finset.min'_mem _ _
  have hmin : ∀ i ∈ s, a ≤ i := fun i hi => Finset.min'_le _ _ hi
  have hbounds : ∀ i ∈ s.erase a, a < i ∧ i ≤ a + d := by
    intro i hi
    have hi' := Finset.mem_erase.mp hi
    have hlo := hmin i hi'.2
    have hhi := (abs_le.mp (hdiam i hi'.2 a ha)).2
    omega
  refine ⟨s.erase a, {a}, ?_, ?_, by simp, ?_, ?_⟩
  · simp
  · simp [Finset.union_singleton, Finset.insert_erase ha]
  · have hsub : s.erase a ⊆ Finset.Ioc a (a+d) := by
      intro i hi
      exact Finset.mem_Ioc.mpr (hbounds i hi)
    have hh := Finset.card_le_card hsub
    simpa using hh
  · intro i hi j hj
    have hi' := hbounds i hi
    have hj' := hbounds j hj
    apply abs_lt.mpr
    constructor <;> omega


/-- Centers outside the invariant interval admit a zero-feedback order by
strictly decreasing distance, with arbitrary tie breaking. -/
theorem outside_order (m r p : ℕ) (hrp : r < p) (s : Finset ℕ)
    (hout : ∀ i ∈ s, 3*((p : ℤ)-(r : ℤ)) < |scaledDeviation m r p i|) :
    ∃ l, GoodOrder (Arrow m r p) s ∅ l := by
  classical
  let cmp : ℕ → ℕ → Bool := fun a b =>
    decide (|scaledDeviation m r p b| ≤ |scaledDeviation m r p a|)
  let l := s.toList.mergeSort cmp
  have hperm : l.Perm s.toList := List.mergeSort_perm _ _
  have hmem : ∀ i, i ∈ l ↔ i ∈ s := by
    intro i
    exact hperm.mem_iff.trans Finset.mem_toList
  have hsorted : l.Pairwise (fun a b =>
      |scaledDeviation m r p b| ≤ |scaledDeviation m r p a|) := by
    have ht : ∀ a b c, cmp a b → cmp b c → cmp a c := by
      intro a b c hab hbc
      simp only [cmp, decide_eq_true_eq] at *
      exact hbc.trans hab
    have htotal : ∀ a b, cmp a b || cmp b a := by
      intro a b
      simp only [cmp, Bool.or_eq_true, decide_eq_true_eq]
      exact le_total _ _
    simpa only [l, cmp, decide_eq_true_eq] using
      List.pairwise_mergeSort ht htotal s.toList
  refine ⟨l, Finset.empty_subset _, hperm.nodup_iff.mpr (Finset.nodup_toList _), ?_, ?_⟩
  · ext i
    exact List.mem_toFinset.trans (hmem i)
  · apply hsorted.imp_of_mem
    intro a b ha hb hab _ hba
    have hlt := arrow_outside_decreases hrp hba (hout b ((hmem b).mp hb))
    omega

/-- Original submitted-paper feedback order for every eligible center.
The postponed set has size at most 1 + floor((p-r)/3). -/
theorem eligible_feedback_order (m r p : ℕ) (hrp : r < p) :
    ∃ (f : Finset ℕ) (l : List ℕ),
      GoodOrder (Arrow m r p)
        ((Finset.range m).filter (fun i => p < i ∧ 2*i < m)) f l ∧
      f.card ≤ 1 + (p-r)/3 := by
  classical
  let v := (Finset.range m).filter (fun i => p < i ∧ 2*i < m)
  let inside : ℕ → Prop := fun i =>
    |scaledDeviation m r p i| ≤ 3*((p : ℤ)-(r : ℤ))
  let s := v.filter inside
  let o := v.filter (fun i => ¬ inside i)
  have hsi : ∀ i ∈ s, inside i := fun i hi => (Finset.mem_filter.mp hi).2
  have hd : 0 < p-r := by omega
  have hdiam : ∀ i ∈ s, ∀ j ∈ s,
      |(i : ℤ)-(j : ℤ)| ≤ ((p-r : ℕ) : ℤ) := by
    intro i hi j hj
    have h := inside_diameter (hsi i hi) (hsi j hj)
    have hcast : ((p-r : ℕ) : ℤ) = (p : ℤ)-(r : ℤ) := by omega
    rwa [hcast]
  obtain ⟨t, e, hte, htes, hec, htc, htd⟩ := trim_endpoint s (p-r) hd hdiam
  have hts : t ⊆ s := by rw [← htes]; exact Finset.subset_union_left
  have hes : e ⊆ s := by rw [← htes]; exact Finset.subset_union_right
  have htd' : ∀ i ∈ t, ∀ j ∈ t,
      |(i : ℤ)-(j : ℤ)| < (p : ℤ)-(r : ℤ) := by
    intro i hi j hj
    have h := htd i hi j hj
    have hcast : ((p-r : ℕ) : ℤ) = (p : ℤ)-(r : ℤ) := by omega
    rwa [hcast] at h
  obtain ⟨f, l, horder, hfc⟩ := indegree_one_feedback (Arrow m r p) t
    (fun i _ hi => hi.1 rfl)
    (fun i hi j hj hij hji => no_two_cycle hrp hij hji (htd' i hi j hj))
    (fun i hi j hj k _ hik hjk => incoming_unique hrp hik hjk (htd' i hi j hj))
  have hpost := all_postponed (Arrow m r p) e
  have hinner := horder.append hpost hte
    (by intro a ha b hb hbe; exact (hbe hb).elim)
  rw [htes] at hinner
  have hot : Disjoint o s := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_filter.mp hi).2 (hsi i hj)
  obtain ⟨k, hk⟩ := outside_order m r p hrp o (by
    intro i hi
    have h := (Finset.mem_filter.mp hi).2
    exact lt_of_not_ge h)
  have hall := hk.append hinner hot (by
    intro a ha b hb _ hba
    have hia := arrow_inside_stays hrp hba (hsi b hb)
    exact (Finset.mem_filter.mp ha).2 hia)
  have hpart : o ∪ s = v := by
    ext i
    simp only [o, s, Finset.mem_union, Finset.mem_filter]
    tauto
  rw [hpart, Finset.empty_union] at hall
  refine ⟨f ∪ e, k ++ (l ++ e.toList), hall, ?_⟩
  have hbound : 3*f.card ≤ p-r := hfc.trans htc
  have hdiv : f.card ≤ (p-r)/3 := by omega
  have hunion := Finset.card_union_le f e
  omega


/-- Move all postponed vertices to the end without changing their number or
invalidating the order of the other vertices. -/
theorem GoodOrder.postponed_last {α : Type*} [DecidableEq α]
    {R : α → α → Prop} {s f : Finset α} {l : List α}
    (h : GoodOrder R s f l) :
    ∃ k, GoodOrder R s f k ∧ k.Pairwise (fun a b => a ∈ f → b ∈ f) := by
  classical
  let q : α → Bool := fun a => decide (a ∉ f)
  let a := l.filter q
  let b := l.filter (fun x => !q x)
  have hp : (a ++ b).Perm l := List.filter_append_perm q l
  have hna : ∀ x ∈ a, x ∉ f := by
    intro x hx
    simpa [a, q] using (List.mem_filter.mp hx).2
  have hpb : ∀ x ∈ b, x ∈ f := by
    intro x hx
    simpa [b, q] using (List.mem_filter.mp hx).2
  refine ⟨a ++ b, ⟨h.1, hp.nodup_iff.mpr h.2.1, ?_, ?_⟩, ?_⟩
  · exact (List.toFinset_eq_of_perm _ _ hp).trans h.2.2.1
  · apply List.pairwise_append.mpr
    refine ⟨h.2.2.2.filter q, ?_, ?_⟩
    · apply List.pairwise_of_forall_mem_list
      intro x hx y hy hnf
      exact (hnf (hpb y hy)).elim
    · intro x hx y hy hnf
      exact (hnf (hpb y hy)).elim
  · apply List.pairwise_append.mpr
    refine ⟨?_, ?_, ?_⟩
    · apply List.pairwise_of_forall_mem_list
      intro x hx y hy hxf
      exact (hna x hx hxf).elim
    · apply List.pairwise_of_forall_mem_list
      intro x hx y hy _
      exact hpb y hy
    · intro x hx y hy _
      exact hpb y hy

/-- Postponed positions are a subset of the actual index range, with exactly
the same cardinality as the postponed center set. -/
theorem GoodOrder.positions {α : Type*} [DecidableEq α]
    {R : α → α → Prop} {s f : Finset α} {l : List α}
    (h : GoodOrder R s f l) :
    let P := f.image (fun a => l.idxOf a)
    P ⊆ Finset.range l.length ∧ P.card = f.card ∧
      (∀ k : Fin l.length, (k.val ∈ P ↔ l.get k ∈ f)) ∧
      (∀ i j : Fin l.length, i < j → j.val ∉ P → ¬ R (l.get j) (l.get i)) := by
  classical
  dsimp only
  have hmem : ∀ a ∈ f, a ∈ l := fun a ha =>
    List.mem_toFinset.mp (h.2.2.1.symm ▸ h.1 ha)
  have hiff : ∀ k : Fin l.length,
      (k.val ∈ f.image (fun a => l.idxOf a) ↔ l.get k ∈ f) := by
    intro k
    constructor
    · intro hk
      obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp hk
      have he : l.get k = a := (List.idxOf_inj (List.get_mem _ _)).mp
        ((List.get_idxOf h.2.1 k).trans heq.symm)
      rwa [he]
    · intro hk
      exact Finset.mem_image.mpr ⟨l.get k, hk, List.get_idxOf h.2.1 k⟩
  refine ⟨?_, ?_, hiff, ?_⟩
  · intro n hn
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_range.mpr (List.idxOf_lt_length_iff.mpr (hmem a ha))
  · apply Finset.card_image_of_injOn
    intro a ha b hb he
    exact (List.idxOf_inj (hmem a ha)).mp he
  · intro i j hij hj
    exact h.2.2.2.rel_get_of_lt hij (fun hf => hj ((hiff j).mpr hf))

/-- Full indexed interface: every eligible center appears exactly once, the
number of centers is the submitted N, postponed positions are last, and no
nonpostponed center points to any earlier center. -/
theorem eligible_feedback_indexed (m r p : ℕ) (hrp : r < p) :
    ∃ (l : List ℕ) (P : Finset ℕ),
      l.Nodup ∧ l.length = (m-1)/2-p ∧
      (∀ i, i ∈ l ↔ Eligible m p i) ∧
      P ⊆ Finset.range l.length ∧ P.card ≤ 1+(p-r)/3 ∧
      (∀ i j : Fin l.length, i < j → i.val ∈ P → j.val ∈ P) ∧
      (∀ i j : Fin l.length, i < j → j.val ∉ P →
        ¬ Arrow m r p (l.get j) (l.get i)) := by
  classical
  obtain ⟨f, l, h, hc⟩ := eligible_feedback_order m r p hrp
  obtain ⟨k, hk, hlast⟩ := h.postponed_last
  obtain ⟨hP, hPc, hPiff, horder⟩ := hk.positions
  refine ⟨k, f.image (fun a => k.idxOf a), hk.2.1, ?_, ?_, hP, ?_, ?_, horder⟩
  · rw [← List.toFinset_card_of_nodup hk.2.1, hk.2.2.1, eligible_card]
  · intro i
    rw [← List.mem_toFinset, hk.2.2.1]
    simp only [Finset.mem_filter, Finset.mem_range, Eligible]
    omega
  · rwa [hPc]
  · intro i j hij hi
    exact (hPiff j).mpr (hlast.rel_get_of_lt hij ((hPiff i).mp hi))

end SubmittedGenus.CapFourMass.FeedbackOrder
