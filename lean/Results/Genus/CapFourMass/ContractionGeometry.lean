import Results.Genus.RawGraph.ComponentLocalization

/-! Original submitted-paper self-pair gadget geometry. All coordinates are
physical coordinates. The scaled center avoids floating-point or rounding
assumptions in the contraction ordering. -/
namespace SubmittedGenus.CapFourMass.ContractionGeometry

def Eligible (m p i : ℕ) : Prop := p < i ∧ 2 * i < m

def Arrow (m r p i j : ℕ) : Prop :=
  i ≠ j ∧ (i + 2 * j = m + r ∨ i + 2 * j = m + p)

def scaledDeviation (m r p i : ℕ) : ℤ :=
  6 * (i : ℤ) - (2 * (m : ℤ) + (r : ℤ) + (p : ℤ))

theorem gadget_bounds {m r p i : ℕ} (hr : 1 ≤ r) (hrp : r < p)
    (hi : Eligible m p i) :
    p < i ∧ i < m ∧ p < 2*i ∧ 2*i < m ∧
    p < m+r-i ∧ m+r-i < m ∧ m < 2*(m+r-i) ∧
    p < m+p-i ∧ m+p-i < m ∧ m < 2*(m+p-i) := by
  rcases hi with ⟨hi,hmi⟩
  omega

theorem only_target_leaf_identifications {m r p i : ℕ}
    (hr : 1 ≤ r) (hrp : r < p) (hi : Eligible m p i) :
    i ≠ 2*i ∧ i ≠ m+r-i ∧ i ≠ m+p-i ∧ m+r-i ≠ m+p-i := by
  rcases hi with ⟨hi,hmi⟩
  omega

/-- The exact two affine dependency maps in integral scaled coordinates. -/
theorem arrow_scaled {m r p i j : ℕ} (h : Arrow m r p i j) :
    2 * scaledDeviation m r p j =
      -scaledDeviation m r p i + 3 * ((r : ℤ) - (p : ℤ)) ∨
    2 * scaledDeviation m r p j =
      -scaledDeviation m r p i + 3 * ((p : ℤ) - (r : ℤ)) := by
  rcases h.2 with h | h
  · left
    unfold scaledDeviation
    omega
  · right
    unfold scaledDeviation
    omega

/-- Outside the central interval, arrows strictly decrease distance from its center. -/
theorem arrow_outside_decreases {m r p i j : ℕ} (hrp : r < p)
    (h : Arrow m r p i j)
    (hout : 3 * ((p : ℤ) - (r : ℤ)) < |scaledDeviation m r p i|) :
    |scaledDeviation m r p j| < |scaledDeviation m r p i| := by
  have hlin := arrow_scaled h
  have hdiff : (0 : ℤ) < (p : ℤ) - (r : ℤ) := by omega
  rcases le_total 0 (scaledDeviation m r p i) with hi | hi <;>
    rcases le_total 0 (scaledDeviation m r p j) with hj | hj
  all_goals simp only [abs_of_nonneg, abs_of_nonpos, hi, hj] at *
  all_goals rcases hlin with hlin | hlin <;> omega

/-- Both affine maps preserve the closed central interval. -/
theorem arrow_inside_stays {m r p i j : ℕ} (_hrp : r < p)
    (h : Arrow m r p i j)
    (hin : |scaledDeviation m r p i| ≤ 3 * ((p : ℤ) - (r : ℤ))) :
    |scaledDeviation m r p j| ≤ 3 * ((p : ℤ) - (r : ℤ)) := by
  have hlin := arrow_scaled h
  have hab := abs_le.mp hin
  apply abs_le.mpr
  rcases hlin with hlin | hlin <;> constructor <;> omega

/-- In a set of diameter strictly below p-r, a target has at most one source. -/
theorem incoming_unique {m r p i k j : ℕ} (_hrp : r < p)
    (hi : Arrow m r p i j) (hk : Arrow m r p k j)
    (hdiam : |(i : ℤ) - (k : ℤ)| < (p : ℤ) - (r : ℤ)) : i = k := by
  have hab := abs_lt.mp hdiam
  rcases hi.2 with hi | hi <;> rcases hk.2 with hk | hk <;> omega

/-- No directed two-cycle survives in such a short interval. -/
theorem no_two_cycle {m r p i j : ℕ} (_hrp : r < p)
    (hi : Arrow m r p i j) (hj : Arrow m r p j i)
    (hdiam : |(i : ℤ) - (j : ℤ)| < (p : ℤ) - (r : ℤ)) : False := by
  have hab := abs_lt.mp hdiam
  have hne := hi.1
  rcases hi.2 with hi | hi <;> rcases hj.2 with hj | hj <;> omega

def Gadget (m r p i : ℕ) : Finset ℕ := {i, 2*i, m+r-i, m+p-i}

def Failure (x : ℕ → ℕ) (i : ℕ) : Prop := x i = 1 ∧ x (2*i) = 3

/-- For nonpostponed centers, every earlier event meeting the gadget is
made false by the entire proposed local failure family. -/
theorem nonpostponed_survival {m r p i j : ℕ} {x : ℕ → ℕ}
    (hr : 1 ≤ r) (hrp : r < p) (hi : Eligible m p i) (hj : Eligible m p j)
    (hne : i ≠ j) (horder : ¬ Arrow m r p i j)
    (hxi : x i = 1) (hxt : x (2*i) = 3)
    (hmeet : j ∈ Gadget m r p i ∨ 2*j ∈ Gadget m r p i) : ¬ Failure x j := by
  intro hf
  have hgb := gadget_bounds hr hrp hi
  rcases hi with ⟨hi,hmi⟩
  rcases hj with ⟨hj,hmj⟩
  have hnarr : i + 2*j ≠ m+r ∧ i + 2*j ≠ m+p := by
    constructor <;> intro h
    · exact horder ⟨hne, Or.inl h⟩
    · exact horder ⟨hne, Or.inr h⟩
  simp only [Gadget, Finset.mem_insert, Finset.mem_singleton] at hmeet
  rcases hmeet with (h | h | h | h) | (h | h | h | h)
  · exact hne h.symm
  · have hh := hf.1
    rw [h, hxt] at hh
    omega
  · omega
  · omega
  · have hh := hf.2
    rw [h, hxi] at hh
    omega
  · omega
  · omega
  · omega

/-- Assigning two to each nonshared reflection leaf also survives events
whose targets meet those leaves, permitting arbitrary postponed order. -/
theorem postponed_survival {m r p i j : ℕ} {x : ℕ → ℕ}
    (hr : 1 ≤ r) (hrp : r < p) (hi : Eligible m p i) (hj : Eligible m p j)
    (hne : i ≠ j) (hxi : x i = 1) (hxt : x (2*i) = 3)
    (hxr : m+r-i ≠ 2*i → x (m+r-i) = 2)
    (hxp : m+p-i ≠ 2*i → x (m+p-i) = 2)
    (hmeet : j ∈ Gadget m r p i ∨ 2*j ∈ Gadget m r p i) : ¬ Failure x j := by
  intro hf
  have hgb := gadget_bounds hr hrp hi
  rcases hi with ⟨hi,hmi⟩
  rcases hj with ⟨hj,hmj⟩
  simp only [Gadget, Finset.mem_insert, Finset.mem_singleton] at hmeet
  rcases hmeet with (h | h | h | h) | (h | h | h | h)
  · exact hne h.symm
  · have hh := hf.1
    rw [h, hxt] at hh
    omega
  · omega
  · omega
  · have hh := hf.2
    rw [h, hxi] at hh
    omega
  · omega
  · have hneq : m+r-i ≠ 2*i := by omega
    have hh := hf.2
    rw [h, hxr hneq] at hh
    omega
  · have hneq : m+p-i ≠ 2*i := by omega
    have hh := hf.2
    rw [h, hxp hneq] at hh
    omega

/-- The submitted number N is exactly the number of eligible centers. -/
theorem eligible_card (m p : ℕ) :
    ((Finset.range m).filter (fun i => p < i ∧ 2*i < m)).card =
      (m-1)/2 - p := by
  have hset : (Finset.range m).filter (fun i => p < i ∧ 2*i < m) =
      Finset.Icc (p+1) ((m-1)/2) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    omega
  rw [hset, Nat.card_Icc]
  omega

/-- Any two centers in the invariant interval are separated by at most d. -/
theorem inside_diameter {m r p i j : ℕ}
    (hi : |scaledDeviation m r p i| ≤ 3*((p : ℤ)-(r : ℤ)))
    (hj : |scaledDeviation m r p j| ≤ 3*((p : ℤ)-(r : ℤ))) :
    |(i : ℤ)-(j : ℤ)| ≤ (p : ℤ)-(r : ℤ) := by
  have hi' := abs_le.mp hi
  have hj' := abs_le.mp hj
  unfold scaledDeviation at hi' hj'
  apply abs_le.mpr
  constructor <;> omega

/-- Every genuine Kunz word avoids each forbidden self-pair event. -/
theorem valid_avoids {m p i : ℕ} {x : KunzWord m} (hx : x.Valid)
    (hi : Eligible m p i) : ¬ Failure (KunzWord.coord x) i := by
  intro hf
  have hi0 : 0 < i := by have := hi.1; omega
  have him : i < m := by have := hi.2; omega
  have hh := hx.noncarry i i hi0 him hi0 him (by have := hi.2; omega)
  have heq : i+i = 2*i := by omega
  rw [heq, hf.1, hf.2] at hh
  omega

open RawGraph RawGraph.SourceModel

/-- The center has no unary loop restriction and the exact alphabet {1,2,3}. -/
theorem center_domain {m r p : ℕ} (hr : 1 ≤ r) (hrp : r < p)
    (i : Fin (m-1)) (hi : Eligible m p (physical i)) (v : ℕ) :
    Domain r p 4 i v ↔ 1 ≤ v ∧ v ≤ 3 := by
  have hip := hi.1
  have him := hi.2
  have hfree : IsFree r p i := by unfold IsFree IsPivot; omega
  have hnp : ¬ IsPivot r p i := hfree
  have hnstrong : ¬ StrongLoop r p i := by unfold StrongLoop; omega
  have hncarry : ¬ CarryLoop r p i := by unfold CarryLoop; omega
  have hir : ¬ physical i < r := by omega
  simp [Domain, hnp, hfree, lower, hnstrong, hncarry, upper, hir]

/-- Every other proposed gadget spin, at least two, satisfies all unary
restrictions above the rightmost pivot, including additional carried loops. -/
theorem high_domain {m r p : ℕ} (hrp : r < p) (i : Fin (m-1))
    (hip : p < physical i) {v : ℕ} (hv : 2 ≤ v ∧ v ≤ 3) :
    Domain r p 4 i v := by
  have hfree : IsFree r p i := by unfold IsFree IsPivot; omega
  have hnp : ¬ IsPivot r p i := hfree
  have hnstrong : ¬ StrongLoop r p i := by unfold StrongLoop; omega
  have hir : ¬ physical i < r := by omega
  simp only [Domain, hnp, hfree, false_implies, true_implies, true_and,
    lower, hnstrong, upper, hir, ↓reduceIte]
  by_cases hc : CarryLoop r p i <;> simp [hc] <;> omega

end SubmittedGenus.CapFourMass.ContractionGeometry
