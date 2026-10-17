import Results.Genus.Injection.SourceClasses
import Results.Genus.Injection.Code
import Mathlib.Data.List.OfFn

namespace SubmittedGenus
namespace KunzData

/-- The literal sequence of all positive Kunz letters. -/
def toList (d : KunzData) : List ℕ := List.ofFn d.2.val

@[simp] theorem length_toList (d : KunzData) : d.toList.length = d.1.val - 1 := by
  simp [toList]

@[simp] theorem sum_toList (d : KunzData) : d.toList.sum = d.weight := by
  simp [toList, weight, KunzWord.weight, List.sum_ofFn]

@[simp] theorem mem_toList (d : KunzData) (a : ℕ) :
    a ∈ d.toList ↔ ∃ i, d.2.val i = a := by simp [toList]

theorem toList_injective : Function.Injective toList := by
  rintro ⟨⟨m, hm⟩, ⟨x, hx⟩⟩ ⟨⟨n, hn⟩, ⟨y, hy⟩⟩ h
  have hlen := congrArg List.length h
  change (List.ofFn x).length = (List.ofFn y).length at hlen
  simp only [List.length_ofFn] at hlen
  have hmn : m = n := by omega
  subst n
  have hxy : x = y := List.ofFn_inj.mp h
  subst y
  rfl

/-- Prefix containing all coordinates except the final one. -/
def prefixList (d : KunzData) : List ℕ :=
  List.ofFn (fun i : Fin (d.1.val - 2) => d.2.val ⟨i.val, by omega⟩)

theorem toList_eq_prefix_append_last (d : KunzData) (hm : 1 < d.1.val) :
    d.toList = d.prefixList ++ [KunzWord.coord d.2.val (d.1.val - 1)] := by
  rcases d with ⟨⟨m, hmpos⟩, ⟨x, hx⟩⟩
  change 1 < m at hm
  cases m with
  | zero => omega
  | succ n =>
    cases n with
    | zero => omega
    | succ k =>
      change (Fin (k + 1) → ℕ) at x
      change List.ofFn x = (List.ofFn fun i : Fin k => x i.castSucc) ++
        [KunzWord.coord (m := k + 2) x (k + 1)]
      have hlast : KunzWord.coord (m := k + 2) x (k + 1) = x (Fin.last k) :=
        KunzWord.coord_index (m := k + 2) x (Fin.last k)
      simpa only [List.concat_eq_append, hlast] using
        (List.ofFn_succ' (fun i : Fin (k + 1) => x i))

end KunzData

namespace KunzWord

/-- Convert a literal list back to its physically indexed coordinates. -/
def ofList (w : List ℕ) : KunzWord (w.length + 1) :=
  fun i => w[i.val]'(by simpa using i.isLt)

@[simp] theorem ofFn_ofList (w : List ℕ) : List.ofFn (ofList w) = w := by
  exact List.ofFn_getElem

theorem ofList_valid_binary {w : List ℕ} (hw : ∀ a ∈ w, a = 1 ∨ a = 2) :
    Valid (ofList w) := by
  apply valid_of_binary
  intro i
  exact hw _ (List.getElem_mem _)

/-- Binary list interpreted as an actual valid numerical-semigroup word. -/
def binaryData (w : List ℕ) (hw : ∀ a ∈ w, a = 1 ∨ a = 2) : KunzData :=
  ⟨⟨w.length + 1, by omega⟩, ⟨ofList w, ofList_valid_binary hw⟩⟩

@[simp] theorem toList_binaryData (w : List ℕ) (hw : ∀ a ∈ w, a = 1 ∨ a = 2) :
    (binaryData w hw).toList = w := ofFn_ofList w

@[simp] theorem genus_binaryData (w : List ℕ) (hw : ∀ a ∈ w, a = 1 ∨ a = 2) :
    (binaryData w hw).toSemigroup.genus = w.sum := by
  rw [KunzData.genus_toSemigroup, ← KunzData.sum_toList, toList_binaryData]

end KunzWord
end SubmittedGenus
