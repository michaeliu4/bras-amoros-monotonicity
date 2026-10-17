import Results.Genus.ArrayNative.Slices

/-! Grouped aggregation of native shards.  `litSum` of a long shard list is split
along `++` into groups whose literal totals are checked one declaration at a time
(bounded kernel memory per declaration), and `AllShards` is assembled along `++`.
Nothing here is new mathematics: two structural lemmas about `List.append`. -/
namespace SubmittedGenus.RawGraph.PackedAcceptance.ArrayNative

theorem litSum_append (l₁ l₂ : List (ℕ × ℕ × ℕ)) :
    litSum (l₁ ++ l₂) = litSum l₁ + litSum l₂ := by
  simp [litSum, List.map_append, List.sum_append]

theorem AllShards_append {a H P : ℕ} :
    ∀ {l₁ l₂ : List (ℕ × ℕ × ℕ)},
      AllShards a H P l₁ → AllShards a H P l₂ → AllShards a H P (l₁ ++ l₂)
  | [], _, _, h₂ => h₂
  | (_, _, _) :: t, _, h₁, h₂ => ⟨h₁.1, AllShards_append (l₁ := t) h₁.2 h₂⟩

#print axioms litSum_append
#print axioms AllShards_append
end SubmittedGenus.RawGraph.PackedAcceptance.ArrayNative
