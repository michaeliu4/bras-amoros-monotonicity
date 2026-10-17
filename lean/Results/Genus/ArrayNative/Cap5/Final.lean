import Results.Genus.ArrayNative.Slices
import Results.Genus.FiniteComparison.Tables
import Results.Genus.ArrayNative.Cap5.S000_063
import Results.Genus.ArrayNative.Cap5.S063_077
import Results.Genus.ArrayNative.Cap5.S077_086
import Results.Genus.ArrayNative.Cap5.S086_093
import Results.Genus.ArrayNative.Cap5.S093_099
import Results.Genus.ArrayNative.Cap5.S099_105
import Results.Genus.ArrayNative.Cap5.S105_110
import Results.Genus.ArrayNative.Cap5.S110_114
import Results.Genus.ArrayNative.Cap5.S114_118
import Results.Genus.ArrayNative.Cap5.S118_123
import Results.Genus.ArrayNative.Cap5.S123_131
import Results.Genus.ArrayNative.Cap5.S131_147

/-! Aggregation of the cap5 native shards: 12 shard theorems (each checked by
`native_decide` in its own module) plus kernel arithmetic give
`rangePolynomial 149 149 5` coefficients through 300 equal to `capFiveTable`. -/
namespace SubmittedGenus.RawGraph.PackedAcceptance.ArrayNative.Cap5
open Packing FiniteComparison

def shards : List (ℕ × ℕ × ℕ) :=
  [(0, 63, Cap5.S000_063.lit),
   (63, 77, Cap5.S063_077.lit),
   (77, 86, Cap5.S077_086.lit),
   (86, 93, Cap5.S086_093.lit),
   (93, 99, Cap5.S093_099.lit),
   (99, 105, Cap5.S099_105.lit),
   (105, 110, Cap5.S105_110.lit),
   (110, 114, Cap5.S110_114.lit),
   (114, 118, Cap5.S114_118.lit),
   (118, 123, Cap5.S118_123.lit),
   (123, 131, Cap5.S123_131.lit),
   (131, 147, Cap5.S131_147.lit)]

theorem cover : coverB 0 shards (149 - 2) = true := by decide

theorem allShards : AllShards 5 300 149 shards :=
  ⟨Cap5.S000_063.shard, Cap5.S063_077.shard, Cap5.S077_086.shard, Cap5.S086_093.shard, Cap5.S093_099.shard, Cap5.S099_105.shard, Cap5.S105_110.shard, Cap5.S110_114.shard, Cap5.S114_118.shard, Cap5.S118_123.shard, Cap5.S123_131.shard, Cap5.S131_147.shard, trivial⟩

theorem packed : litSum shards % modulus 300 =
    pack (digitBase 300) (fun k : Fin (300+1) => capFiveTable k.val) := by
  decide +kernel

theorem bounded : ∀ i : Fin (300+1), capFiveTable i.val < digitBase 300 := by
  decide +kernel

theorem range_coeff : ∀ g, g ≤ 300 →
    (rangePolynomial 149 149 5).coeff g = capFiveTable g := by
  intro g hg
  exact range_coeff_of_shards 149 149 5 300 (Or.inr rfl) shards cover allShards
    (fun k => capFiveTable k.val) packed bounded ⟨g, by omega⟩

#print axioms range_coeff
end SubmittedGenus.RawGraph.PackedAcceptance.ArrayNative.Cap5
