import Results.Genus.ArrayNative.Grouped
import Results.Genus.FiniteComparison.Tables
import Results.Genus.ArrayNative.Cap4.G000
import Results.Genus.ArrayNative.Cap4.G001
import Results.Genus.ArrayNative.Cap4.G002
import Results.Genus.ArrayNative.Cap4.G003
import Results.Genus.ArrayNative.Cap4.G004
import Results.Genus.ArrayNative.Cap4.G005
import Results.Genus.ArrayNative.Cap4.G006
import Results.Genus.ArrayNative.Cap4.G007
import Results.Genus.ArrayNative.Cap4.G008
import Results.Genus.ArrayNative.Cap4.G009
import Results.Genus.ArrayNative.Cap4.G010
import Results.Genus.ArrayNative.Cap4.G011
import Results.Genus.ArrayNative.Cap4.G012
import Results.Genus.ArrayNative.Cap4.G013
import Results.Genus.ArrayNative.Cap4.G014
import Results.Genus.ArrayNative.Cap4.G015
import Results.Genus.ArrayNative.Cap4.G016
import Results.Genus.ArrayNative.Cap4.G017
import Results.Genus.ArrayNative.Cap4.G018
import Results.Genus.ArrayNative.Cap4.G019
import Results.Genus.ArrayNative.Cap4.G020
import Results.Genus.ArrayNative.Cap4.G021
import Results.Genus.ArrayNative.Cap4.G022
import Results.Genus.ArrayNative.Cap4.G023
import Results.Genus.ArrayNative.Cap4.G024
import Results.Genus.ArrayNative.Cap4.G025
import Results.Genus.ArrayNative.Cap4.G026
import Results.Genus.ArrayNative.Cap4.G027

/-! Grouped aggregation of the cap4 native shards: 224 shard theorems (each checked by
`native_decide` in its own module) in 28 groups whose literal totals are checked by the
kernel one group at a time; then kernel arithmetic gives `rangePolynomial 597 300 4`
coefficients through 897 equal to `capFourTable`. -/
namespace SubmittedGenus.RawGraph.PackedAcceptance.ArrayNative.Cap4
open Packing FiniteComparison SubmittedGenus.RawGraph.PackedAcceptance.ArrayNative

def shards : List (ℕ × ℕ × ℕ) :=
  G000.shards ++ (G001.shards ++ (G002.shards ++ (G003.shards ++ (G004.shards ++ (G005.shards ++ (G006.shards ++ (G007.shards ++ (G008.shards ++ (G009.shards ++ (G010.shards ++ (G011.shards ++ (G012.shards ++ (G013.shards ++ (G014.shards ++ (G015.shards ++ (G016.shards ++ (G017.shards ++ (G018.shards ++ (G019.shards ++ (G020.shards ++ (G021.shards ++ (G022.shards ++ (G023.shards ++ (G024.shards ++ (G025.shards ++ (G026.shards ++ (G027.shards)))))))))))))))))))))))))))

theorem cover : coverB 0 shards (597 - 2) = true := by decide +kernel

theorem allShards : AllShards 4 897 300 shards :=
  AllShards_append G000.all (AllShards_append G001.all (AllShards_append G002.all (AllShards_append G003.all (AllShards_append G004.all (AllShards_append G005.all (AllShards_append G006.all (AllShards_append G007.all (AllShards_append G008.all (AllShards_append G009.all (AllShards_append G010.all (AllShards_append G011.all (AllShards_append G012.all (AllShards_append G013.all (AllShards_append G014.all (AllShards_append G015.all (AllShards_append G016.all (AllShards_append G017.all (AllShards_append G018.all (AllShards_append G019.all (AllShards_append G020.all (AllShards_append G021.all (AllShards_append G022.all (AllShards_append G023.all (AllShards_append G024.all (AllShards_append G025.all (AllShards_append G026.all (G027.all)))))))))))))))))))))))))))

theorem litSum_shards : litSum shards = G000.total + (G001.total + (G002.total + (G003.total + (G004.total + (G005.total + (G006.total + (G007.total + (G008.total + (G009.total + (G010.total + (G011.total + (G012.total + (G013.total + (G014.total + (G015.total + (G016.total + (G017.total + (G018.total + (G019.total + (G020.total + (G021.total + (G022.total + (G023.total + (G024.total + (G025.total + (G026.total + (G027.total))))))))))))))))))))))))))) := by
  simp only [shards, litSum_append, G000.litSum_eq, G001.litSum_eq, G002.litSum_eq, G003.litSum_eq, G004.litSum_eq, G005.litSum_eq, G006.litSum_eq, G007.litSum_eq, G008.litSum_eq, G009.litSum_eq, G010.litSum_eq, G011.litSum_eq, G012.litSum_eq, G013.litSum_eq, G014.litSum_eq, G015.litSum_eq, G016.litSum_eq, G017.litSum_eq, G018.litSum_eq, G019.litSum_eq, G020.litSum_eq, G021.litSum_eq, G022.litSum_eq, G023.litSum_eq, G024.litSum_eq, G025.litSum_eq, G026.litSum_eq, G027.litSum_eq]

theorem packed : litSum shards % modulus 897 =
    pack (digitBase 897) (fun k : Fin (897+1) => capFourTable k.val) := by
  rw [litSum_shards]
  decide +kernel

theorem bounded : ∀ i : Fin (897+1), capFourTable i.val < digitBase 897 := by
  decide +kernel

theorem range_coeff : ∀ g, g ≤ 897 →
    (rangePolynomial 597 300 4).coeff g = capFourTable g := by
  intro g hg
  exact range_coeff_of_shards 597 300 4 897 (Or.inl rfl) shards cover allShards
    (fun k => capFourTable k.val) packed bounded ⟨g, by omega⟩

#print axioms range_coeff
end SubmittedGenus.RawGraph.PackedAcceptance.ArrayNative.Cap4
