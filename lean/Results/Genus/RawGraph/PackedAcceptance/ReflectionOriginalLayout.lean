import Results.Genus.RawGraph.PackedAcceptance.ReflectionFullLayout
import Results.Genus.RawGraph.PackedAcceptance.ReflectionGcdParameters

/-! Uniform executable complete physical layouts for every original pair of
pivots. All indexing, orbit decomposition and coverage is proved internally. -/
namespace SubmittedGenus.RawGraph.PackedAcceptance.ReflectionOriginalLayout
open LayoutCompiler SourceModel
open scoped BigOperators

structure Coordinates (M r p : ℕ) where
  g : ℕ
  n : ℕ
  δ : ℕ
  g_pos : 0<g
  modulus : M=g*(n+2)
  gap : p=r+g*δ
  coprime : Nat.Coprime δ (n+2)
  pivot_pos : 0<p
  pivot_lt : p<g*(n+2)

def coordinates (M r p : ℕ) (hrp : r<p) (hpm : p<M) : Coordinates M r p := by
  let g := ReflectionGcdParameters.gcdScale M r p
  let L := ReflectionGcdParameters.orbitLength M r p
  let δ := ReflectionGcdParameters.reducedGap M r p
  have hM : 0<M := by omega
  have hL : 2≤L := ReflectionGcdParameters.orbitLength_two hrp hpm
  have hLn : L=(L-2)+2 := by omega
  have he : M=g*((L-2)+2) := by
    rw [←hLn]
    exact ReflectionGcdParameters.modulus_eq M r p
  exact {
    g := g
    n := L-2
    δ := δ
    g_pos := ReflectionGcdParameters.gcdScale_pos hM
    modulus := he
    gap := by have h:=ReflectionGcdParameters.gap_eq M r p; change p-r=g*δ at h; omega
    coprime := by rw [←hLn]; exact ReflectionGcdParameters.reducedGap_coprime hM
    pivot_pos := by omega
    pivot_lt := by rw [←he]; exact hpm }

/-- Every numerical operation in the returned layout is explicit: gcd,
quotient, finite involution indices, modular inverse and component formulas. -/
def layout (M r p : ℕ) (hrp : r<p) (hpm : p<M) : Layout M :=
  let c := coordinates M r p hrp hpm
  letI : NeZero c.g := ⟨ne_of_gt c.g_pos⟩
  ReflectionGcdParameters.transportLayout c.modulus
    (ReflectionFullLayout.layout c.n r p c.δ c.coprime c.gap c.pivot_pos c.pivot_lt)

/-- Unconditional source coverage for the original valid pivot range. -/
theorem covers (M r p a : ℕ) (hrp : r<p) (hpm : p<M) :
    Covers (layout M r p hrp hpm) r p a := by
  let c := coordinates M r p hrp hpm
  letI : NeZero c.g := ⟨ne_of_gt c.g_pos⟩
  change Covers (ReflectionGcdParameters.transportLayout c.modulus
    (ReflectionFullLayout.layout c.n r p c.δ c.coprime c.gap c.pivot_pos c.pivot_lt)) r p a
  apply (ReflectionGcdParameters.transportLayout_covers _ _ r p a).mpr
  exact ReflectionFullLayout.covers c.n r p c.δ a c.coprime c.gap c.pivot_pos c.pivot_lt

/-- The executable family evaluates exactly the submitted raw source. -/
theorem source_polynomial {M r p a : ℕ} (hp : Parameters M r p a) :
    rawPolynomial M r p a=∏c,componentRun (layout M r p hp.2.1 hp.2.2.1) r p a c :=
  rawPolynomial_eq_components (layout M r p hp.2.1 hp.2.2.1) hp
    (covers M r p a hp.2.1 hp.2.2.1)

#print axioms coordinates
#print axioms covers
#print axioms source_polynomial
end SubmittedGenus.RawGraph.PackedAcceptance.ReflectionOriginalLayout
