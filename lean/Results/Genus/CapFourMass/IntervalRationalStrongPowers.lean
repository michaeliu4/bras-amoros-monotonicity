import Results.Genus.CapFourMass.IntervalRationalStrongChunk15

open scoped Matrix
namespace SubmittedGenus.CapFourMass.Interval.RationalStrongPowers
open MatrixTables RationalTables RationalTableInputs RationalStrongSegments
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def fallback : ℕ→Boxes 4
  | 0=>identity 4
  | n+1=>product (fallback n) full

theorem fallback_contains (n : ℕ) : Encloses (fallback n) ((rationalTransfer 4 4)^n) := by
  induction n with
  | zero=>simpa only [fallback,pow_zero] using identity_contains 4
  | succ n ih=>simpa only [fallback,pow_succ] using product_contains ih full_contains

def lookup (n : ℕ) : Boxes 4 :=
  if h0:n≤25 then Chunk00.powers ⟨n-0,by omega⟩ else
  if h1:n≤50 then Chunk01.powers ⟨n-25,by omega⟩ else
  if h2:n≤75 then Chunk02.powers ⟨n-50,by omega⟩ else
  if h3:n≤100 then Chunk03.powers ⟨n-75,by omega⟩ else
  if h4:n≤125 then Chunk04.powers ⟨n-100,by omega⟩ else
  if h5:n≤150 then Chunk05.powers ⟨n-125,by omega⟩ else
  if h6:n≤175 then Chunk06.powers ⟨n-150,by omega⟩ else
  if h7:n≤200 then Chunk07.powers ⟨n-175,by omega⟩ else
  if h8:n≤225 then Chunk08.powers ⟨n-200,by omega⟩ else
  if h9:n≤250 then Chunk09.powers ⟨n-225,by omega⟩ else
  if h10:n≤275 then Chunk10.powers ⟨n-250,by omega⟩ else
  if h11:n≤300 then Chunk11.powers ⟨n-275,by omega⟩ else
  if h12:n≤325 then Chunk12.powers ⟨n-300,by omega⟩ else
  if h13:n≤350 then Chunk13.powers ⟨n-325,by omega⟩ else
  if h14:n≤375 then Chunk14.powers ⟨n-350,by omega⟩ else
  if h15:n≤400 then Chunk15.powers ⟨n-375,by omega⟩ else
  fallback n

theorem lookup_contains (n : ℕ) : Encloses (lookup n) ((rationalTransfer 4 4)^n) := by
  unfold lookup
  by_cases h0:n≤25
  · rw [dif_pos h0]
    have h:=Chunk00.powers_contain ⟨n-0,by omega⟩
    have he : 0+(n-0)=n := by omega
    simpa only [he] using h
  rw [dif_neg h0]
  by_cases h1:n≤50
  · rw [dif_pos h1]
    have h:=Chunk01.powers_contain ⟨n-25,by omega⟩
    have he : 25+(n-25)=n := by omega
    simpa only [he] using h
  rw [dif_neg h1]
  by_cases h2:n≤75
  · rw [dif_pos h2]
    have h:=Chunk02.powers_contain ⟨n-50,by omega⟩
    have he : 50+(n-50)=n := by omega
    simpa only [he] using h
  rw [dif_neg h2]
  by_cases h3:n≤100
  · rw [dif_pos h3]
    have h:=Chunk03.powers_contain ⟨n-75,by omega⟩
    have he : 75+(n-75)=n := by omega
    simpa only [he] using h
  rw [dif_neg h3]
  by_cases h4:n≤125
  · rw [dif_pos h4]
    have h:=Chunk04.powers_contain ⟨n-100,by omega⟩
    have he : 100+(n-100)=n := by omega
    simpa only [he] using h
  rw [dif_neg h4]
  by_cases h5:n≤150
  · rw [dif_pos h5]
    have h:=Chunk05.powers_contain ⟨n-125,by omega⟩
    have he : 125+(n-125)=n := by omega
    simpa only [he] using h
  rw [dif_neg h5]
  by_cases h6:n≤175
  · rw [dif_pos h6]
    have h:=Chunk06.powers_contain ⟨n-150,by omega⟩
    have he : 150+(n-150)=n := by omega
    simpa only [he] using h
  rw [dif_neg h6]
  by_cases h7:n≤200
  · rw [dif_pos h7]
    have h:=Chunk07.powers_contain ⟨n-175,by omega⟩
    have he : 175+(n-175)=n := by omega
    simpa only [he] using h
  rw [dif_neg h7]
  by_cases h8:n≤225
  · rw [dif_pos h8]
    have h:=Chunk08.powers_contain ⟨n-200,by omega⟩
    have he : 200+(n-200)=n := by omega
    simpa only [he] using h
  rw [dif_neg h8]
  by_cases h9:n≤250
  · rw [dif_pos h9]
    have h:=Chunk09.powers_contain ⟨n-225,by omega⟩
    have he : 225+(n-225)=n := by omega
    simpa only [he] using h
  rw [dif_neg h9]
  by_cases h10:n≤275
  · rw [dif_pos h10]
    have h:=Chunk10.powers_contain ⟨n-250,by omega⟩
    have he : 250+(n-250)=n := by omega
    simpa only [he] using h
  rw [dif_neg h10]
  by_cases h11:n≤300
  · rw [dif_pos h11]
    have h:=Chunk11.powers_contain ⟨n-275,by omega⟩
    have he : 275+(n-275)=n := by omega
    simpa only [he] using h
  rw [dif_neg h11]
  by_cases h12:n≤325
  · rw [dif_pos h12]
    have h:=Chunk12.powers_contain ⟨n-300,by omega⟩
    have he : 300+(n-300)=n := by omega
    simpa only [he] using h
  rw [dif_neg h12]
  by_cases h13:n≤350
  · rw [dif_pos h13]
    have h:=Chunk13.powers_contain ⟨n-325,by omega⟩
    have he : 325+(n-325)=n := by omega
    simpa only [he] using h
  rw [dif_neg h13]
  by_cases h14:n≤375
  · rw [dif_pos h14]
    have h:=Chunk14.powers_contain ⟨n-350,by omega⟩
    have he : 350+(n-350)=n := by omega
    simpa only [he] using h
  rw [dif_neg h14]
  by_cases h15:n≤400
  · rw [dif_pos h15]
    have h:=Chunk15.powers_contain ⟨n-375,by omega⟩
    have he : 375+(n-375)=n := by omega
    simpa only [he] using h
  rw [dif_neg h15]
  exact fallback_contains n

def strong : StrongRun→Boxes 4
  | .full n _=>lookup n
  | .restricted=>restricted

theorem strong_contains (s : StrongRun) : Encloses (strong s) (RationalRuns.strong s) := by
  cases s with
  | full n hn=>exact lookup_contains n
  | restricted=>exact restricted_contains

def context : Context where
  weights:=weights
  right:=rights
  norm:=norms
  root:=roots
  strong:=strong
  weights_contains:=weights_contains
  right_contains:=rights_contains
  norm_contains:=norms_contains
  norm_positive:=norms_positive
  root_contains:=roots_contains
  strong_contains:=strong_contains

end SubmittedGenus.CapFourMass.Interval.RationalStrongPowers
