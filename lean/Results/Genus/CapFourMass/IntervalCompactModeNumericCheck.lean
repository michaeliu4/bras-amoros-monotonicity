import Results.Genus.CapFourMass.IntervalCompactModeCertificate

/-! Split checking allows a previously checked physical family to be reused
without rerunning its topology/program certificate for each numerical pass. -/
namespace SubmittedGenus.CapFourMass.Interval.ModeSignatures
open ActualComponent ExecutableModes RationalTables
namespace CompactCertificate

def numericCheck (C : CachedContext) {k : ℕ} (entries : Fin k→Entry)
    (A : CompactCertificate) (hb : A.base.check=true) : Bool :=
  if hk : A.KeysValid (k:=k) then
    let L:=A.base.acceptedLayout hb
    let key:=A.key hk
    matchesCheck L A.base.program entries key &&
    (A.pure.isSome || A.mixed.isSome) &&
    optionCheck A.pure (pureSeries C L entries key) &&
    optionCheck A.mixed (mixedSeries C L entries key)
  else false

theorem check_of_numeric (C : CachedContext) {k : ℕ} (entries : Fin k→Entry)
    (A : CompactCertificate) (hb : A.base.check=true)
    (hn : A.numericCheck C entries hb=true) : A.check C entries=true := by
  simpa only [check,dif_pos hb,numericCheck] using hn

end CompactCertificate
end SubmittedGenus.CapFourMass.Interval.ModeSignatures
