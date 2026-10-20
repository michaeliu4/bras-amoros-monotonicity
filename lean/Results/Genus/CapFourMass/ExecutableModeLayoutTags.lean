import Results.Genus.CapFourMass.ExecutableModeLayout
import Results.Genus.CapFourMass.ExecutableModeTags

namespace SubmittedGenus.CapFourMass.ExecutableModes
open FixedPivot ActualComponent

def FreeLayout.pathTags {r N d : ℕ} (hd : 0<d) (hN : d<N) (L : FreeLayout (r+N) r (r+d))
    (c : Fin L.count) : List (TaggedEdge (Option (CarryRepresentative N d hN))) :=
  ExecutableModes.pathTags hd hN (L.vertex c)

def FreeLayout.cycleTags {r N d : ℕ} (hd : 0<d) (hN : d<N) (L : FreeLayout (r+N) r (r+d))
    (c : Fin L.count) : List (TaggedEdge (Option (CarryRepresentative N d hN))) :=
  ExecutableModes.cycleTags hd hN (L.vertex c)

end SubmittedGenus.CapFourMass.ExecutableModes
