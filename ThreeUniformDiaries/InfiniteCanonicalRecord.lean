import ThreeUniformDiaries.InfiniteCanonicalAuxTypeCompat
import ThreeUniformDiaries.InfiniteCanonicalInjectivity
import ThreeUniformDiaries.InfiniteCanonicalSelectedTriples
import ThreeUniformDiaries.InfiniteCanonicalAuxOneRestriction
import ThreeUniformDiaries.CanonicalMap

/-!
# Assemble a real geometric infinite picture into CanonicalMap

Every field of CanonicalMap is now supplied by a verified theorem about
the genuine recursively defined infinite E2/E1/E0 canonical maps.
No CanonicalMap compatibility field, embedding preservation, or
injectivity property is postulated. This closes the abstract-to-
concrete compatibility interface for the canonical-map lemma.

The next separate obligation is composing TWO geometric strong vector
pictures and proving that their associated CanonicalMap objects compose.
The vector-Milliken transfer is also independent and remains open.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- A synchronized triple of genuine infinite geometric strong pictures
induces the full canonical-map record, including all ambient 1-/aux-
type identities at skipped levels. -/
noncomputable def infiniteStrongPictureCanonicalMap
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : InfiniteStrongPicture S₀ f (.enum (f 0) r₀))
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂))
    (hf : StrictMono f) : CanonicalMap where
  level := f
  strictMono := hf
  mapAux := fun n a => (infiniteAuxCanonicalMap h₂ n a).val
  mapOne := fun n a => (infiniteOneCanonicalMap h₁ h₂ n a).val
  mapEnum := fun n a => (infiniteEnumCanonicalMap h₀ h₁ h₂ n a).val
  mapAux_injective := fun n => infiniteAuxCanonicalMap_injective h₂ hf n
  mapOne_injective := fun n => infiniteOneCanonicalMap_injective h₁ h₂ hf n
  mapEnum_injective := fun n => infiniteEnumCanonicalMap_injective h₀ h₁ h₂ hf n
  enum_triple_compat := by
    intro N i j k H hij hjk hkN
    exact infiniteEnumCanonicalMap_selectedTriple
      h₀ h₁ h₂ hf N i j k hij hjk hkN H
  truncate_compat := by
    intro N l H hl
    exact (infiniteEnumCanonicalMap_truncate
      h₀ h₁ h₂ hf l N hl H).symm
  oneType_compat := by
    intro N l v H hlv hvN
    exact infiniteCanonicalMap_oneType_compat h₀ h₁ h₂ hf H hlv hvN
  auxType_compat := by
    intro N l u v H hlu huv hvN
    exact infiniteCanonicalMap_auxType_compat h₀ h₁ h₂ hf H hlu huv hvN

end CoordNode
end ThreeUniformDiaries
