import ThreeUniformDiaries.TypedFiniteCoordinateCompletion
import ThreeUniformDiaries.FiniteAembCanonicalImages

/-!
# Complete finite-target Aemb canonical coding existence

Under precisely the actual finite m-vertex aux-type-respecting
embedding assumptions, typed strong pictures at exactly the selected
levels exist in all three coordinates, and their *constructed*
finite canonical maps encode every source branch prefix H|f(i)+1.

This combines the typed E0/E1/E2^- completion, all three root
identities, the concrete coordinate-map inductions and the final
enumeration successor law. No artificial source vertex assumptions,
no abstract CanonicalMap structure, and no Milliken hypothesis.

The remaining manuscript interface is that H may be an arbitrary
countable enumerated hypergraph rather than an EnumNode N, and the
finite type-tree coding must be expressed in K_I branch notation.
-/

namespace ThreeUniformDiaries
namespace EnumNode

theorem exists_finiteAemb_coding_of_finite
    {m N : Nat} (A : EnumNode m) (H : EnumNode N)
    (f : Nat → Nat)
    (hf : Ordered3Graph.FiniteAuxEmbedding
      A.toOrdered3Graph H.toOrdered3Graph f m)
    (n : Nat) (hnm : n ≤ m) (hm : 0 < m)
    (hfix : ∀ j < n, f j = j) :
    ∃ (r₀ : EnumNode (f 0)) (r₁ : OneNode (f 0))
      (r₂ : AuxNode (f 0)),
      ∃ (S₀ S₁ S₂ : Set CoordNode),
      ∃ (h₀ : CoordNode.FiniteStrongPicture S₀ f (m - 1)
        (.enum (f 0) r₀))
        (h₁ : CoordNode.FiniteStrongPicture S₁ f (m - 1)
          (.one (f 0) r₁))
        (h₂ : CoordNode.FiniteStrongPicture S₂ f (m - 1)
          (.aux (f 0) r₂)),
      (∀ x, finiteEnumCandidate H f n m x → x ∈ S₀) ∧
      (∀ x, finiteOneCandidate A H f n x → x ∈ S₁) ∧
      (∀ x, finiteAuxCandidate A H f n x → x ∈ S₂) ∧
      (∀ (i : Nat) (him : i < m),
        (CoordNode.finiteStrongPicture_enumCanonicalMap h₀ h₁ h₂ i
          (by omega) (A.truncate i)).val.succ
          (CoordNode.finiteStrongPicture_oneCanonicalMap h₁ h₂ i
            (by omega) (A.oneType i i)).val =
          H.truncate (f i + 1)) := by
  obtain ⟨r₀, r₁, r₂, S₀, S₁, S₂,
      hinc₀, hinc₁, hinc₂, h₀, h₁, h₂⟩ :=
    A.exists_typed_threeCoordinate_picture_of_finite
      H f hf n hnm hm hfix
  obtain ⟨_, _, _, hCode⟩ :=
    A.finiteAemb_canonical_images_of_typed_pictures
      H f hf n hm hfix h₀ h₁ h₂ hinc₀ hinc₁ hinc₂
  exact ⟨r₀, r₁, r₂, S₀, S₁, S₂,
    h₀, h₁, h₂, hinc₀, hinc₁, hinc₂, hCode⟩

end EnumNode
end ThreeUniformDiaries
