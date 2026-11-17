import ThreeUniformDiaries.DiaryLowerCanonicalColourUnavoidability
import ThreeUniformDiaries.DiaryCanonicalMarkedRestrictionFactor

/-!
# Unavoidable marked diary colours are surjective

The abstract restriction-by-fibres construction requires the large
colouring to use every colour. The existing kernel-checked
canonicalMarkedDiaryColour_unavoidable result gives a *stronger*
assertion: every marked colour occurs inside every unordered
selfcopy. Choosing the identity selfcopy discharges surjectivity.

No finite-to-countable diary fusion or full diary Ramsey theorem
is used in this argument.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open _root_.ThreeUniformDiaries.Ordered3Graph

/-- If every marked colour is present inside every U-selfcopy,
then the colouring genuinely uses ALL its advertised palette.
The conclusion does not require universality of U. -/
theorem unavoidableMarkedColours_surjective
    {a : Nat} {A : EnumNode a}
    {U : Ordered3Graph Nat}
    (χ : GenuineFiniteEmbeddings A U → GenuineMarkedDiaryTypes A)
    (h : IsEveryMarkedDiaryColourUnavoidable A U χ) :
    Function.Surjective χ := by
  let identity : UnorderedEmbedding U U := {
    toFun := id
    injective := by intro x y hxy; exact hxy
    edge_iff := by intro x y z hxy hyz; exact Iff.rfl
  }
  intro d
  obtain ⟨v, hv⟩ := h identity d
  have hId : v.postcompose identity = v := by
    apply Subtype.ext
    rfl
  refine ⟨v, ?_⟩
  simpa only [hId] using hv

/-- The ACTUAL canonical marked-diary colouring is surjective
for every genuine full diary leaf model of a universal U.
It is therefore a valid large colouring for the abstract
restriction-of-fibres construction. -/
theorem canonicalMarkedDiaryColour_surjective
    (G : GenericEnumerated3Graph)
    (U K : Ordered3Graph Nat)
    (hUniversal : CountablyUniversal U)
    (DK : RoleDiary K)
    (F : UnorderedEmbedding U K)
    (hFLeaf : ∀ x : Nat, IsLeaf K (F x))
    {a : Nat} (A : EnumNode a) :
    Function.Surjective
      (canonicalMarkedDiaryColour DK F hFLeaf A) := by
  apply unavoidableMarkedColours_surjective
    (canonicalMarkedDiaryColour DK F hFLeaf A)
  exact canonicalMarkedDiaryColour_unavoidable
    G U K hUniversal DK F hFLeaf A

end ATRFiniteDecoder
end ThreeUniformDiaries
