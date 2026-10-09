import ThreeUniformDiaries.RootBranchAuxEmbedding
import ThreeUniformDiaries.ExactMeetsFromTypes

/-!
# Exact type-meet equations on canonical branches of the root K_I embedding

RootBranchAuxEmbedding establishes actual singleton and auxiliary
agreement at all selected cuts of a branch. ExactMeetsFromTypes then
turns these equivalences into literal equalities of capped meet levels.
No global aux-type-respecting property of K_I is assumed.
-/

namespace ThreeUniformDiaries
namespace SizeFirstBranchPresentation

variable {n : Nat} {I : EnumNode n} (E : SizeFirstBranchPresentation I)

/-- The root-based canonical branch preserves the exact singleton meet. -/
theorem rootBranch_oneMeet_eq
    (G : GenericEnumerated3Graph)
    (H : Ordered3Graph Nat) (hI : H.initialSegment n = I)
    (u v : Nat) :
    G.graph.oneMeetLevel
      (E.rootBranchEmbedding G H hI u)
      (E.rootBranchEmbedding G H hI v) =
      E.rootBranchEmbedding G H hI (H.oneMeetLevel u v) :=
  (E.rootBranchEmbedding G H hI).oneMeetLevel_eq_of_auxTypeRespecting
    (E.rootBranch_auxTypeRespecting G H hI) u v

/-- The same holds for the exact auxiliary meet of two ordered pairs. -/
theorem rootBranch_auxMeet_eq
    (G : GenericEnumerated3Graph)
    (H : Ordered3Graph Nat) (hI : H.initialSegment n = I)
    (u₀ u₁ v₀ v₁ : Nat) (hu : u₀ < u₁) (hv : v₀ < v₁) :
    G.graph.auxMeetLevel
      (E.rootBranchEmbedding G H hI u₀)
      (E.rootBranchEmbedding G H hI u₁)
      (E.rootBranchEmbedding G H hI v₀)
      (E.rootBranchEmbedding G H hI v₁) =
      E.rootBranchEmbedding G H hI (H.auxMeetLevel u₀ u₁ v₀ v₁) :=
  (E.rootBranchEmbedding G H hI).auxMeetLevel_eq_of_auxTypeRespecting
    (E.rootBranch_auxTypeRespecting G H hI)
    u₀ u₁ v₀ v₁ hu hv

end SizeFirstBranchPresentation
end ThreeUniformDiaries
