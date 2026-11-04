import ThreeUniformDiaries.DiaryIndependentReservedStageExistence
import ThreeUniformDiaries.DiaryCofinalStageRestrictions

/-!
# Arbitrarily long coherent finite reserved-stage systems

The padded finite-source theorem gives ONE reserved map at any
prescribed finite horizon n. Restrict that SAME map to every prior
canonical source support, retaining all marker, role, induced edge/
nonedge, numerical meet, leaf-range and reserve properties.

Hence the exact manuscript hypotheses give arbitrary finite coherent
stage systems. This is NOT an infinite coherent system: the selected
map may depend on the chosen final horizon and move previously placed
leaves. The finite-stage noncompactness counterexample still prevents
a König-style inference without a new bounded-choice/reservoir theorem.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

namespace ReservedDiaryStage

/-- Numerical future reserve, like finite admissibility, restricts
from a later canonical support to any smaller earlier support. -/
theorem restrict
    {H K : Ordered3Graph Nat} {F f : Nat → Nat}
    {m n : Nat}
    (P : ReservedDiaryStage H K F n f)
    (hmn : m ≤ n) :
    ReservedDiaryStage H K F m f := by
  refine ⟨P.1.restrict hmn, ?_⟩
  intro x y hx hy hxy
  exact P.2 x y
    (countableDiaryFiniteSupport_mono H m n hmn hx)
    (countableDiaryFiniteSupport_mono H m n hmn hy) hxy

end ReservedDiaryStage

/-- Every finite horizon admits a SINGLE total map that is an
admissible future-order-reserved diary stage at every earlier level.
The map is allowed to depend on the final horizon. -/
theorem exists_reserved_map_for_all_stages_up_to
    {H U K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (hUniversal : Ordered3Graph.CountablyUniversal U)
    (F : Ordered3Graph.UnorderedEmbedding U K)
    (hFleaf : ∀ t : Nat, IsLeaf K (F t))
    (n : Nat) :
    ∃ f : Nat → Nat,
      ∀ m : Nat, m ≤ n → ReservedDiaryStage H K F m f := by
  obtain ⟨f,hf⟩ :=
    exists_independent_reserved_stage_in_universal_leaf_range
      DH DK G hUniversal F hFleaf n
  exact ⟨f, fun m hmn => hf.restrict hmn⟩

end DiaryLeafPriority
end ThreeUniformDiaries
