import ThreeUniformDiaries.DiaryFirstLeafInjectiveRange
import ThreeUniformDiaries.DiaryLeafGeneratedStageCompatibility

/-!
# Track C: first-leaf reserved extension fixes the entire old support

The verified first-leaf theorem chooses a high target leaf from an
injective prescribed leaf range and returns a genuine future-reserved
stage. Its explicit agreement condition mentions old SELECTED leaves,
of which there are none at the first-leaf step.

For a supplied real old reserved stage, agreement on those selected
leaves implies agreement on the ENTIRE old finite S1/S2 support by the
checked generated-support determinacy theorem. We expose this exact
compatibility result. The theorem produces an IMMEDIATE successor,
not a finitely persistent successor; it does not solve the later
countable diary fusion obstruction, even at the first leaf.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- At the first genuine source leaf, EVERY supplied reserved old
stage has an old-support-compatible immediate reserved successor
inside any injective prescribed target-leaf range.

No countable universality of the range or leaf-only extension
property is used; only its injectivity and target leaf role.
This result does NOT guarantee finite persistence of the successor. -/
theorem firstLeaf_exists_oldSupportCompatible_reserved_successor
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m : Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (P : ReservedDiaryStage H K F m f)
    (hm : IsLeaf H m)
    (hFirst : countableDiaryLeafPrefix H m = ∅)
    (hFinj : Function.Injective F)
    (hFleaf : ∀ t : Nat, IsLeaf K (F t)) :
    ∃ g : Nat → Nat,
      ReservedDiaryStage H K F (m + 1) g ∧
      CofinalDiaryStageCompatible H m f g := by
  obtain ⟨g, Q, hOldLeaves⟩ :=
    exists_reserved_successor_of_first_leaf_injective_range
      DH DK hm hFirst hFinj hFleaf
  exact ⟨g, Q,
    P.1.successor_compatible_of_selected_leaf_agreement
      Q.1 hOldLeaves⟩

end DiaryLeafPriority
end ThreeUniformDiaries
