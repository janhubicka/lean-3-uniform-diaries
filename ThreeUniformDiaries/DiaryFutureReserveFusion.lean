import ThreeUniformDiaries.DiaryFutureOrderReserve
import ThreeUniformDiaries.DiaryCountableCertifiedFusion
import ThreeUniformDiaries.DiaryNonleafStageTrivialExtension

/-!
# Countable fusion through finitely checkable future-order reserves

The previous unrestricted relative-extension hypothesis asks that EVERY
admissible finite diary support map extend. This is unnecessarily strong:
a finite map can compress old supported source vertices and leave no
room for source vertices that must be inserted later. The formally
verified order-reserve obstruction rules those stages out.

We restrict attention to stages satisfying an explicit finite
FutureOrderReserve predicate in addition to admissibility.
Nonleaf stages still extend by the identity; the only remaining
hypothesis is a relative new-leaf extension *within this reserved
subsystem*, preserving old leaf images and the reserve predicate.

The result is a mathematically correct pruned fusion statement with
a fully explicit, non-circular finite stage predicate. It DOES NOT
show the new-leaf extension hypothesis, or deduce it from genericity,
finite flip absorption, or other independently established theorems.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A finite full diary support map with adequate numerical room
between every pair of currently supported source vertices. -/
def ReservedDiaryStage
    (H K : Ordered3Graph Nat) (F : Nat → Nat)
    (m : Nat) (f : Nat → Nat) : Prop :=
  AdmissibleCofinalDiaryStage H K F m f ∧
  FutureOrderReserve H m f

namespace ReservedDiaryStage

variable {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m : Nat}

/-- The literal marker-only base satisfies the finite order reserve.
No prescribed target leaf image or genericity assumption is needed. -/
theorem marker_base
    (DH : RoleDiary H) (DK : RoleDiary K)
    (F : Nat → Nat) :
    ReservedDiaryStage H K F 0 (fun u : Nat => u) := by
  refine ⟨AdmissibleCofinalDiaryStage.marker_base DH DK F, ?_⟩
  intro x y hx hy hxy
  change x + (y - x) ≤ y
  omega

/-- A nonleaf step changes neither the supported vertex set nor the
finite reserve condition, so its successor is literally the same map. -/
theorem extend_of_not_leaf
    (P : ReservedDiaryStage H K F m f)
    (hm : ¬ IsLeaf H m) :
    ReservedDiaryStage H K F (m + 1) f := by
  refine ⟨P.1.extend_of_not_leaf hm, ?_⟩
  intro x y hx hy hxy
  have hEq := countableDiaryFiniteSupport_succ_of_not_leaf H m hm
  have hx' : x ∈ countableDiaryFiniteSupport H m := by
    simpa only [hEq] using hx
  have hy' : y ∈ countableDiaryFiniteSupport H m := by
    simpa only [hEq] using hy
  exact P.2 x y hx' hy' hxy

end ReservedDiaryStage

/-- The precise non-circular countable lower-bound reduction:
only leaf steps require extension, and the source/target finite
maps must satisfy the explicit reserve predicate. There is
NO hypothesis that arbitrary, numerically compressed admissible
finite support embeddings can be extended.

The still-open hypothesis is that a fixed reserved finite stage
can be extended at a NEW source leaf while preserving its earlier
selected leaf images and remaining reserved. -/
theorem exists_fullDiaryEmbedding_of_reserved_new_leaf_extensions
    {H K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (F : Nat → Nat)
    (hRealize : ∀ m : Nat, IsLeaf H m →
      ∀ f : Nat → Nat,
        ReservedDiaryStage H K F m f →
        ∃ g : Nat → Nat,
          ReservedDiaryStage H K F (m + 1) g ∧
          (∀ u : Nat, u ∈ countableDiaryLeafPrefix H m →
            g u = f u)) :
    ∃ e : Ordered3Graph.Embedding H K,
      (∀ u : Nat, IsLeaf H u → ∃ t : Nat, e u = F t) ∧
      (∀ u v : Nat, 3 ≤ u → 3 ≤ v →
        K.oneMeetLevel (e u) (e v) =
          e (H.oneMeetLevel u v)) ∧
      (∀ a b c d : Nat, a < b → c < d →
        3 ≤ a → 3 ≤ c →
        K.twoMeetLevel (e a) (e b) (e c) (e d) =
          e (H.twoMeetLevel a b c d)) := by
  let C : CertifiedDiaryFusionData DH K F := {
    Safe := fun m f => ReservedDiaryStage H K F m f
    valid := by
      intro m f hf
      exact hf.1
    initial := by
      exact ⟨fun u => u, ReservedDiaryStage.marker_base DH DK F⟩
    next := by
      intro m f hf
      by_cases hm : IsLeaf H m
      · obtain ⟨g,hg,hKeep⟩ := hRealize m hm f hf
        have hCompat : CofinalDiaryStageCompatible H m f g :=
          hf.1.successor_compatible_of_selected_leaf_agreement hg.1 hKeep
        exact ⟨g,hg,hCompat⟩
      · exact ⟨f,hf.extend_of_not_leaf hm,by intro u hu; rfl⟩
  }
  exact C.exists_full_embedding DK

end DiaryLeafPriority
end ThreeUniformDiaries
