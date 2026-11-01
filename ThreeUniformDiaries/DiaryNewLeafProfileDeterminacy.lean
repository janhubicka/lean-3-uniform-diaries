import ThreeUniformDiaries.DiaryFutureLeafProfileGate
import ThreeUniformDiaries.DiaryLeafGeneratedStageCompatibility

/-!
# A new diary leaf has a forced old-pair profile and a unique generated extension

The missing countable lower-bound step asks for a successor map preserving
previously chosen leaf images. The new source leaf may introduce earlier
one- and two-splits, so unrestricted genericity on leaf triples is not enough.

Here we prove two *necessary* local facts, with no target genericity assumption:

* Every valid successor realizes the complete old-pair edge profile of the
  fresh leaf, including edges involving old markers and split vertices.
* Once the old leaf images and the fresh leaf image are fixed, every image
  on the new leaf-meet support is forced. There is no independent freedom
  to place the newly generated splits.

The old-pair profile is not claimed to be sufficient: the new leaf also
forces role, order, and numerical one- and two-meet constraints. Consequently
this file does NOT establish the existence of relative extensions.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority
namespace AdmissibleCofinalDiaryStage

variable {H K : Ordered3Graph Nat} {F : Nat → Nat}
variable {m : Nat} {f g h : Nat → Nat}

/-- The required mixed old-pair profile follows already from a SINGLE
admissible successor, without waiting for a coherent infinite family. -/
theorem successor_new_leaf_has_old_pair_profile
    (P : AdmissibleCofinalDiaryStage H K F m f)
    (Q : AdmissibleCofinalDiaryStage H K F (m + 1) g)
    (hm : IsLeaf H m)
    (hKeep : ∀ u : Nat, u ∈ countableDiaryLeafPrefix H m →
      g u = f u) :
    OldPairLeafExtensionProfile H K F m f m (g m) := by
  have hCompat : CofinalDiaryStageCompatible H m f g :=
    P.successor_compatible_of_selected_leaf_agreement Q hKeep
  have hmSelected : m ∈ countableDiaryLeafPrefix H (m + 1) :=
    (mem_countableDiaryLeafPrefix_iff H (m + 1) m).mpr
      ⟨hm.1, by omega, hm⟩
  have hmSupported : m ∈ countableDiaryFiniteSupport H (m + 1) :=
    mem_finiteLeafMeetSupport_leaf H
      (countableDiaryLeafPrefix H (m + 1)) m hmSelected
  refine {
    leaf := Q.leaf_role m hmSupported hm
    range := Q.leaf_range m hmSupported hm
    later := ?_
    induced_old_pairs := ?_
  }
  · intro x hx hxm
    have hx' : x ∈ countableDiaryFiniteSupport H (m + 1) :=
      (countableDiaryFiniteSupport_mono H m (m + 1) (by omega)) hx
    have hOrder := Q.ordered x m hx' hmSupported hxm
    calc
      f x = g x := (hCompat x hx).symm
      _ < g m := hOrder
  · intro x y hx hy hxy hym
    have hx' : x ∈ countableDiaryFiniteSupport H (m + 1) :=
      (countableDiaryFiniteSupport_mono H m (m + 1) (by omega)) hx
    have hy' : y ∈ countableDiaryFiniteSupport H (m + 1) :=
      (countableDiaryFiniteSupport_mono H m (m + 1) (by omega)) hy
    have hTriple := Q.induced_edge x y m
      hx' hy' hmSupported hxy hym
    simpa only [hCompat x hx, hCompat y hy] using hTriple.symm

/-- Two valid successors keeping the old selected leaves and using the
same image of the newly selected leaf agree on the ENTIRE new support,
including all newly generated one- and two-split vertices. -/
theorem new_leaf_image_determines_successor
    (Q : AdmissibleCofinalDiaryStage H K F (m + 1) g)
    (R : AdmissibleCofinalDiaryStage H K F (m + 1) h)
    (hKeepG : ∀ u : Nat, u ∈ countableDiaryLeafPrefix H m →
      g u = f u)
    (hKeepH : ∀ u : Nat, u ∈ countableDiaryLeafPrefix H m →
      h u = f u)
    (hNew : g m = h m) :
    ∀ u : Nat, u ∈ countableDiaryFiniteSupport H (m + 1) →
      g u = h u := by
  apply Q.eq_on_support_of_selected_leaves R
  intro u hu
  obtain ⟨hu3, hum, huLeaf⟩ :=
    (mem_countableDiaryLeafPrefix_iff H (m + 1) u).mp hu
  by_cases hEq : u = m
  · simpa only [hEq] using hNew
  · have huOld : u ∈ countableDiaryLeafPrefix H m :=
      (mem_countableDiaryLeafPrefix_iff H m u).mpr
        ⟨hu3, by omega, huLeaf⟩
    exact (hKeepG u huOld).trans (hKeepH u huOld).symm

/-- If the prescribed leaf range contains no realization of the
required old-pair profile, the relative successor does not exist.
This is a necessary condition, not an equivalence or a construction. -/
theorem no_relative_successor_without_old_pair_profile
    (P : AdmissibleCofinalDiaryStage H K F m f)
    (hm : IsLeaf H m)
    (hNo : ∀ v : Nat,
      ¬ OldPairLeafExtensionProfile H K F m f m v) :
    ¬ ∃ g : Nat → Nat,
      AdmissibleCofinalDiaryStage H K F (m + 1) g ∧
      (∀ u : Nat, u ∈ countableDiaryLeafPrefix H m →
        g u = f u) := by
  rintro ⟨g, Q, hKeep⟩
  exact hNo (g m) (P.successor_new_leaf_has_old_pair_profile Q hm hKeep)

end AdmissibleCofinalDiaryStage
end DiaryLeafPriority
end ThreeUniformDiaries
