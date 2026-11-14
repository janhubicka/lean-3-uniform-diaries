import ThreeUniformDiaries.DiaryCofinalOldCutColourExcludesBoundedLeaf
import ThreeUniformDiaries.DiaryFiniteLeafMeetSupport

/-!
# Track A: an old selected source leaf makes the ORIGINAL full old-cut colour nonconstant

English-first adversarial proof: 3-uniform-diaries PR #367.

At the FIRST source leaf, the old support consists of the three
fixed markers and every true target leaf has the SAME complete
old-cut singleton colour. This special fact gives unconditional
whole generic successor cones at the first leaf (#1509).

Once ANY genuine old source leaf a is selected, an ACTUAL reserved
old stage maps it to a true target leaf f(a)=F(i), with
f(a)<oldStageTailCut H m f by definition. The full target RoleDiary
singleton-colour rigidity theorem then says that the COMPLETE
old-cut colour of this particular low target leaf distinguishes
it from EVERY other true target leaf.

An original unordered induced generic leaf embedding F is
injective, so F(i+1) differs from F(i). Hence the complete
old-cut singleton colours of F(i) and F(i+1) differ, and
the original F[G] range CANNOT be globally monochromatic
at this full old-support cut.

This rules out repeating the globally constant-colour argument
unmodified after the first source leaf. It DOES NOT rule out
a selected good MONOCHROMATIC generic subcopy of F[G], and
does not refute countable diary unavoidability.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Nonempty genuine old selected-leaf support forces the
COMPLETE full oldStageTailCut singleton-colour map on the
ORIGINAL prescribed unordered generic leaf range F to have
at least TWO distinct values.

This uses the ACTUAL old reserved stage P, including its true
old leaf-range and order conditions, and the checked full target
diary singleton-colour rigidity at a cut containing f(a).
No target F monotonicity, source m leaf hypothesis, arbitrary
fixed generic refinement or future-horizon persistence is assumed.
The result is a global F nonconstancy statement, NOT absence
of monochromatic generic subcopies. -/
theorem RoleDiary.nonempty_old_leaf_support_forces_nonconstant_original_oldCut_colours
    {H K : Ordered3Graph Nat}
    (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    {m : Nat} (f : Nat → Nat)
    (P : ReservedDiaryStage H K (fun t : Nat => F t) m f)
    (hOld : (countableDiaryLeafPrefix H m).Nonempty) :
    ∃ i j : Nat,
      DiaryLowerBoundColors.singletonColour K
        (oldStageTailCut H m f) (F i) ≠
      DiaryLowerBoundColors.singletonColour K
        (oldStageTailCut H m f) (F j) := by
  classical
  obtain ⟨a, ha⟩ := hOld
  have haSupport : a ∈ countableDiaryFiniteSupport H m :=
    mem_finiteLeafMeetSupport_leaf H
      (countableDiaryLeafPrefix H m) a ha
  have haLeaf : IsLeaf H a :=
    ((mem_countableDiaryLeafPrefix_iff H m a).mp ha).2.2
  obtain ⟨i, hi⟩ := P.1.leaf_range a haSupport haLeaf
  have hBound : f a ≤ oldStageTailCut H m f := by
    change f a ≤
      max ((countableDiaryFiniteSupport H m).sup f)
        ((countableDiaryLeafPrefix H m).sup f) + 1
    have hSup : f a ≤ (countableDiaryLeafPrefix H m).sup f :=
      Finset.le_sup (f := f) ha
    omega
  refine ⟨i, i + 1, ?_⟩
  intro hColourEq
  have hEqAtOld :
      DiaryLowerBoundColors.singletonColour K
        (oldStageTailCut H m f) (f a) =
      DiaryLowerBoundColors.singletonColour K
        (oldStageTailCut H m f) (F (i + 1)) := by
    rw [hi]
    exact hColourEq
  have hOldLeaf : IsLeaf K (f a) := by
    rw [hi]
    exact hFLeaf i
  have hTargetEq : f a = F (i + 1) :=
    (DK.singletonColour_eq_iff_leaf_eq_above_self
      hOldLeaf (hFLeaf (i + 1)) hBound).mp hEqAtOld
  have hIndexEq : i = i + 1 :=
    F.injective (hi.symm.trans hTargetEq)
  omega

end DiaryLeafPriority
end ThreeUniformDiaries
