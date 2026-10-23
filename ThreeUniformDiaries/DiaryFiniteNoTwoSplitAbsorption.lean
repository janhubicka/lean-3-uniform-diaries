import ThreeUniformDiaries.DiaryFiniteUnconditionalFlipOrbitBound
import ThreeUniformDiaries.DiaryFiniteRigidFlipAbsorption
import ThreeUniformDiaries.DiaryFiniteGlobalDevlinOrientation

/-!
# Strong finite flip absorption for ALL sources without genuine 2-splits

This is an existence theorem, not a finite-code equivalence.

Let A be any complete finite diary with no 2-type splits.
Choose a finite universal diary B containing fully protected
bounded copies of ALL genuine flips of A (already verified).

For any target flip T of B, the verified global Devlin theorem
gives ONE marker-one sign: either all ordered leaf-pair bits
are preserved or all are reversed. If preserved, the original
copy A -> B pulls back to a flip of A with its reference bit
unchanged, so the source pullback is literally A: no 2-splits
means there are no other flip controls.

If reversed, pull the original copy A -> B back to a genuine
opposite-sign flip P of A. The chosen universal B ALSO contains
a protected bounded copy P -> B. Pulling THIS second copy back
to T reverses its marker-one sign once more, hence yields a
flip Q whose reference bit equals A's bit. Again the absence of
2-splits implies Q=A. The full protected pullback theorem
upgrades the selected embedding to all numerical mixed meets.

Thus the verified FIRST finite flip direction implies the
SECOND direction for every source with no genuine 2-splits.
Only TWO candidate protected copies are ever needed per target
flip. Sources with zero/one leaf are handled by the existing
flip-rigidity theorem. This does not solve absorption for
sources with genuine 2-type splits.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- For a bounded fully induced diary copy P -> B, the
source Devlin marker-one bit equals its image bit in B. -/
theorem finite_bounded_copy_marker_one_iff
    {P B : Ordered3Graph Nat} {n k : Nat} {f : Nat → Nat}
    (E : FiniteBoundedMeetEmbedding P B n k f)
    (r t : Nat) (hrt : r < t) (htn : t < n)
    (hr : IsLeaf P r) :
    (P.edge 1 r t ↔ B.edge 1 (f r) (f t)) := by
  have h1r : 1 < r := by have h := hr.1; omega
  simpa only [E.toMeetEmbedding.marker_one] using
    (E.toMeetEmbedding.edge_iff 1 r t h1r hrt htn).symm

/-- For its canonical target-flip pullback, the marker-one
bit is precisely the target edge at the image leaf pair. -/
theorem finite_bounded_pullback_marker_one_iff
    {P B T : Ordered3Graph Nat} {n k : Nat} {f : Nat → Nat}
    (E : FiniteBoundedMeetEmbedding P B n k f)
    (r t : Nat) (hrt : r < t) (htn : t < n)
    (hr : IsLeaf P r) :
    ((finiteDiaryPullbackGraph T n f).edge 1 r t ↔
      T.edge 1 (f r) (f t)) := by
  have h1r : 1 < r := by have h := hr.1; omega
  simpa only [E.toMeetEmbedding.marker_one] using
    (finiteDiaryPullbackGraph_edge_iff T n f
      1 r t h1r hrt htn)

/-- When A has no genuine 2-splits, agreement on ONE marker-one
bit forces any two genuine finite flips of A to be identical:
the S2 witness conditions of the faithful flip signature theorem
are vacuous. -/
theorem finite_no_twoSplit_flips_eq_of_reference_marker
    {A P Q : Ordered3Graph Nat} {n : Nat}
    (hNoTwo : ∀ s : Nat, ¬ IsTwoSplit A s)
    (FP : FiniteDiaryFlip A P n)
    (FQ : FiniteDiaryFlip A Q n)
    (r t : Nat) (hrt : r < t) (htn : t < n)
    (hr : IsLeaf A r) (ht : IsLeaf A t)
    (hMark : P.edge 1 r t ↔ Q.edge 1 r t) :
    P = Q := by
  apply finite_two_flips_eq_of_global_marker_and_S2_bits
    FP FQ r t hrt htn hr ht hMark
  intro s hs
  exact False.elim (hNoTwo s hs)

/-- MAIN TWO-COPY ABSORPTION THEOREM:
For every genuine finite source diary with NO 2-splits,
there exists an actual bounded finite diary target B which
contains a fully induced all-mixed-meet preserving copy of A
in EVERY genuine target flip.

The proof uses the global sign of a target flip and at most
two protected source-flip copies from the finite universal B.
It neither assumes free E3 orientations nor attempts to
construct an absorber for sources containing 2-splits. -/
theorem exists_finite_absorbing_target_of_no_twoSplits
    (A : Ordered3Graph Nat) (n : Nat)
    (DA : FiniteRoleDiaryBlock A n)
    (hNoTwo : ∀ s : Nat, ¬ IsTwoSplit A s) :
    ∃ (B : Ordered3Graph Nat) (k : Nat),
      FiniteRoleDiaryBlock B k ∧
      AbsorbsEveryTargetFlipInside A B n k := by
  classical
  by_cases hPair : FiniteSourceHasLeafPair A n
  · obtain ⟨⟨r,t⟩,hrt,htn,hr,ht⟩ := hPair
    obtain ⟨B,k,DB,hAllCopies⟩ :=
      exists_finiteDiary_for_all_source_flips_bounded A n DA
    refine ⟨B,k,DB,?_⟩
    intro T FT
    obtain ⟨f,EA⟩ := hAllCopies A (FiniteDiaryFlip.refl DA)
    let P := finiteDiaryPullbackGraph T n f
    have FP : FiniteDiaryFlip A P n :=
      finiteDiaryPullbackGraph_is_sourceFlip
        DA EA.toMeetEmbedding EA.image_bound FT
    have EP : FiniteBoundedMeetEmbedding P T n k f :=
      finiteDiaryPullbackGraph_boundedEmbedding_into_targetFlip
        DA EA FT
    have hFr : IsLeaf B (f r) :=
      (EA.toMeetEmbedding.leaf_iff r hr.1 (by omega)).mpr hr
    have hFt : IsLeaf B (f t) :=
      (EA.toMeetEmbedding.leaf_iff t ht.1 htn).mpr ht
    have hFrt : f r < f t := EA.toMeetEmbedding.strictMono hrt
    have hFtn : f t < k := EA.image_bound t htn
    have hMarkA := finite_bounded_copy_marker_one_iff
      EA r t hrt htn hr
    have hMarkP := finite_bounded_pullback_marker_one_iff
      (T := T) EA r t hrt htn hr
    rcases finite_flip_marker_one_global_sign FT with hPres | hRev
    · have hTarget : B.edge 1 (f r) (f t) ↔
          T.edge 1 (f r) (f t) :=
        hPres (f r) (f t) hFrt hFtn hFr hFt
      have hMark : A.edge 1 r t ↔ P.edge 1 r t := by
        tauto
      have hEq : A = P :=
        finite_no_twoSplit_flips_eq_of_reference_marker
          hNoTwo (FiniteDiaryFlip.refl DA) FP
          r t hrt htn hr ht hMark
      refine ⟨f,?_⟩
      simpa only [hEq] using EP
    · have hTarget : B.edge 1 (f r) (f t) ↔
          ¬ T.edge 1 (f r) (f t) :=
        hRev (f r) (f t) hFrt hFtn hFr hFt
      have hAP : A.edge 1 r t ↔ ¬ P.edge 1 r t := by
        tauto
      obtain ⟨g,EG⟩ := hAllCopies P FP
      let Q := finiteDiaryPullbackGraph T n g
      have FQ : FiniteDiaryFlip P Q n :=
        finiteDiaryPullbackGraph_is_sourceFlip
          FP.target_diary EG.toMeetEmbedding EG.image_bound FT
      have FAQ : FiniteDiaryFlip A Q n := FP.trans FQ
      have EQ : FiniteBoundedMeetEmbedding Q T n k g :=
        finiteDiaryPullbackGraph_boundedEmbedding_into_targetFlip
          FP.target_diary EG FT
      have hPr : IsLeaf P r :=
        ((FP.role_iff r hr.1 (by omega)).1).mp hr
      have hPt : IsLeaf P t :=
        ((FP.role_iff t ht.1 htn).1).mp ht
      have hGr : IsLeaf B (g r) :=
        (EG.toMeetEmbedding.leaf_iff r hPr.1 (by omega)).mpr hPr
      have hGt : IsLeaf B (g t) :=
        (EG.toMeetEmbedding.leaf_iff t hPt.1 htn).mpr hPt
      have hGrt : g r < g t := EG.toMeetEmbedding.strictMono hrt
      have hGtn : g t < k := EG.image_bound t htn
      have hMarkG := finite_bounded_copy_marker_one_iff
        EG r t hrt htn hPr
      have hMarkQ := finite_bounded_pullback_marker_one_iff
        (T := T) EG r t hrt htn hPr
      have hTargetG : B.edge 1 (g r) (g t) ↔
          ¬ T.edge 1 (g r) (g t) :=
        hRev (g r) (g t) hGrt hGtn hGr hGt
      have hPQ : P.edge 1 r t ↔ ¬ Q.edge 1 r t := by
        tauto
      have hAQ : A.edge 1 r t ↔ Q.edge 1 r t := by
        tauto
      have hEq : A = Q :=
        finite_no_twoSplit_flips_eq_of_reference_marker
          hNoTwo (FiniteDiaryFlip.refl DA) FAQ
          r t hrt htn hr ht hAQ
      refine ⟨g,?_⟩
      simpa only [hEq] using EQ
  · have hRigid : FiniteDiaryFlipRigid A n := by
      intro P FP
      exact (finite_two_flips_eq_of_no_source_leaf_pair
        DA (FiniteDiaryFlip.refl DA) FP hPair).symm
    exact exists_finite_absorbing_target_of_flip_rigid
      A n DA hRigid

end DiaryLeafPriority
end ThreeUniformDiaries
