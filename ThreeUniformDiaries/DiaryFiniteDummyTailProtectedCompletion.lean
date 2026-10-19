import ThreeUniformDiaries.DiaryFiniteDummyTailPrediary
import ThreeUniformDiaries.DiaryFiniteProtectedWithMarkers

/-!
# Protected countable diary completion of a bounded finite pre-diary

The causal dummy-tail construction has a verified global
RolePrediary on Nat, with an induced finite initial segment.
Every old singleton and full pair-type numerical meet is unchanged,
including mixed split/leaf cases.

Here we transfer an explicitly PROTECTED finite meet picture from
the bounded source to the countable pre-diary. Its S1/S2 protection
conditions are evaluated on exactly the same source vertices,
because old leaf/split roles and numerical meets are preserved.

Apply the already checked one-pass theorem to the countable
pre-diary, preserving every meet of the original protected picture
INCLUDING the distinguished markers 0,1,2.

The conclusion is a genuine COUNTABLE RoleDiary and an induced,
meet-preserving copy of the protected finite picture. It does not
make a finite diary output or solve every-flip target absorption.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H : Ordered3Graph Nat} {n : Nat} {F : Finset Nat}

/-- Exact protected finite-picture S1/S2 hypotheses survive
the addition of any dummy-leaf tail, regardless of its bit choice.
The protected vertices must be old genuine nonmarker vertices. -/
theorem finiteDummyTail_preserves_protected_picture
    (P : FiniteRolePrediaryBlock H n)
    (Q : FiniteProtectedMeetPicture H F)
    (hF : ∀ u : Nat, u ∈ F → u < n)
    (bits : Nat → Bool) :
    FiniteProtectedMeetPicture
      (finiteDummyTailCarrier H n bits) F := by
  let G := finiteDummyTailCarrier H n bits
  refine ⟨Q.above_markers, ?_, ?_⟩
  · intro u v hu hv huLeaf hvLeaf hne
    have hun := hF u hu
    have hvn := hF v hv
    have hSourceU : IsLeaf H u :=
      (finiteDummyTailCarrier_old_leaf_iff
        P.frame bits u hun).mp huLeaf
    have hSourceV : IsLeaf H v :=
      (finiteDummyTailCarrier_old_leaf_iff
        P.frame bits v hvn).mp hvLeaf
    have hSplit : IsOneSplit H (H.oneMeetLevel u v) :=
      Q.singleton_split u v hu hv hSourceU hSourceV hne
    have hMeetN : H.oneMeetLevel u v < n := by
      have hBound := H.oneMeetLevel_le_min u v
      omega
    have hSplitG : IsOneSplit G (H.oneMeetLevel u v) :=
      (finiteDummyTailCarrier_old_oneSplit_iff
        P.frame bits (H.oneMeetLevel u v) hMeetN).mpr hSplit
    rw [finiteDummyTailCarrier_old_oneMeet_exact
      P.frame bits u v hun hvn]
    exact hSplitG
  · intro a b c d ha hb hc hd hab hcd haLeaf hbLeaf hcLeaf hdLeaf
    have han := hF a ha
    have hbn := hF b hb
    have hcn := hF c hc
    have hdn := hF d hd
    have hSourceA : IsLeaf H a :=
      (finiteDummyTailCarrier_old_leaf_iff
        P.frame bits a han).mp haLeaf
    have hSourceB : IsLeaf H b :=
      (finiteDummyTailCarrier_old_leaf_iff
        P.frame bits b hbn).mp hbLeaf
    have hSourceC : IsLeaf H c :=
      (finiteDummyTailCarrier_old_leaf_iff
        P.frame bits c hcn).mp hcLeaf
    have hSourceD : IsLeaf H d :=
      (finiteDummyTailCarrier_old_leaf_iff
        P.frame bits d hdn).mp hdLeaf
    have hSourceCase :=
      Q.leaf_pair_meets a b c d ha hb hc hd hab hcd
        hSourceA hSourceB hSourceC hSourceD
    have hMeet : G.twoMeetLevel a b c d =
        H.twoMeetLevel a b c d :=
      finiteDummyTailCarrier_old_twoMeet_exact
        P.frame bits a b c d han hbn hcn hdn
    rcases hSourceCase with hMarker | hSplit | ⟨hAC,hCap⟩
    · exact Or.inl (hMeet.trans hMarker)
    · have hMeetN : H.twoMeetLevel a b c d < n := by
        have hBound := H.twoMeetLevel_le_min a b c d
        omega
      have hSplitG : IsTwoSplit G (H.twoMeetLevel a b c d) :=
        (finiteDummyTailCarrier_old_twoSplit_iff
          P.frame bits (H.twoMeetLevel a b c d) hMeetN).mpr hSplit
      exact Or.inr (Or.inl (by rw [hMeet]; exact hSplitG))
    · exact Or.inr (Or.inr ⟨hAC, hMeet.trans hCap⟩)

/-- The three original markers and all protected source vertices
lie inside the original finite frame. -/
theorem finiteDummyTail_marked_source_bound
    (P : FiniteRolePrediaryBlock H n)
    (hF : ∀ u : Nat, u ∈ F → u < n)
    (u : Nat) (hu : u ∈ finiteProtectedWithMarkers F) :
    u < n := by
  change u ∈ Finset.range 3 ∪ F at hu
  rcases Finset.mem_union.mp hu with hMarker | hOld
  · have hlt3 : u < 3 := Finset.mem_range.mp hMarker
    have hn3 := P.frame.length_ge_three
    omega
  · exact hF u hOld

/-- FINITE PROTECTED COMPLETION INTO A COUNTABLE DIARY.

For any protected nonmarker finite set F of a finite V/E
pre-diary, there is an ACTUAL countable RoleDiary obtained by
dummy-tail extension followed by one-pass completion.

The old finite marker-extended picture is induced, and its
numeric singleton/full pair meets are transported exactly under
the one-pass old-vertex embedding. No source S1/S2 outside F,
no finite output and no every-flip absorption is claimed. -/
theorem exists_countableDiary_completes_finiteProtected
    (P : FiniteRolePrediaryBlock H n)
    (Q : FiniteProtectedMeetPicture H F)
    (hF : ∀ u : Nat, u ∈ F → u < n) :
    ∃ bits : Nat → Bool,
      RoleDiary
        (onePassRawTarget (finiteDummyTailCarrier H n bits)) ∧
      (∀ u v : Nat,
        u ∈ finiteProtectedWithMarkers F →
        v ∈ finiteProtectedWithMarkers F →
        (onePassRawTarget (finiteDummyTailCarrier H n bits)).oneMeetLevel
          (onePassOldImage (finiteDummyTailCarrier H n bits) u)
          (onePassOldImage (finiteDummyTailCarrier H n bits) v) =
        onePassOldImage (finiteDummyTailCarrier H n bits)
          (H.oneMeetLevel u v)) ∧
      (∀ a b c d : Nat,
        a ∈ finiteProtectedWithMarkers F →
        b ∈ finiteProtectedWithMarkers F →
        c ∈ finiteProtectedWithMarkers F →
        d ∈ finiteProtectedWithMarkers F →
        a < b → c < d →
        (onePassRawTarget (finiteDummyTailCarrier H n bits)).twoMeetLevel
          (onePassOldImage (finiteDummyTailCarrier H n bits) a)
          (onePassOldImage (finiteDummyTailCarrier H n bits) b)
          (onePassOldImage (finiteDummyTailCarrier H n bits) c)
          (onePassOldImage (finiteDummyTailCarrier H n bits) d) =
        onePassOldImage (finiteDummyTailCarrier H n bits)
          (H.twoMeetLevel a b c d)) ∧
      (∀ a b c : Nat, c < n →
        ((onePassRawTarget (finiteDummyTailCarrier H n bits)).edge
          (onePassOldImage (finiteDummyTailCarrier H n bits) a)
          (onePassOldImage (finiteDummyTailCarrier H n bits) b)
          (onePassOldImage (finiteDummyTailCarrier H n bits) c) ↔
        H.edge a b c)) := by
  obtain ⟨bits,PG⟩ := exists_finiteDummyTailCarrier_prediary P
  let G := finiteDummyTailCarrier H n bits
  have QG : FiniteProtectedMeetPicture G F :=
    finiteDummyTail_preserves_protected_picture P Q hF bits
  refine ⟨bits, onePassRawTarget_isDiary PG, ?_, ?_, ?_⟩
  · intro u v hu hv
    have hTail :=
      onePass_finiteProtectedWithMarkers_oneMeet PG QG u v hu hv
    have hSourceMeet :=
      finiteDummyTailCarrier_old_oneMeet_exact
        P.frame bits u v
        (finiteDummyTail_marked_source_bound P hF u hu)
        (finiteDummyTail_marked_source_bound P hF v hv)
    exact hTail.trans (congrArg (onePassOldImage G) hSourceMeet)
  · intro a b c d ha hb hc hd hab hcd
    have hTail :=
      onePass_finiteProtectedWithMarkers_twoMeet PG QG
        a b c d ha hb hc hd hab hcd
    have hSourceMeet :=
      finiteDummyTailCarrier_old_twoMeet_exact P.frame bits
        a b c d
        (finiteDummyTail_marked_source_bound P hF a ha)
        (finiteDummyTail_marked_source_bound P hF b hb)
        (finiteDummyTail_marked_source_bound P hF c hc)
        (finiteDummyTail_marked_source_bound P hF d hd)
    exact hTail.trans (congrArg (onePassOldImage G) hSourceMeet)
  · intro a b c hc
    have hCompletion :=
      onePassRawTarget_edge_image_iff G a b c
    have hTail := finiteDummyTailCarrier_finite_edge_iff
      P.frame bits a b c hc
    exact hCompletion.trans hTail

end DiaryLeafPriority
end ThreeUniformDiaries
