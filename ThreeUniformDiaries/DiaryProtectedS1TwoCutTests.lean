import ThreeUniformDiaries.DiaryCofinalJointFiniteColourPersistence
import ThreeUniformDiaries.DiaryFiniteColourStageCompatibility
import ThreeUniformDiaries.DiaryExactSingletonColourSplitCut
import ThreeUniformDiaries.DiaryCountableRelativeStepExtension

/-!
# Track A: exact S1 meet targets as FINITE two-cut mixed-colour conditions

The full-diary S1 theorem determines the exact numerical singleton
meet of any two distinct genuine leaves by the FIRST target cut at
which their complete mixed singleton-colour masks differ.

For one prescribed old finite set of genuine target leaves and a
candidate new target leaf v, checking all desired one-meet values is
therefore equivalent to a FINITE conjunction of equal-colour and
different-colour tests at the corresponding numeric cuts t and t+1.
The role-diary hypothesis on the TARGET and distinctness are ESSENTIAL;
there is no claim for arbitrary ordered 3-graphs.

These finite tests are a practical interface for a future protected
relative reservoir. No image v is constructed and no persistence,
countable unavoidability or full diary Ramsey theorem is asserted.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The exact target S1 meet of two distinct true diary leaves is the
unique boundary t where the finite complete mixed singleton colours
agree at t but disagree at t+1.  The cutoff t can be ANY natural. -/
theorem RoleDiary.oneMeet_eq_iff_singletonColour_transition
    {K : Ordered3Graph Nat}
    (DK : RoleDiary K)
    {u v : Nat}
    (hu : IsLeaf K u) (hv : IsLeaf K v)
    (hne : u ≠ v) (t : Nat) :
    K.oneMeetLevel u v = t ↔
      (DiaryLowerBoundColors.singletonColour K t u =
        DiaryLowerBoundColors.singletonColour K t v) ∧
      (DiaryLowerBoundColors.singletonColour K (t + 1) u ≠
        DiaryLowerBoundColors.singletonColour K (t + 1) v) := by
  constructor
  · intro hMeet
    constructor
    · exact (DK.singletonColour_eq_iff_cut_le_oneMeet
        hu hv hne t).mpr (by omega)
    · intro hEqual
      have hBeyond : t + 1 ≤ K.oneMeetLevel u v :=
        (DK.singletonColour_eq_iff_cut_le_oneMeet
          hu hv hne (t + 1)).mp hEqual
      omega
  · rintro ⟨hEq, hDiff⟩
    have hLow : t ≤ K.oneMeetLevel u v :=
      (DK.singletonColour_eq_iff_cut_le_oneMeet
        hu hv hne t).mp hEq
    have hUpper : K.oneMeetLevel u v < t + 1 := by
      by_contra hNot
      have hEqNext :
          DiaryLowerBoundColors.singletonColour K (t + 1) u =
          DiaryLowerBoundColors.singletonColour K (t + 1) v :=
        (DK.singletonColour_eq_iff_cut_le_oneMeet
          hu hv hne (t + 1)).mpr (by omega)
      exact hDiff hEqNext
    omega

/-- A finite requested S1-meet profile with all frozen old leaves
is EXACTLY a finite set of two-cut mixed-colour comparisons.
No order-preservation assumption on the enumeration of old leaves. -/
theorem RoleDiary.finite_old_leaf_oneMeet_profile_iff_two_cut_tests
    {K : Ordered3Graph Nat}
    (DK : RoleDiary K)
    (L : Finset Nat) (f : Nat → Nat) (v : Nat)
    (hOldLeaves : ∀ a : Nat, a ∈ L → IsLeaf K (f a))
    (hv : IsLeaf K v)
    (hDifferent : ∀ a : Nat, a ∈ L → f a ≠ v)
    (targetMeet : Nat → Nat) :
    (∀ a : Nat, a ∈ L →
      K.oneMeetLevel (f a) v = targetMeet a) ↔
    (∀ a : Nat, a ∈ L →
      (DiaryLowerBoundColors.singletonColour K (targetMeet a) (f a) =
        DiaryLowerBoundColors.singletonColour K (targetMeet a) v) ∧
      (DiaryLowerBoundColors.singletonColour K (targetMeet a + 1) (f a) ≠
        DiaryLowerBoundColors.singletonColour K (targetMeet a + 1) v)) := by
  constructor
  · intro hMatches a ha
    exact (DK.oneMeet_eq_iff_singletonColour_transition
      (hOldLeaves a ha) hv (hDifferent a ha) (targetMeet a)).mp
        (hMatches a ha)
  · intro hTests a ha
    exact (DK.oneMeet_eq_iff_singletonColour_transition
      (hOldLeaves a ha) hv (hDifferent a ha) (targetMeet a)).mpr
        (hTests a ha)

/-- Specialized to actual OLD SOURCE LEAVES of a genuine admissible
stage, so the target old-leaf role follows from that finite stage.
A future new-leaf candidate v is assumed larger than every old leaf
image (the numerical ordering required by a relative successor).
Under this concrete hypothesis, the proposed numeric S1 meet table
can be checked by finite complete target mixed-colour masks. -/
theorem AdmissibleCofinalDiaryStage.old_new_oneMeet_profile_iff_two_cut_tests
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m : Nat}
    (DK : RoleDiary K)
    (P : AdmissibleCofinalDiaryStage H K F m f)
    (v : Nat) (hv : IsLeaf K v)
    (hAbove : ∀ a : Nat, a ∈ countableDiaryLeafPrefix H m → f a < v)
    (targetMeet : Nat → Nat) :
    (∀ a : Nat, a ∈ countableDiaryLeafPrefix H m →
      K.oneMeetLevel (f a) v = targetMeet a) ↔
    (∀ a : Nat, a ∈ countableDiaryLeafPrefix H m →
      (DiaryLowerBoundColors.singletonColour K (targetMeet a) (f a) =
        DiaryLowerBoundColors.singletonColour K (targetMeet a) v) ∧
      (DiaryLowerBoundColors.singletonColour K (targetMeet a + 1) (f a) ≠
        DiaryLowerBoundColors.singletonColour K (targetMeet a + 1) v)) := by
  have hOld : ∀ a : Nat,
      a ∈ countableDiaryLeafPrefix H m → IsLeaf K (f a) := by
    intro a ha
    have hSupport : a ∈ countableDiaryFiniteSupport H m :=
      mem_finiteLeafMeetSupport_leaf H (countableDiaryLeafPrefix H m) a ha
    have hLeaf : IsLeaf H a :=
      ((mem_countableDiaryLeafPrefix_iff H m a).mp ha).2.2
    exact P.leaf_role a hSupport hLeaf
  exact DK.finite_old_leaf_oneMeet_profile_iff_two_cut_tests
    (countableDiaryLeafPrefix H m) f v
    hOld hv (fun a ha => ne_of_lt (hAbove a ha)) targetMeet

end DiaryLeafPriority
end ThreeUniformDiaries
