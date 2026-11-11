import ThreeUniformDiaries.DiaryFiniteColourStageCompatibility
import ThreeUniformDiaries.DiaryPersistentSuccessorBoundEquivalence
import ThreeUniformDiaries.DiaryFixedLeafImageSurvival

/-!
# Track A: one fixed joint finite-colour fibre characterizes persistence

Fix a genuine old admissible diary stage f at level m. In a full target
RoleDiary, the complete mixed singleton masks of all old selected leaves
at one cut B >= their old images certify literal agreement on the entire
old support. If a specified genuine new target leaf u satisfies u <= B,
the SAME cut also isolates the new leaf: equality with its mask forces
the actual next image to equal u.

Thus a single fixed vector of FINITE old/new leaf colours recurring at
cofinally many genuine reserved horizons is equivalent, after choosing
some B and u, to a finitely persistent compatible next-leaf successor.

All the horizon maps must be genuine reserved stages and B, u are fixed
BEFORE the cofinal quantifier. This is a recognition theorem, not a
construction of the recurrent fibre, a saturation principle, a relative
geometric reservoir, or unconditional diary unavoidability.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- One finite, FIXED mixed-colour vector for all selected old leaves
and one proposed next genuine leaf u occurs in actual reserved stages
at arbitrarily large source horizons. Unlike ordinary old/new stage
compatibility, this predicate is phrased solely in terms of finite
colour tests, while genuine horizon stages remain essential. -/
def HasCofinalJointOldNewLeafColour
    (H K : Ordered3Graph Nat) (F f : Nat → Nat)
    (m B u : Nat) : Prop :=
  ∀ N : Nat, ∃ n : Nat, N ≤ n ∧
    ∃ g : Nat → Nat,
      ReservedDiaryStage H K F (m + 1 + n) g ∧
      (∀ a : Nat, a ∈ countableDiaryLeafPrefix H m →
        DiaryLowerBoundColors.singletonColour K B (g a) =
          DiaryLowerBoundColors.singletonColour K B (f a)) ∧
      DiaryLowerBoundColors.singletonColour K B (g m) =
        DiaryLowerBoundColors.singletonColour K B u

/-- English proof: old-leaf colour equality at cut B certifies
old-S_m support equality by the checked finite-colour rigidity lemma.
The new-leaf colour equality at the SAME cut B identifies its image
with u, since u is a genuine target leaf at or below B. Consequently
all cofinally late actual reserved witnesses share the fixed next
image u while retaining the entire old support. The verified bounded-
image/finite-choice theorem yields a persistent reserved successor. -/
theorem persistent_successor_of_cofinal_joint_old_new_leaf_colour
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m B u : Nat}
    (DK : RoleDiary K)
    (P : AdmissibleCofinalDiaryStage H K F m f)
    (hm : IsLeaf H m)
    (hu : IsLeaf K u) (huB : u ≤ B)
    (hBoundOld : ∀ a : Nat,
      a ∈ countableDiaryLeafPrefix H m → f a ≤ B)
    (hRecur : HasCofinalJointOldNewLeafColour H K F f m B u) :
    ∃ g : Nat → Nat,
      PersistentReservedDiaryStage H K F (m + 1) g ∧
      CofinalDiaryStageCompatible H m f g := by
  have hCofinal : HasCofinalBoundedNextLeafImages H K F f m := by
    refine ⟨u, ?_⟩
    intro N
    obtain ⟨n, hn, g, Q, hOldColours, hNextColour⟩ := hRecur N
    have Qold : AdmissibleCofinalDiaryStage H K F m g :=
      Q.1.restrict (by omega)
    have hOld : CofinalDiaryStageCompatible H m f g :=
      (P.compatible_iff_leaf_colour_at_cut DK Qold hBoundOld).mpr
        hOldColours
    have hmSelected : m ∈ countableDiaryLeafPrefix H (m + 1 + n) :=
      (mem_countableDiaryLeafPrefix_iff H (m + 1 + n) m).mpr
        ⟨hm.1, by omega, hm⟩
    have hmSupported : m ∈ countableDiaryFiniteSupport H (m + 1 + n) :=
      mem_finiteLeafMeetSupport_leaf H
        (countableDiaryLeafPrefix H (m + 1 + n)) m hmSelected
    have hgLeaf : IsLeaf K (g m) :=
      Q.1.leaf_role m hmSupported hm
    have hEq : u = g m :=
      (DK.singletonColour_eq_iff_leaf_eq_above_self
        hu hgLeaf huB).mp hNextColour.symm
    exact ⟨n, hn, g, Q, hOld, by omega⟩
  exact (persistentSuccessor_iff_cofinalBoundedNextLeafImages hm).mpr
    hCofinal

/-- Sharp finite-vector reformulation: a persistent successor exists
IFF SOME one finite cut B and SOME one genuine target leaf u, both
fixed before all future horizons, witness recurrent old/new mixed
singleton-colour equality. The source old stage is genuine.

The forward direction takes u to be the persistent next-stage image,
B = max(u, max old selected-leaf image), and restricts each compatible
future horizon. The converse applies the preceding theorem. -/
theorem persistent_successor_iff_exists_cofinal_joint_finite_colour
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m : Nat}
    (DK : RoleDiary K)
    (P : AdmissibleCofinalDiaryStage H K F m f)
    (hm : IsLeaf H m) :
    (∃ g : Nat → Nat,
      PersistentReservedDiaryStage H K F (m + 1) g ∧
      CofinalDiaryStageCompatible H m f g) ↔
    ∃ B u : Nat,
      IsLeaf K u ∧ u ≤ B ∧
      (∀ a : Nat, a ∈ countableDiaryLeafPrefix H m → f a ≤ B) ∧
      HasCofinalJointOldNewLeafColour H K F f m B u := by
  constructor
  · rintro ⟨g0, P0, hOld0⟩
    let B := max (g0 m) ((countableDiaryLeafPrefix H m).sup f)
    have hmSelected : m ∈ countableDiaryLeafPrefix H (m + 1) :=
      (mem_countableDiaryLeafPrefix_iff H (m + 1) m).mpr
        ⟨hm.1, by omega, hm⟩
    have hmSupported : m ∈ countableDiaryFiniteSupport H (m + 1) :=
      mem_finiteLeafMeetSupport_leaf H
        (countableDiaryLeafPrefix H (m + 1)) m hmSelected
    have hu : IsLeaf K (g0 m) := P0.1.1.leaf_role m hmSupported hm
    have hBound : ∀ a : Nat,
        a ∈ countableDiaryLeafPrefix H m → f a ≤ B := by
      intro a ha
      exact (Finset.le_sup (f := f) ha).trans (le_max_right _ _)
    refine ⟨B, g0 m, hu, le_max_left _ _, hBound, ?_⟩
    intro N
    obtain ⟨g, Q, hKeep⟩ := P0.2 N
    have hOld : CofinalDiaryStageCompatible H m f g :=
      CofinalDiaryStageCompatible.trans (Nat.le_succ m) hOld0 hKeep
    refine ⟨N, le_rfl, g, Q, ?_, ?_⟩
    · intro a ha
      have haSupported : a ∈ countableDiaryFiniteSupport H m :=
        mem_finiteLeafMeetSupport_leaf H
          (countableDiaryLeafPrefix H m) a ha
      rw [hOld a haSupported]
    · rw [hKeep m hmSupported]
  · rintro ⟨B, u, hu, huB, hBoundOld, hRecur⟩
    exact persistent_successor_of_cofinal_joint_old_new_leaf_colour
      DK P hm hu huB hBoundOld hRecur

/-- Under absence of a persistent successor, each FIXED finite
joint old/new colour vector whose proposed new leaf is genuine and
lies below the cut has a finite death horizon: from then on, no
genuine reserved stage can match all its old/new finite colour tests.

The death horizon may depend on u and B. This is not a uniform bound
over all colours or a proof that some protected recurring fibre exists. -/
theorem no_persistent_successor_eventually_excludes_joint_finite_colour
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m B u : Nat}
    (DK : RoleDiary K)
    (P : AdmissibleCofinalDiaryStage H K F m f)
    (hm : IsLeaf H m)
    (hu : IsLeaf K u) (huB : u ≤ B)
    (hBoundOld : ∀ a : Nat,
      a ∈ countableDiaryLeafPrefix H m → f a ≤ B)
    (hNo : ¬ ∃ g : Nat → Nat,
      PersistentReservedDiaryStage H K F (m + 1) g ∧
      CofinalDiaryStageCompatible H m f g) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n → ∀ g : Nat → Nat,
      ReservedDiaryStage H K F (m + 1 + n) g →
      (∀ a : Nat, a ∈ countableDiaryLeafPrefix H m →
        DiaryLowerBoundColors.singletonColour K B (g a) =
          DiaryLowerBoundColors.singletonColour K B (f a)) →
      DiaryLowerBoundColors.singletonColour K B (g m) ≠
        DiaryLowerBoundColors.singletonColour K B u := by
  classical
  have hNot :
      ¬ HasCofinalJointOldNewLeafColour H K F f m B u := by
    intro hRecur
    exact hNo (persistent_successor_of_cofinal_joint_old_new_leaf_colour
      DK P hm hu huB hBoundOld hRecur)
  unfold HasCofinalJointOldNewLeafColour at hNot
  push_neg at hNot
  exact hNot

end DiaryLeafPriority
end ThreeUniformDiaries
