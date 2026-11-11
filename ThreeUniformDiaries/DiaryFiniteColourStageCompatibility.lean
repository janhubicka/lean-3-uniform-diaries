import ThreeUniformDiaries.DiaryPersistentFiniteColourIsolation
import ThreeUniformDiaries.DiaryLeafGeneratedStageCompatibility
import ThreeUniformDiaries.DiaryProtectedS2FinitePairColour

/-!
# Track A: one finite mixed-colour cut rigidifies an entire old diary stage

In a full target RoleDiary, the complete singleton colour at a cut B
identifies a genuine leaf u uniquely once B is at least u. The already
certified selected-leaf generator lemma then implies that, between TWO
genuine admissible stage maps, equality of the finitely many old-leaf
colours at one B dominating the first map's selected-leaf images is
EQUIVALENT to literal agreement on the entire old S1/S2 meet support.

Taking B to be the supremum of the finitely many old leaf images gives
an explicit finite compatibility certificate with NO free cut parameter.
This is a recognition/reduction lemma, NOT existence of any such later
stage, a persistent successor, or the countable diary Ramsey theorem.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- At any cut B at least the position of a genuine target leaf u, its
one finite mixed singleton mask isolates u among all genuine leaves.
Only u, not the competing leaf v, must lie below B. -/
theorem RoleDiary.singletonColour_eq_iff_leaf_eq_above_self
    {K : Ordered3Graph Nat} (DK : RoleDiary K)
    {u v B : Nat} (hu : IsLeaf K u) (hv : IsLeaf K v)
    (huB : u ≤ B) :
    DiaryLowerBoundColors.singletonColour K B u =
      DiaryLowerBoundColors.singletonColour K B v ↔ u = v := by
  constructor
  · intro hColour
    have hType : K.SameOneTypeBelow B u v :=
      (DiaryLowerBoundColors.singletonColour_eq_iff K B u v).mp hColour
    have hAtU : K.SameOneTypeBelow u u v := by
      intro x y hxy hy
      exact hType hxy (lt_of_lt_of_le hy huB)
    have hSmall :
        DiaryLowerBoundColors.singletonColour K u u =
          DiaryLowerBoundColors.singletonColour K u v :=
      (DiaryLowerBoundColors.singletonColour_eq_iff K u u v).mpr hAtU
    exact (DK.singletonColour_self_cut_isolates_leaf u v hu hv).mp hSmall
  · rintro rfl
    rfl

/-- An entire ordered pair of genuine leaves is determined by ONE
finite complete pair-type colour, provided the cut dominates both
coordinates of the first pair. No orderedness of the competing pair
and no cut bound on the competing coordinates is needed. -/
theorem RoleDiary.fullTwoTypeColour_eq_iff_leaf_pair_eq_above_self
    {K : Ordered3Graph Nat} (DK : RoleDiary K)
    {u₀ u₁ v₀ v₁ B : Nat}
    (hu₀ : IsLeaf K u₀) (hu₁ : IsLeaf K u₁)
    (hv₀ : IsLeaf K v₀) (hv₁ : IsLeaf K v₁)
    (hB₀ : u₀ ≤ B) (hB₁ : u₁ ≤ B) :
    fullTwoTypeColour K B u₀ u₁ =
      fullTwoTypeColour K B v₀ v₁ ↔
      u₀ = v₀ ∧ u₁ = v₁ := by
  constructor
  · intro hColour
    have h₀ :
        DiaryLowerBoundColors.singletonColour K B u₀ =
          DiaryLowerBoundColors.singletonColour K B v₀ :=
      congrArg (fun z => z.1.1) hColour
    have h₁ :
        DiaryLowerBoundColors.singletonColour K B u₁ =
          DiaryLowerBoundColors.singletonColour K B v₁ :=
      congrArg (fun z => z.1.2) hColour
    exact ⟨(DK.singletonColour_eq_iff_leaf_eq_above_self
      hu₀ hv₀ hB₀).mp h₀,
      (DK.singletonColour_eq_iff_leaf_eq_above_self
        hu₁ hv₁ hB₁).mp h₁⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- For two ACTUAL admissible maps on the SAME old support, literal
compatibility is equivalent to matching the complete singleton
colours of every selected old leaf at ONE fixed cut B, as soon as B
dominates the first map's finitely many old leaf images.

All split images follow from the exact S1 and S2 generator equations.
This is not an existence or no-escape theorem. -/
theorem AdmissibleCofinalDiaryStage.compatible_iff_leaf_colour_at_cut
    {H K : Ordered3Graph Nat} {F f g : Nat → Nat} {m B : Nat}
    (DK : RoleDiary K)
    (P : AdmissibleCofinalDiaryStage H K F m f)
    (Q : AdmissibleCofinalDiaryStage H K F m g)
    (hBound : ∀ a : Nat,
      a ∈ countableDiaryLeafPrefix H m → f a ≤ B) :
    CofinalDiaryStageCompatible H m f g ↔
      (∀ a : Nat, a ∈ countableDiaryLeafPrefix H m →
        DiaryLowerBoundColors.singletonColour K B (g a) =
          DiaryLowerBoundColors.singletonColour K B (f a)) := by
  constructor
  · intro hCompat a ha
    have haS : a ∈ countableDiaryFiniteSupport H m :=
      mem_finiteLeafMeetSupport_leaf H
        (countableDiaryLeafPrefix H m) a ha
    rw [hCompat a haS]
  · intro hColours
    have hLeaves : ∀ a : Nat,
        a ∈ countableDiaryLeafPrefix H m → f a = g a := by
      intro a ha
      have haS : a ∈ countableDiaryFiniteSupport H m :=
        mem_finiteLeafMeetSupport_leaf H
          (countableDiaryLeafPrefix H m) a ha
      have haLeaf : IsLeaf H a :=
        ((mem_countableDiaryLeafPrefix_iff H m a).mp ha).2.2
      have hfLeaf : IsLeaf K (f a) := P.leaf_role a haS haLeaf
      have hgLeaf : IsLeaf K (g a) := Q.leaf_role a haS haLeaf
      exact (DK.singletonColour_eq_iff_leaf_eq_above_self
        hfLeaf hgLeaf (hBound a ha)).mp (hColours a ha).symm
    intro x hx
    exact (P.eq_on_support_of_selected_leaves Q hLeaves x hx).symm

/-- A genuine later stage can be certified to preserve EVERY old
supported vertex using finite mixed colours on old selected leaves
only; S1/S2 split preservation is automatic. -/
theorem AdmissibleCofinalDiaryStage.successor_compatible_iff_leaf_colour_at_cut
    {H K : Ordered3Graph Nat} {F f g : Nat → Nat} {m B : Nat}
    (DK : RoleDiary K)
    (P : AdmissibleCofinalDiaryStage H K F m f)
    (Q : AdmissibleCofinalDiaryStage H K F (m + 1) g)
    (hBound : ∀ a : Nat,
      a ∈ countableDiaryLeafPrefix H m → f a ≤ B) :
    CofinalDiaryStageCompatible H m f g ↔
      (∀ a : Nat, a ∈ countableDiaryLeafPrefix H m →
        DiaryLowerBoundColors.singletonColour K B (g a) =
          DiaryLowerBoundColors.singletonColour K B (f a)) := by
  exact P.compatible_iff_leaf_colour_at_cut DK
    (Q.restrict (Nat.le_succ m)) hBound

/-- Canonical finite code: take B to be the numerical maximum of
the old selected-leaf images (zero if there are none). Then exactly
one cut suffices to test preservation of the entire old support. -/
theorem AdmissibleCofinalDiaryStage.successor_compatible_iff_colour_at_old_leaf_sup
    {H K : Ordered3Graph Nat} {F f g : Nat → Nat} {m : Nat}
    (DK : RoleDiary K)
    (P : AdmissibleCofinalDiaryStage H K F m f)
    (Q : AdmissibleCofinalDiaryStage H K F (m + 1) g) :
    CofinalDiaryStageCompatible H m f g ↔
      (∀ a : Nat, a ∈ countableDiaryLeafPrefix H m →
        DiaryLowerBoundColors.singletonColour K
            ((countableDiaryLeafPrefix H m).sup f) (g a) =
          DiaryLowerBoundColors.singletonColour K
            ((countableDiaryLeafPrefix H m).sup f) (f a)) := by
  exact P.successor_compatible_iff_leaf_colour_at_cut DK Q
    (fun a ha => Finset.le_sup (f := f) ha)

end DiaryLeafPriority
end ThreeUniformDiaries
