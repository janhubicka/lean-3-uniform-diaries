import ThreeUniformDiaries.DiaryExactSingletonColourSplitCut
import ThreeUniformDiaries.DiaryMonochromaticLeafMeetObstruction

/-!
# Track C: exact supported-leaf singleton colours force exact split images

English-first proof and adversarial audit:
  janhubicka/3-uniform-diaries PR #276
  notes/track_c_relative_singleton_colour_exact_split_obstruction_20261110.md

For a genuine admissible finite diary stage into a FULL target RoleDiary,
any two distinct ordered supported SOURCE leaves have identical target
mixed singleton colours below B IFF their forced image of the numerical
S1 meet is >= B. No separate lower bounds on the two target leaf
positions are required; they follow from the colour equality itself.

This strictly sharpens the earlier monochromatic leaf-range obstruction
only under the explicit full-target-diary hypothesis. No persistent
relative successor or countable unavoidability is constructed.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The exact singleton-colour cutoff for two ordered supported source
leaves inside a real admissible stage. The target is a FULL RoleDiary,
and the source leaves are distinct and ordered a<b.

The stage's exact numeric S1 preservation moves the entire
type/meet equivalence from target leaves back to the SOURCE split. -/
theorem AdmissibleCofinalDiaryStage.supported_leaf_colour_eq_iff_meet_ge
    {H K : Ordered3Graph Nat} {F f : Nat → Nat}
    {m B a b : Nat}
    (DK : RoleDiary K)
    (Q : AdmissibleCofinalDiaryStage H K F m f)
    (ha : a ∈ countableDiaryFiniteSupport H m)
    (hb : b ∈ countableDiaryFiniteSupport H m)
    (hLa : IsLeaf H a) (hLb : IsLeaf H b)
    (hab : a < b) :
    (DiaryLowerBoundColors.singletonColour K B (f a) =
      DiaryLowerBoundColors.singletonColour K B (f b)) ↔
      B ≤ f (H.oneMeetLevel a b) := by
  have hTargetA : IsLeaf K (f a) :=
    Q.leaf_role a ha hLa
  have hTargetB : IsLeaf K (f b) :=
    Q.leaf_role b hb hLb
  have hNe : f a ≠ f b :=
    ne_of_lt (Q.ordered a b ha hb hab)
  have hCut :=
    DK.singletonColour_eq_iff_cut_le_oneMeet
      hTargetA hTargetB hNe B
  simpa only [Q.leaf_oneMeet a b ha hb hLa hLb] using hCut

/-- In a prescribed B-monochromatic complete singleton-type range,
ALL supported ordered source-leaf pairs must have their source
singleton meets mapped to target levels >= B.

No assumptions B<=f(a), B<=f(b) are needed, unlike the earlier
arbitrary-target obstruction. Full RoleDiary K is essential. -/
theorem AdmissibleCofinalDiaryStage.monochromatic_range_meet_ge_no_leaf_bounds
    {H K : Ordered3Graph Nat} {F f : Nat → Nat}
    {m B a b : Nat}
    (DK : RoleDiary K)
    (Q : AdmissibleCofinalDiaryStage H K F m f)
    (ha : a ∈ countableDiaryFiniteSupport H m)
    (hb : b ∈ countableDiaryFiniteSupport H m)
    (hLa : IsLeaf H a) (hLb : IsLeaf H b)
    (hab : a < b)
    (hMono : ∃ c : Fin B → Fin B → Bool,
      ∀ t : Nat,
        DiaryLowerBoundColors.singletonColour K B (F t) = c) :
    B ≤ f (H.oneMeetLevel a b) := by
  obtain ⟨c, hCol⟩ := hMono
  obtain ⟨ta, hFa⟩ := Q.leaf_range a ha hLa
  obtain ⟨tb, hFb⟩ := Q.leaf_range b hb hLb
  have hEq :
      DiaryLowerBoundColors.singletonColour K B (f a) =
        DiaryLowerBoundColors.singletonColour K B (f b) := by
    calc
      DiaryLowerBoundColors.singletonColour K B (f a) =
          DiaryLowerBoundColors.singletonColour K B (F ta) :=
        congrArg (DiaryLowerBoundColors.singletonColour K B) hFa
      _ = c := hCol ta
      _ = DiaryLowerBoundColors.singletonColour K B (F tb) :=
        (hCol tb).symm
      _ = DiaryLowerBoundColors.singletonColour K B (f b) :=
        congrArg (DiaryLowerBoundColors.singletonColour K B) hFb.symm
  exact (Q.supported_leaf_colour_eq_iff_meet_ge
    DK ha hb hLa hLb hab).mp hEq

/-- An already fixed source one-split image BELOW B makes
a full-target-diary supported stage in a B-monochromatic
prescribed leaf range impossible, with no target leaf lower
bound hypotheses. This is a RELATIVE obstruction only. -/
theorem AdmissibleCofinalDiaryStage.no_small_meet_in_monochromatic_range
    {H K : Ordered3Graph Nat} {F f : Nat → Nat}
    {m B a b : Nat}
    (DK : RoleDiary K)
    (Q : AdmissibleCofinalDiaryStage H K F m f)
    (ha : a ∈ countableDiaryFiniteSupport H m)
    (hb : b ∈ countableDiaryFiniteSupport H m)
    (hLa : IsLeaf H a) (hLb : IsLeaf H b)
    (hab : a < b)
    (hMono : ∃ c : Fin B → Fin B → Bool,
      ∀ t : Nat,
        DiaryLowerBoundColors.singletonColour K B (F t) = c)
    (hSmall : f (H.oneMeetLevel a b) < B) : False := by
  have hLarge :=
    Q.monochromatic_range_meet_ge_no_leaf_bounds
      DK ha hb hLa hLb hab hMono
  omega

end DiaryLeafPriority
end ThreeUniformDiaries
