import ThreeUniformDiaries.DiaryUniformOldStageTailColour
import ThreeUniformDiaries.DiaryGenericMixedConeIndivisibility

/-!
# Track D: monochromatic mixed singleton cones cannot realize lower split meets

A complete mixed singleton colour below a finite target cut B
contains both positive and negative tests from all older marker,
one-split and two-split target vertices. If two target leaves u,v
are both at least B and share the SAME colour, then their exact
numeric singleton meet is at least B. This is an immediate but
important fact about the capped findGreatest definition.

Consequently a genuine admissible finite diary-support map whose
selected leaves lie in one B-monochromatic prescribed leaf range
cannot preserve a source one-split whose prescribed target image
lies strictly BELOW B, provided both witnessing leaf images are
at least B.

The generic mixed-colour indivisibility theorem does produce
monochromatic induced generic subcopies. It does NOT imply that
an old fixed diary support can be extended inside one such
subcopy: a fixed earlier source one-split may demand the
excluded small meet. This is a RELATIVE obstruction, not a
counterexample to unconditional diary unavoidability (the proof
may choose all split images and a suitable generic subcopy afresh).

An incidental audit simplification: the explicit old-stage cut
already equals 1 plus the maximum over the OLD COMPLETE support;
the separate old leaf supremum is redundant because every old
selected leaf belongs to the old support.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The old leaf supremum is redundant in the uniform tail cut:
selected leaves are themselves in the complete old support. -/
theorem oldStageTailCut_eq_oldSupport_sup_succ
    (H : Ordered3Graph Nat) (m : Nat) (f : Nat → Nat) :
    oldStageTailCut H m f =
      (countableDiaryFiniteSupport H m).sup f + 1 := by
  classical
  have hBound :
      (countableDiaryLeafPrefix H m).sup f ≤
        (countableDiaryFiniteSupport H m).sup f := by
    apply Finset.sup_le
    intro a ha
    exact Finset.le_sup (f := f)
      (mem_finiteLeafMeetSupport_leaf
        H (countableDiaryLeafPrefix H m) a ha)
  simp only [oldStageTailCut, max_eq_left hBound]

/-- Equality of full mixed singleton types through cut B forces
the numeric singleton meet to be at least B, provided the
vertex cap itself does not intervene before B. -/
theorem sameOneTypeBelow_forces_oneMeet_ge_cut
    (K : Ordered3Graph Nat) (B u v : Nat)
    (hBu : B ≤ u) (hBv : B ≤ v)
    (hSame : K.SameOneTypeBelow B u v) :
    B ≤ K.oneMeetLevel u v := by
  classical
  exact Nat.le_findGreatest (le_min hBu hBv) hSame

/-- The same exact numeric lower bound, using the existing
complete finite Boolean singleton-colour API. -/
theorem equal_singletonColour_forces_oneMeet_ge_cut
    (K : Ordered3Graph Nat) (B u v : Nat)
    (hBu : B ≤ u) (hBv : B ≤ v)
    (hEqual :
      DiaryLowerBoundColors.singletonColour K B u =
        DiaryLowerBoundColors.singletonColour K B v) :
    B ≤ K.oneMeetLevel u v := by
  exact sameOneTypeBelow_forces_oneMeet_ge_cut K B u v
    hBu hBv
    ((DiaryLowerBoundColors.singletonColour_eq_iff K B u v).mp hEqual)

/-- Any genuine finite diary stage with two selected source
leaves in a single B-monochromatic prescribed F-range must send
their exact singleton meet to a target index AT LEAST B,
as long as both target leaf indices are themselves at least B.

There is no assumption that the outer leaf map F is ordered;
its range hypothesis is provided by the actual stage. -/
theorem AdmissibleCofinalDiaryStage.monochromatic_leaf_range_meet_ge_cut
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m B a b : Nat}
    (Q : AdmissibleCofinalDiaryStage H K F m f)
    (ha : a ∈ countableDiaryFiniteSupport H m)
    (hb : b ∈ countableDiaryFiniteSupport H m)
    (hLa : IsLeaf H a) (hLb : IsLeaf H b)
    (hBa : B ≤ f a) (hBb : B ≤ f b)
    (hMono : ∃ c : Fin B → Fin B → Bool,
      ∀ t : Nat,
        DiaryLowerBoundColors.singletonColour K B (F t) = c) :
    B ≤ f (H.oneMeetLevel a b) := by
  obtain ⟨c, hCol⟩ := hMono
  obtain ⟨ta, hA⟩ := Q.leaf_range a ha hLa
  obtain ⟨tb, hB⟩ := Q.leaf_range b hb hLb
  have hEqual :
      DiaryLowerBoundColors.singletonColour K B (f a) =
        DiaryLowerBoundColors.singletonColour K B (f b) := by
    calc
      DiaryLowerBoundColors.singletonColour K B (f a) =
          DiaryLowerBoundColors.singletonColour K B (F ta) :=
        congrArg (DiaryLowerBoundColors.singletonColour K B) hA
      _ = c := hCol ta
      _ = DiaryLowerBoundColors.singletonColour K B (F tb) :=
        (hCol tb).symm
      _ = DiaryLowerBoundColors.singletonColour K B (f b) :=
        congrArg (DiaryLowerBoundColors.singletonColour K B) hB.symm
  have hLower : B ≤ K.oneMeetLevel (f a) (f b) :=
    equal_singletonColour_forces_oneMeet_ge_cut
      K B (f a) (f b) hBa hBb hEqual
  rw [Q.leaf_oneMeet a b ha hb hLa hLb] at hLower
  exact hLower

/-- Explicit impossibility of a relative finite diary stage
with two old leaves above B but their required split image below B
inside a B-monochromatic prescribed leaf range. -/
theorem AdmissibleCofinalDiaryStage.no_small_meet_in_monochromatic_leaf_range
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m B a b : Nat}
    (Q : AdmissibleCofinalDiaryStage H K F m f)
    (ha : a ∈ countableDiaryFiniteSupport H m)
    (hb : b ∈ countableDiaryFiniteSupport H m)
    (hLa : IsLeaf H a) (hLb : IsLeaf H b)
    (hBa : B ≤ f a) (hBb : B ≤ f b)
    (hMono : ∃ c : Fin B → Fin B → Bool,
      ∀ t : Nat,
        DiaryLowerBoundColors.singletonColour K B (F t) = c)
    (hSmall : f (H.oneMeetLevel a b) < B) :
    False := by
  have hLarge := Q.monochromatic_leaf_range_meet_ge_cut
    ha hb hLa hLb hBa hBb hMono
  omega

/-- In a genuine full diary, TWO distinct target leaves necessarily
have different complete mixed singleton colours already at the cut
min(a,b). Their numeric meet is a genuine one-split strictly
below both leaf vertices, by S1 and role disjointness. -/
theorem RoleDiary.distinct_leaves_have_different_colour_at_min
    {K : Ordered3Graph Nat} (DK : RoleDiary K)
    (a b : Nat) (ha : IsLeaf K a) (hb : IsLeaf K b)
    (hne : a ≠ b) :
    DiaryLowerBoundColors.singletonColour K (min a b) a ≠
      DiaryLowerBoundColors.singletonColour K (min a b) b := by
  intro hEqual
  have hs : IsOneSplit K (K.oneMeetLevel a b) :=
    DK.singleton_meets a b ha hb hne
  have hCap : K.oneMeetLevel a b ≤ min a b :=
    K.oneMeetLevel_le_min a b
  have hNeA : K.oneMeetLevel a b ≠ a := by
    intro he
    have hSplit : IsOneSplit K a := by simpa only [he] using hs
    exact ha.2.1 hSplit.2.1
  have hNeB : K.oneMeetLevel a b ≠ b := by
    intro he
    have hSplit : IsOneSplit K b := by simpa only [he] using hs
    exact hb.2.1 hSplit.2.1
  have hStrict : K.oneMeetLevel a b < min a b := by
    have haLe := hCap.trans (min_le_left a b)
    have hbLe := hCap.trans (min_le_right a b)
    omega
  have hType : K.SameOneTypeBelow (min a b) a b :=
    (DiaryLowerBoundColors.singletonColour_eq_iff K (min a b) a b).mp hEqual
  have hLower : min a b ≤ K.oneMeetLevel a b := by
    classical
    exact Nat.le_findGreatest (le_refl _) hType
  omega

/-- A complete countable mixed singleton type, even if all
its finite prefixes are realizable, has AT MOST ONE realizing
genuine target diary leaf. Saturation or a nested all-cut
monochromatic generic copy cannot be inferred from finite
Ramsey monochromatizations. -/
theorem RoleDiary.full_singleton_colour_type_unique_on_leaves
    {K : Ordered3Graph Nat} (DK : RoleDiary K)
    (a b : Nat) (ha : IsLeaf K a) (hb : IsLeaf K b)
    (hAll : ∀ B : Nat,
      DiaryLowerBoundColors.singletonColour K B a =
        DiaryLowerBoundColors.singletonColour K B b) :
    a = b := by
  by_contra hne
  exact DK.distinct_leaves_have_different_colour_at_min
    a b ha hb hne (hAll (min a b))

end DiaryLeafPriority
end ThreeUniformDiaries
