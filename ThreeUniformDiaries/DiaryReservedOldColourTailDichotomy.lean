import ThreeUniformDiaries.DiaryUniformOldStageTailColour
import ThreeUniformDiaries.DiaryFiniteLeafMeetSupport

/-!
# Track C: each fixed old-cut mixed colour is eventually all-good or empty

English proof and adversarial audit:
  janhubicka/3-uniform-diaries PR #313

Fix a true next source diary leaf m and the old support map f.
The previously checked oldStageTailCut H m f is a cut chosen
BEFORE any proposed new target leaf. Every actual old-compatible
reserved successor has all supported images other than its new
leaf below that old-stage-fixed cut.

By the checked exact reserved tail replacement theorem, within
ONE complete mixed singleton-colour class at that cut, existence
of ANY genuine compatible reserved next leaf v implies that
EVERY numerically later genuine leaf w of the ORIGINAL prescribed
F-range with the same colour also is a compatible reserved
next leaf (replace only the new image m).

Thus a complete old-cut colour fibre is either Good-empty or
eventually ALL of its sufficiently late true F-range leaves
are valid immediate reserved successors. This does NOT assert
the colour class is unbounded or contains a generic copy, nor
that the particular generic Ramsey-winning colour contains
a compatible successor, nor persistence through future horizons.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Every element of the canonical finite leaf-meet support S_m
lies STRICTLY below m when m≥3. Markers are <3≤m, selected leaves
are <m by definition, and all S1/S2 generator meets are capped by
some selected old leaf. No full diary axioms are required. -/
theorem countableDiaryFiniteSupport_lt_cut
    (H : Ordered3Graph Nat) (m u : Nat) (hm3 : 3 ≤ m)
    (hu : u ∈ countableDiaryFiniteSupport H m) :
    u < m := by
  classical
  let L := countableDiaryLeafPrefix H m
  have hLeafBound (a : Nat) (ha : a ∈ L) : a < m :=
    ((mem_countableDiaryLeafPrefix_iff H m a).mp ha).2.1
  change u ∈ (Finset.range 3 ∪ L) ∪
    (finiteOneMeetSupport H L ∪ finiteTwoMeetSupport H L) at hu
  rcases Finset.mem_union.mp hu with hFront | hMeets
  · rcases Finset.mem_union.mp hFront with hMarker | hLeaf
    · have hu3 : u < 3 := Finset.mem_range.mp hMarker
      omega
    · exact hLeafBound u hLeaf
  · rcases Finset.mem_union.mp hMeets with hOne | hTwo
    · change u ∈ ((L.product L).filter
          (fun p : Nat × Nat => p.1 ≠ p.2)).image
            (fun p : Nat × Nat => H.oneMeetLevel p.1 p.2) at hOne
      obtain ⟨⟨a,b⟩, hp, hEq⟩ := Finset.mem_image.mp hOne
      obtain ⟨hp,_hNe⟩ := Finset.mem_filter.mp hp
      obtain ⟨ha,_hb⟩ := Finset.mem_product.mp hp
      have hCap : H.oneMeetLevel a b ≤ a :=
        (H.oneMeetLevel_le_min a b).trans (min_le_left _ _)
      rw [← hEq]
      exact lt_of_le_of_lt hCap (hLeafBound a ha)
    · change u ∈
        ((finiteOrderedLeafPairs L).product
          (finiteOrderedLeafPairs L)).image
          (fun p : (Nat × Nat) × (Nat × Nat) =>
            H.twoMeetLevel p.1.1 p.1.2 p.2.1 p.2.2) at hTwo
      obtain ⟨⟨⟨a,b⟩,⟨c,d⟩⟩, hp, hEq⟩ :=
        Finset.mem_image.mp hTwo
      obtain ⟨hAB,_hCD⟩ := Finset.mem_product.mp hp
      obtain ⟨hAB,_hab⟩ := Finset.mem_filter.mp hAB
      obtain ⟨ha,_hb⟩ := Finset.mem_product.mp hAB
      have hCap : H.twoMeetLevel a b c d ≤ a :=
        (H.twoMeetLevel_le_min a b c d).trans (min_le_left _ _)
      rw [← hEq]
      exact lt_of_le_of_lt hCap (hLeafBound a ha)

/-- An actual RESERVED next source-leaf stage with all old S_m images
literally unchanged and new leaf image v. This is stronger than
an arbitrary candidate table, and weaker than finite-horizon
persistence. -/
def HasCompatibleReservedNextLeaf
    (H K : Ordered3Graph Nat) (F f : Nat → Nat)
    (m v : Nat) : Prop :=
  ∃ g : Nat → Nat,
    ReservedDiaryStage H K F (m + 1) g ∧
    CofinalDiaryStageCompatible H m f g ∧ g m = v

/-- In one COMPLETE mixed singleton colour at the old-stage-fixed cut,
actual compatible reserved next-leaf images are UPWARD CLOSED along
true target leaves of the original F-range.

This includes preservation of all roles, edges AND nonedges,
numerical S1/S2 meets, support images and future quantitative
order reserve. The new next image w must be >= the old valid v.
No target full RoleDiary or genericity is needed. -/
theorem compatible_reserved_nextLeaf_tail_of_oldCut_colour
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m v w : Nat}
    (hm : IsLeaf H m)
    (hGood : HasCompatibleReservedNextLeaf H K F f m v)
    (hvw : v ≤ w)
    (hwLeaf : IsLeaf K w)
    (hwRange : ∃ t : Nat, w = F t)
    (hColour :
      DiaryLowerBoundColors.singletonColour K
        (oldStageTailCut H m f) v =
      DiaryLowerBoundColors.singletonColour K
        (oldStageTailCut H m f) w) :
    HasCompatibleReservedNextLeaf H K F f m w := by
  obtain ⟨g, Q, hCompat, hAtM⟩ := hGood
  have hColourAtG :
      DiaryLowerBoundColors.singletonColour K
          (oldStageTailCut H m f) (g m) =
        DiaryLowerBoundColors.singletonColour K
          (oldStageTailCut H m f) w := by
    simpa only [hAtM] using hColour
  have hType :
      K.SameOneTypeBelow (oldStageTailCut H m f) (g m) w :=
    (DiaryLowerBoundColors.singletonColour_eq_iff
      K (oldStageTailCut H m f) (g m) w).mp hColourAtG
  have hvLater : g m ≤ w := by
    simpa only [hAtM] using hvw
  have hNewStage :
      ReservedDiaryStage H K F (m + 1) (replaceAt g m w) :=
    ReservedDiaryStage.replace_new_leaf_of_old_stage_type
      hm Q hCompat hType hvLater hwLeaf hwRange
  refine ⟨replaceAt g m w, hNewStage, ?_, replaceAt_eq g m w⟩
  intro x hx
  have hxLt : x < m :=
    countableDiaryFiniteSupport_lt_cut H m x hm.1 hx
  have hxNe : x ≠ m := ne_of_lt hxLt
  exact (replaceAt_other g m w x hxNe).trans (hCompat x hx)

/-- Exact quantifier-level dichotomy, FOR EACH finite full mixed
singleton colour c at B=oldStageTailCut H m f:

Either no compatible reserved immediate successor has colour c,
OR beyond one finite numerical threshold EVERY genuine F-range
leaf of colour c admits an actual old-compatible reserved
immediate successor.

The conclusion does NOT say there are ANY colour-c leaves beyond
the threshold: the colour class may be numerically bounded or
contain no generic induced subcopy. Nor is a persistent image
through future source horizons asserted. -/
theorem compatible_reserved_nextLeaf_colour_fibre_all_or_none
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m : Nat}
    (hm : IsLeaf H m)
    (c : Fin (oldStageTailCut H m f) →
      Fin (oldStageTailCut H m f) → Bool) :
    (∀ v : Nat, HasCompatibleReservedNextLeaf H K F f m v →
      DiaryLowerBoundColors.singletonColour K
        (oldStageTailCut H m f) v ≠ c) ∨
    (∃ T : Nat, ∀ w : Nat, T ≤ w →
      IsLeaf K w → (∃ t : Nat, w = F t) →
      DiaryLowerBoundColors.singletonColour K
        (oldStageTailCut H m f) w = c →
      HasCompatibleReservedNextLeaf H K F f m w) := by
  classical
  by_cases hAnchor : ∃ v : Nat,
      HasCompatibleReservedNextLeaf H K F f m v ∧
      DiaryLowerBoundColors.singletonColour K
        (oldStageTailCut H m f) v = c
  · obtain ⟨v,hGood,hCol⟩ := hAnchor
    refine Or.inr ⟨v, ?_⟩
    intro w hw hwLeaf hwRange hwColour
    exact compatible_reserved_nextLeaf_tail_of_oldCut_colour
      hm hGood hw hwLeaf hwRange (hCol.trans hwColour.symm)
  · apply Or.inl
    intro v hGood hColour
    exact hAnchor ⟨v,hGood,hColour⟩

end DiaryLeafPriority
end ThreeUniformDiaries
