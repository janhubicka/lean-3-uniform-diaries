import ThreeUniformDiaries.DiaryGenericProfileColourGoodAnchorBridge
import ThreeUniformDiaries.DiaryGenericOldStageRequiredE5Copy
import ThreeUniformDiaries.DiaryGenericCompleteOneNewS1S2

/-!
# Track A: SOURCE E5 and full target S1/S2 profiles at the ACTUAL old-stage cut

English-first adversarial audit: janhubicka/3-uniform-diaries PR #329.

CRITICAL exact-cut repair: the earlier source E5 generic profile theorem
homogenizes at 1+sup f[old selected leaves], whereas the verified
reserved old-colour saturation theorem uses oldStageTailCut H m f,
which also includes the entire old meet/marker support. These cuts
must NOT be identified without a proof.

Here the generic E5 reservoir J is fixed first, then the already
validated uniform complete S1 and BOTH S2 numerical profile theorem
is applied INSIDE J at Cut=oldStageTailCut H m f. The required
strict W.sup < Cut follows from the finite image W=f[L] and the
definition of the old support max, with NO assumption L.Nonempty.

The second theorem applies the verified exact reserved colour
all-or-none bridge to the SAME generic J, c, and full E5/S1/S2
profile. Either the selected colour has no actual compatible
reserved immediate successor anywhere, or every sufficiently late
selected whole generic cone consists of actual reserved immediate
next-leaf images, retaining all numerical profiles and E5 bits.
No good anchor is produced, and no fixed new leaf is claimed
to survive subsequent source horizons.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The corrected joint SOURCE-required E5 and complete target S1
and both S2 numeric generic profile theorem at precisely the cut
required by the reserved next-leaf colour dichotomy.

The profiles p, q, r are existential TARGET selections; source
generator compatibility and future-stage persistence are NOT
asserted. The original F and constructed J are unordered induced
embeddings, never assumed numerically increasing. -/
theorem RoleDiary.exists_uniform_source_E5_generic_full_oldCut_S1_S2_cones
    {H K : Ordered3Graph Nat} (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    {m : Nat} (f : Nat → Nat)
    (P : ReservedDiaryStage H K F m f) :
    let L := countableDiaryLeafPrefix H m
    let W := L.image f
    let Cut := oldStageTailCut H m f
    ∃ J : Ordered3Graph.UnorderedEmbedding G.graph K,
      (∀ t : Nat, IsLeaf K (J t) ∧
        (∃ i : Nat, J t = F i) ∧
        (∀ a b : Nat, a ∈ L → b ∈ L → a < b →
          (H.edge a b m ↔ K.edge (f a) (f b) (J t)))) ∧
      ∃ c : Fin Cut → Fin Cut → Bool,
        ∃ p : FiniteRootMeetProfile W,
          ∃ q : FiniteRootCrossPairMeetProfile W,
            ∃ r : FiniteRootNewNewPairMeetProfile W,
              (∀ w : {w : Nat // w ∈ W},
                IsOneSplit K (p w).val ∧ (p w).val < w.val) ∧
              (∀ ab : {ab : Nat × Nat // ab ∈ finiteOrderedLeafPairs W},
                ∀ w : {w : Nat // w ∈ W},
                  (q ab w).val = min ab.val.1 w.val ∨
                  (q ab w).val = 1 ∨ IsTwoSplit K (q ab w).val) ∧
              (∀ ab : {ab : Nat × Nat // ab ∈ finiteOrderedLeafPairs W},
                (r ab).val = min ab.val.1 ab.val.2 ∨
                (r ab).val = 1 ∨ IsTwoSplit K (r ab).val) ∧
              (∀ M : Nat,
                ∃ u : Ordered3Graph.Embedding G.graph G.graph,
                  u.AuxTypeRespecting ∧
                  ∀ t : Nat,
                    M < J (u t) ∧
                    DiaryLowerBoundColors.singletonColour K Cut (J (u t)) = c ∧
                    (∀ a b : Nat, a ∈ L → b ∈ L → a < b →
                      (H.edge a b m ↔ K.edge (f a) (f b) (J (u t)))) ∧
                    (∀ w : {w : Nat // w ∈ W},
                      K.oneMeetLevel w.val (J (u t)) = (p w).val) ∧
                    (∀ ab : {ab : Nat × Nat //
                        ab ∈ finiteOrderedLeafPairs W},
                      ∀ w : {w : Nat // w ∈ W},
                        K.twoMeetLevel ab.val.1 ab.val.2
                          w.val (J (u t)) = (q ab w).val) ∧
                    (∀ ab : {ab : Nat × Nat //
                        ab ∈ finiteOrderedLeafPairs W},
                      K.twoMeetLevel ab.val.1 (J (u t))
                        ab.val.2 (J (u t)) = (r ab).val)) := by
  classical
  let L := countableDiaryLeafPrefix H m
  let W := L.image f
  let Cut := oldStageTailCut H m f
  obtain ⟨J, hRange, hE5⟩ :=
    ReservedDiaryStage.exists_generic_leaf_subcopy_realizing_all_required_old_E5
      G F hFLeaf f P 0
  have hJLeaves (t : Nat) : IsLeaf K (J t) :=
    (hRange t).2.1
  have hRoots (w : Nat) (hw : w ∈ W) : IsLeaf K w := by
    obtain ⟨a, ha, hfa⟩ := Finset.mem_image.mp hw
    have haSupport : a ∈ countableDiaryFiniteSupport H m :=
      mem_finiteLeafMeetSupport_leaf H L a ha
    have haLeaf : IsLeaf H a :=
      ((mem_countableDiaryLeafPrefix_iff H m a).mp ha).2.2
    have hLeaf := P.1.leaf_role a haSupport haLeaf
    simpa only [hfa] using hLeaf
  have hWsup :
      W.sup (fun w : Nat => w) ≤ L.sup f := by
    apply Finset.sup_le
    intro w hw
    obtain ⟨a, ha, hfa⟩ := Finset.mem_image.mp hw
    rw [← hfa]
    exact Finset.le_sup (f := f) ha
  have hWCut : W.sup (fun w : Nat => w) < Cut := by
    change W.sup (fun w : Nat => w) <
      max ((countableDiaryFiniteSupport H m).sup f)
          ((countableDiaryLeafPrefix H m).sup f) + 1
    exact lt_of_le_of_lt
      (hWsup.trans (le_max_right _ _)) (Nat.lt_succ_self _)
  obtain ⟨c, p, q, r, hOne, hCross, hNewNew, hAll⟩ :=
    DK.exists_uniform_generic_complete_oneNew_S1_S2_profiles
      G J hJLeaves W hRoots Cut hWCut
  refine ⟨J, ?_, c, p, q, r, hOne, hCross, hNewNew, ?_⟩
  · intro t
    obtain ⟨_hHigh, hLeaf, t₀, hAtF⟩ := hRange t
    exact ⟨hLeaf, ⟨t₀, hAtF⟩, hE5 t⟩
  · intro M
    obtain ⟨u, hu, hCopy⟩ := hAll M
    refine ⟨u, hu, ?_⟩
    intro t
    obtain ⟨hHigh, _hLeaf, hColour, hOneMeet, hCrossMeet, hNewMeet⟩ :=
      hCopy t
    exact ⟨hHigh, hColour, hE5 (u t),
      hOneMeet, hCrossMeet, hNewMeet⟩

/-- Instantiation of the exact old-cut generic-profile good-anchor bridge:
one ACTUAL fixed old reserved stage P gives a source-required E5
generic leaf copy J and selected complete target numeric S1/S2
profiles at the SAME oldStageTailCut used by reserved successors.

Either the selected full colour c is globally incompatible with
any genuine reserved next leaf, or for every M there is ONE whole
generic J-subcopy above M whose EVERY vertex retains all selected
source-required E5 and exact p/q/r target meet values and is an
ACTUAL compatible reserved immediate next-leaf image.

This is a sharp conditional conclusion: it neither finds a good
source-compatible anchor nor proves all-future-horizon persistence. -/
theorem RoleDiary.exists_source_E5_full_oldCut_generic_cones_good_or_no_anchor
    {H K : Ordered3Graph Nat} (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    {m : Nat} (hm : IsLeaf H m) (f : Nat → Nat)
    (P : ReservedDiaryStage H K F m f) :
    let L := countableDiaryLeafPrefix H m
    let W := L.image f
    let Cut := oldStageTailCut H m f
    ∃ J : Ordered3Graph.UnorderedEmbedding G.graph K,
      (∀ t : Nat, IsLeaf K (J t) ∧
        (∃ i : Nat, J t = F i) ∧
        (∀ a b : Nat, a ∈ L → b ∈ L → a < b →
          (H.edge a b m ↔ K.edge (f a) (f b) (J t)))) ∧
      ∃ c : Fin Cut → Fin Cut → Bool,
        ∃ p : FiniteRootMeetProfile W,
          ∃ q : FiniteRootCrossPairMeetProfile W,
            ∃ r : FiniteRootNewNewPairMeetProfile W,
              (∀ w : {w : Nat // w ∈ W},
                IsOneSplit K (p w).val ∧ (p w).val < w.val) ∧
              (∀ ab : {ab : Nat × Nat // ab ∈ finiteOrderedLeafPairs W},
                ∀ w : {w : Nat // w ∈ W},
                  (q ab w).val = min ab.val.1 w.val ∨
                  (q ab w).val = 1 ∨ IsTwoSplit K (q ab w).val) ∧
              (∀ ab : {ab : Nat × Nat // ab ∈ finiteOrderedLeafPairs W},
                (r ab).val = min ab.val.1 ab.val.2 ∨
                (r ab).val = 1 ∨ IsTwoSplit K (r ab).val) ∧
              ((∀ v : Nat,
                HasCompatibleReservedNextLeaf H K F f m v →
                DiaryLowerBoundColors.singletonColour K Cut v ≠ c) ∨
               (∀ M : Nat,
                ∃ u : Ordered3Graph.Embedding G.graph G.graph,
                  u.AuxTypeRespecting ∧
                  ∀ t : Nat,
                    M < J (u t) ∧
                    DiaryLowerBoundColors.singletonColour K Cut (J (u t)) = c ∧
                    (∀ a b : Nat, a ∈ L → b ∈ L → a < b →
                      (H.edge a b m ↔ K.edge (f a) (f b) (J (u t)))) ∧
                    (∀ w : {w : Nat // w ∈ W},
                      K.oneMeetLevel w.val (J (u t)) = (p w).val) ∧
                    (∀ ab : {ab : Nat × Nat //
                        ab ∈ finiteOrderedLeafPairs W},
                      ∀ w : {w : Nat // w ∈ W},
                        K.twoMeetLevel ab.val.1 ab.val.2
                          w.val (J (u t)) = (q ab w).val) ∧
                    (∀ ab : {ab : Nat × Nat //
                        ab ∈ finiteOrderedLeafPairs W},
                      K.twoMeetLevel ab.val.1 (J (u t))
                        ab.val.2 (J (u t)) = (r ab).val) ∧
                    HasCompatibleReservedNextLeaf H K F f m (J (u t)))) := by
  classical
  let L := countableDiaryLeafPrefix H m
  let W := L.image f
  let Cut := oldStageTailCut H m f
  obtain ⟨J, hJ, c, p, q, r, hOne, hCross, hNewNew, hAll⟩ :=
    DK.exists_uniform_source_E5_generic_full_oldCut_S1_S2_cones
      G F hFLeaf f P
  refine ⟨J, hJ, c, p, q, r, hOne, hCross, hNewNew, ?_⟩
  let R : Nat → Prop := fun v =>
    (∀ a b : Nat, a ∈ L → b ∈ L → a < b →
      (H.edge a b m ↔ K.edge (f a) (f b) v)) ∧
    (∀ w : {w : Nat // w ∈ W},
      K.oneMeetLevel w.val v = (p w).val) ∧
    (∀ ab : {ab : Nat × Nat // ab ∈ finiteOrderedLeafPairs W},
      ∀ w : {w : Nat // w ∈ W},
        K.twoMeetLevel ab.val.1 ab.val.2 w.val v = (q ab w).val) ∧
    (∀ ab : {ab : Nat × Nat // ab ∈ finiteOrderedLeafPairs W},
      K.twoMeetLevel ab.val.1 v ab.val.2 v = (r ab).val)
  have hJLeaves (t : Nat) : IsLeaf K (J t) := (hJ t).1
  have hJInF (t : Nat) : ∃ i : Nat, J t = F i := (hJ t).2.1
  have hProfileCones : ∀ M : Nat,
      ∃ u : Ordered3Graph.Embedding G.graph G.graph,
        u.AuxTypeRespecting ∧
        ∀ t : Nat,
          M < J (u t) ∧
          DiaryLowerBoundColors.singletonColour K Cut (J (u t)) = c ∧
          R (J (u t)) := by
    intro M
    obtain ⟨u, hu, hCopy⟩ := hAll M
    refine ⟨u, hu, ?_⟩
    intro t
    obtain ⟨hHigh, hColour, hE5, hOneMeet, hCrossMeet, hNewMeet⟩ :=
      hCopy t
    exact ⟨hHigh, hColour, hE5, hOneMeet, hCrossMeet, hNewMeet⟩
  rcases generic_profile_colour_cones_good_or_no_compatible_anchor
    (H := H) (K := K) (F := (fun t : Nat => F t))
    (f := f) (m := m)
    hm G J hJLeaves hJInF c R hProfileCones with
    hNone | hGood
  · exact Or.inl hNone
  · right
    intro M
    obtain ⟨u, hu, hCopy⟩ := hGood M
    refine ⟨u, hu, ?_⟩
    intro t
    obtain ⟨hHigh, hColour, hR, hReserved⟩ := hCopy t
    obtain ⟨hE5, hOneMeet, hCrossMeet, hNewMeet⟩ := hR
    exact ⟨hHigh, hColour, hE5, hOneMeet,
      hCrossMeet, hNewMeet, hReserved⟩

end DiaryLeafPriority
end ThreeUniformDiaries
