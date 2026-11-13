import ThreeUniformDiaries.DiaryGenericOldStageRequiredE5Copy
import ThreeUniformDiaries.DiaryGenericCompleteOneNewS1S2

/-!
# Track A: entire source-required E5 generic cones with one complete S1/S2 profile

For a fixed ACTUAL old reserved diary stage f whose selected
source leaves belong to one original UNORDERED induced generic
true-leaf target copy F[G], the newly checked source-required E5
generic-copy theorem gives an ACTUAL induced generic subcopy J[G]
inside the same F range whose EVERY leaf realizes the entire
SOURCE-required old-pair/new-leaf E5 edge AND nonedge table.

Apply the already fully validated Track C theorem on uniform
generic one-new-leaf full-colour numerical profiles INSIDE J,
with W equal to the literal OLD selected target leaf images and
Cut larger than every W root. This gives one selected complete
mixed singleton colour and an EXACT numerical S1 and BOTH
old-old/new and new-new full S2 meet vector, all simultaneous
on arbitrarily late ACTUAL induced generic J-subcopies.

Thus the very SAME induced generic leaf reservoirs both realize
ALL source-required E5 bits and have a constant complete target
S1/S2 numeric profile, including genuine target S1 and S2 role
alternatives. No independent intersection of unrelated E5 and
numeric-profile fibres occurs: numeric homogeneous refinement is
performed INSIDE the source-required E5 generic copy.

Critical limitation: the target p,q,r and complete colour c
are EXISTENTIALLY SELECTED and need NOT be the target images
of the source's prescribed S1/S2 generator vertices. Neither
source-required E2/E3 orientations nor full generator-table
functionality, order gaps, future reserve, or all-horizon
persistent next-leaf images are constructed here.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- From one ACTUAL fixed old reserved source diary stage in an
original unordered induced generic true-leaf range F, construct
an entire generic copy J⊆F whose every leaf realizes ALL the
source's required old-pair E5 bits. Within that SAME copy,
arbitrarily late induced auxiliary-type-respecting generic
subcopies share one full mixed singleton colour and one
complete NUMERIC target new-leaf S1/S2 generator profile.

The old selected target images are literal and fixed. The
new numerical profile is selected existentially, so this
is NOT a full source-compatible reserved successor theorem. -/
theorem RoleDiary.exists_uniform_source_E5_generic_complete_target_S1_S2_cones
    {H K : Ordered3Graph Nat} (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    {m : Nat} (f : Nat → Nat)
    (P : ReservedDiaryStage H K F m f) :
    let L := countableDiaryLeafPrefix H m
    let W := L.image f
    let Cut := (W.sup (fun w : Nat => w)) + 1
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
  let Cut := (W.sup (fun w : Nat => w)) + 1
  obtain ⟨J,hRange,hE5⟩ :=
    ReservedDiaryStage.exists_generic_leaf_subcopy_realizing_all_required_old_E5
      G F hFLeaf f P 0
  have hJLeaves (t : Nat) : IsLeaf K (J t) :=
    (hRange t).2.1
  have hRoots (w : Nat) (hw : w ∈ W) : IsLeaf K w := by
    obtain ⟨a,ha,hfa⟩ := Finset.mem_image.mp hw
    have haSupport : a ∈ countableDiaryFiniteSupport H m :=
      mem_finiteLeafMeetSupport_leaf H L a ha
    have haLeaf : IsLeaf H a :=
      ((mem_countableDiaryLeafPrefix_iff H m a).mp ha).2.2
    have hLeaf := P.1.leaf_role a haSupport haLeaf
    simpa only [hfa] using hLeaf
  obtain ⟨c,p,q,r,hOne,hCross,hNewNew,hAll⟩ :=
    DK.exists_uniform_generic_complete_oneNew_S1_S2_profiles
      G J hJLeaves W hRoots Cut (Nat.lt_succ_self _)
  refine ⟨J, ?_, c,p,q,r,hOne,hCross,hNewNew, ?_⟩
  · intro t
    obtain ⟨_hHigh,hLeaf,t0,hAtF⟩ := hRange t
    exact ⟨hLeaf,⟨t0,hAtF⟩,hE5 t⟩
  · intro M
    obtain ⟨u,hu,hCopy⟩ := hAll M
    refine ⟨u,hu,?_⟩
    intro t
    obtain ⟨hHigh,_hLeaf,hColour,hOneMeet,hCrossMeet,hNewMeet⟩ :=
      hCopy t
    exact ⟨hHigh,hColour,hE5 (u t),
      hOneMeet,hCrossMeet,hNewMeet⟩

end DiaryLeafPriority
end ThreeUniformDiaries
