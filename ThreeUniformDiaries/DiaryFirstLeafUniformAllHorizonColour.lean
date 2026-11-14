import ThreeUniformDiaries.DiaryIndependentReservedStageExistence
import ThreeUniformDiaries.DiaryGenericTargetOldE5PatternCopy
import ThreeUniformDiaries.DiaryHorizonUniformOldColourDiagonal

/-!
# Track A: UNCONDITIONAL first-leaf all-horizon reserved and old-cut colour recurrence

English-first adversarial proof: 3-uniform-diaries PR #359.

For ANY genuine source next leaf m and ANY finite horizon q=m+1+n,
a chosen generic target-leaf subcopy J of the ORIGINAL unordered F
range can be placed entirely above any prescribed target M. The
checked INDEPENDENT genuine reserved q-stage existence theorem in
that J has its true source leaf m mapped into J. Weakening its
leaf range back to F proves cofinally high actual q-stage
new-leaf witnesses for EVERY q,M. These witnesses need not agree
on earlier source leaves.

At the FIRST source leaf, however, there are NO previously
selected source leaves and canonical old support S_m consists
only of the three fixed role markers 0,1,2. Hence EVERY actual
reserved q-stage witness above has one SINGLETON old-supported
image profile, independent of q and M. This UNCONDITIONALLY
verifies the common finite-profile cover hypothesis used by
the already kernel-checked Track A #1495 and #1502.

The result is ONE finitely persistent old marker stage f and
ONE complete oldStageTailCut colour c which recurs with actual
compatible reserved q-stage new images cofinally at EVERY future
horizon, and is eventually saturated for IMMEDIATE successors.

This base case does NOT fix one new-leaf image through later
source horizons, does not make the c fibre generically rich,
and does not establish countable diary unavoidability.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Arbitrarily high genuine RESERVED q-horizon source stages
exist in the ORIGINAL arbitrary unordered induced generic
true-leaf target range F, for each given future source horizon
q=m+1+n and any true source leaf m.

There is NO single fixed old support f across q or target bounds;
the stages and initial generic refinements may all vary. -/
theorem RoleDiary.exists_cofinally_high_reserved_new_image_at_every_finite_horizon
    {H K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    (m : Nat) (hm : IsLeaf H m) :
    ∀ n M : Nat,
      ∃ t : Nat, ∃ g : Nat → Nat,
        M < F t ∧
        ReservedDiaryStage H K (fun t : Nat => F t)
          (m + 1 + n) g ∧
        g m = F t := by
  classical
  have hUniversal : Ordered3Graph.CountablyUniversal G.graph := by
    intro A
    obtain ⟨v, hMono, hInduced⟩ :=
      G.exists_countable_induced_embedding A
    let e : Ordered3Graph.Embedding A G.graph := {
      toFun := v
      strictMono := hMono
      edge_iff := by
        intro a b c hab hbc
        exact hInduced a b c hab hbc
    }
    exact ⟨e.asUnordered⟩
  intro n M
  obtain ⟨J, hRange, _hPattern⟩ :=
    exists_generic_leaf_subcopy_in_prescribed_target_bounded_E5_pattern
      G K F hFLeaf 0 M (fun _ _ => false)
  have hJLeaf (t : Nat) : IsLeaf K (J t) :=
    (hRange t).2.2.1
  have hJInsideF (t : Nat) : ∃ i : Nat, J t = F i :=
    (hRange t).2.2.2
  obtain ⟨g, Q⟩ :=
    exists_independent_reserved_stage_in_universal_leaf_range
      DH DK G hUniversal J hJLeaf (m + 1 + n)
  have hmSelected : m ∈ countableDiaryLeafPrefix H (m + 1 + n) :=
    (mem_countableDiaryLeafPrefix_iff H (m + 1 + n) m).mpr
      ⟨hm.1, by omega, hm⟩
  have hmSupported : m ∈ countableDiaryFiniteSupport H (m + 1 + n) :=
    mem_finiteLeafMeetSupport_leaf H
      (countableDiaryLeafPrefix H (m + 1 + n)) m hmSelected
  obtain ⟨j, hNew⟩ := Q.1.leaf_range m hmSupported hm
  obtain ⟨t, hAtF⟩ := hJInsideF j
  have hHigh : M < F t := by
    rw [← hAtF]
    exact (hRange j).1
  have QOriginal :
      ReservedDiaryStage H K (fun t : Nat => F t)
        (m + 1 + n) g :=
    Q.weaken_leaf_range hJInsideF
  exact ⟨t, g, hHigh, QOriginal, hNew.trans hAtF⟩

/-- At the FIRST true source leaf the old support is JUST
the three fixed role markers. All independent q-horizon
reserved stage maps therefore have the SAME literal
old-supported image profile, independent of q and M. -/
theorem first_leaf_old_support_only_markers
    (H : Ordered3Graph Nat) (m : Nat)
    (hFirst : countableDiaryLeafPrefix H m = ∅) :
    ∀ u : Nat, u ∈ countableDiaryFiniteSupport H m → u < 3 := by
  classical
  intro u hu
  have hSupport :
      u ∈ finiteLeafMeetSupport H (∅ : Finset Nat) := by
    simpa only [countableDiaryFiniteSupport, hFirst] using hu
  have hMarker : u ∈ Finset.range 3 := by
    simpa [finiteLeafMeetSupport, finiteOneMeetSupport,
      finiteTwoMeetSupport, finiteOrderedLeafPairs] using hSupport
  exact Finset.mem_range.mp hMarker

/-- UNCONDITIONAL positive first-source-leaf base case:
one ACTUAL finitely persistent old marker stage f and one
complete genuine old-cut mixed singleton colour c can be
selected BEFORE all future source horizons n and target
numerical bounds M, with genuine compatible q=m+1+n
reserved new-leaf images of the SAME colour cofinally late
for every n,M. The colour is eventually saturated among
valid IMMEDIATE reserved next-leaf images in the original
unordered F[G] true-leaf range.

This works because the old supported palette has the SINGLETON
marker-identity profile at the FIRST leaf. No assertion that one
new target leaf image survives every future source horizon, or
that the colour class contains an induced generic copy. -/
theorem RoleDiary.exists_first_leaf_uniform_all_horizon_old_support_and_colour
    {H K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    (m : Nat) (hm : IsLeaf H m)
    (hFirst : countableDiaryLeafPrefix H m = ∅) :
    ∃ f : Nat → Nat,
      PersistentReservedDiaryStage H K
        (fun t : Nat => F t) m f ∧
      ∃ c : Fin (oldStageTailCut H m f) →
          Fin (oldStageTailCut H m f) → Bool,
        (∀ n M : Nat,
          ∃ t : Nat, ∃ g : Nat → Nat,
            M < F t ∧
            ReservedDiaryStage H K
              (fun t : Nat => F t) (m + 1 + n) g ∧
            CofinalDiaryStageCompatible H m f g ∧
            g m = F t ∧
            DiaryLowerBoundColors.singletonColour K
              (oldStageTailCut H m f) (F t) = c) ∧
        (∃ T : Nat, ∀ t : Nat,
          T ≤ F t →
          DiaryLowerBoundColors.singletonColour K
            (oldStageTailCut H m f) (F t) = c →
          HasCompatibleReservedNextLeaf H K
            (fun t : Nat => F t) f m (F t)) := by
  classical
  let Old := {u : Nat // u ∈ countableDiaryFiniteSupport H m}
  let W : Finset (Old → Nat) :=
    {fun u : Old => u.val}
  have hAll : ∀ n M : Nat,
      ∃ t : Nat, ∃ g : Nat → Nat,
        M < F t ∧
        ReservedDiaryStage H K (fun t : Nat => F t)
          (m + 1 + n) g ∧
        g m = F t :=
    DH.exists_cofinally_high_reserved_new_image_at_every_finite_horizon
      DK G F hFLeaf m hm
  have hCover : ∀ n M : Nat,
      ∃ t : Nat, ∃ g : Nat → Nat,
        M < F t ∧
        ReservedDiaryStage H K (fun t : Nat => F t)
          (m + 1 + n) g ∧
        g m = F t ∧
        (fun u : Old => g u.val) ∈ W := by
    intro n M
    obtain ⟨t, g, hHigh, Q, hAt⟩ := hAll n M
    have hProfile : (fun u : Old => g u.val) ∈ W := by
      apply Finset.mem_singleton.mpr
      funext u
      have hu3 : u.val < 3 :=
        first_leaf_old_support_only_markers H m hFirst
          u.val u.property
      have huCases : u.val = 0 ∨ u.val = 1 ∨ u.val = 2 := by
        omega
      rcases huCases with h0 | h1 | h2
      · simpa only [h0] using Q.1.marker_zero
      · simpa only [h1] using Q.1.marker_one
      · simpa only [h2] using Q.1.marker_two
    exact ⟨t, g, hHigh, Q, hAt, hProfile⟩
  exact exists_persistent_old_support_and_saturated_colour_all_horizons_of_finite_profile_cover
    (H := H) (K := K) (fun t : Nat => F t)
    m hm hFLeaf W hCover

end DiaryLeafPriority
end ThreeUniformDiaries
