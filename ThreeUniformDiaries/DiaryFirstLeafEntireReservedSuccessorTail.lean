import ThreeUniformDiaries.DiaryFirstLeafWholeGenericReservedCones

/-!
# Track A: a genuine first-leaf reserved anchor saturates the ENTIRE late leaf tail

English-first adversarial proof: 3-uniform-diaries PR #365.

The independently kernel-verified first-leaf whole generic cone
theorem #1509 proves existence of arbitrarily late induced generic
subcopies of actual RESERVED IMMEDIATE successors over one fixed
old marker stage. Its proof has a stronger, useful ingredient:
the full source old support S_m at the FIRST source leaf consists
only of the three fixed markers, so the exact oldStageTailCut≤3.
In a full target RoleDiary every genuine target leaf has the
SAME complete mixed singleton type below this cut, because all
three marker-pair/true-leaf edge bits are false.

Thus for ANY actual first-leaf reserved old stage P and ANY
actual compatible reserved immediate successor anchor v0,
the already checked old-cut type-tail replacement applies to
EVERY genuine F-range leaf w≥v0. The result is a whole numerical
TAIL of actual compatible reserved immediate successors, not
merely cofinal or generic subsets.

The theorem does NOT assert that one fixed new image v0 persists
through later source horizons. The known abstract horizon-escape
countermodel still obstructs that logical inference.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- FULL first-leaf numerical tail saturation. Given a GENUINE
old reserved stage P at a true source leaf m with no earlier
selected source leaves, and ONE ACTUAL compatible immediate
successor with image v0, EVERY genuine target F-range leaf
w≥v0 is itself an ACTUAL compatible reserved immediate
successor over the literal SAME old f.

This does not require G, genericity of F, or target numerical
monotonicity of the prescribed F map: only target RoleDiary K,
the first-leaf marker-only support, and one actual anchor.
No source-horizon persistence follows. -/
theorem RoleDiary.first_leaf_reserved_anchor_saturates_entire_late_leaf_tail
    {H K : Ordered3Graph Nat}
    (DK : RoleDiary K)
    {F f : Nat → Nat} {m v₀ : Nat}
    (hm : IsLeaf H m)
    (hFirst : countableDiaryLeafPrefix H m = ∅)
    (P : ReservedDiaryStage H K F m f)
    (hAnchor : HasCompatibleReservedNextLeaf H K F f m v₀) :
    ∀ w : Nat, v₀ ≤ w →
      IsLeaf K w → (∃ t : Nat, w = F t) →
      HasCompatibleReservedNextLeaf H K F f m w := by
  have hv₀Leaf : IsLeaf K v₀ := by
    obtain ⟨g, Q, _hOld, hNew⟩ := hAnchor
    have hmSelected : m ∈ countableDiaryLeafPrefix H (m + 1) :=
      (mem_countableDiaryLeafPrefix_iff H (m + 1) m).mpr
        ⟨hm.1, by omega, hm⟩
    have hmSupported : m ∈ countableDiaryFiniteSupport H (m + 1) :=
      mem_finiteLeafMeetSupport_leaf H
        (countableDiaryLeafPrefix H (m + 1)) m hmSelected
    have hRole : IsLeaf K (g m) :=
      Q.1.leaf_role m hmSupported hm
    simpa only [hNew] using hRole
  have hCut : oldStageTailCut H m f ≤ 3 :=
    first_leaf_oldStageTailCut_le_three P hFirst
  intro w hvw hwLeaf hwRange
  have hColour :
      DiaryLowerBoundColors.singletonColour K
        (oldStageTailCut H m f) v₀ =
      DiaryLowerBoundColors.singletonColour K
        (oldStageTailCut H m f) w :=
    DK.genuine_leaves_same_singletonColour_below_marker_cut
      (oldStageTailCut H m f) hCut hv₀Leaf hwLeaf
  exact compatible_reserved_nextLeaf_tail_of_oldCut_colour
    hm hAnchor hvw hwLeaf hwRange hColour

/-- Existential unconditional FULL TAIL for the FIRST true source
leaf in any original unordered induced generic true-leaf target
range F[G]. There is ONE literal genuine reserved old source
stage f and a finite target threshold T such that EVERY
genuine F-range leaf w≥T is a compatible actual future-order-
reserved immediate new-leaf image fixing all of f's old support.

An actual anchor T is supplied by the existing verified
first-leaf generic-cone theorem. This is strictly stronger
than the existence of arbitrary late whole induced generic
successor subcopies, but still not persistent new-leaf image
survival through future source horizons. -/
theorem RoleDiary.exists_first_leaf_entire_late_reserved_successor_tail
    {H K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    (m : Nat) (hm : IsLeaf H m)
    (hFirst : countableDiaryLeafPrefix H m = ∅) :
    ∃ f : Nat → Nat,
      ReservedDiaryStage H K (fun t : Nat => F t) m f ∧
      ∃ T : Nat,
        ∀ w : Nat, T ≤ w →
          IsLeaf K w →
          (∃ t : Nat, w = F t) →
          HasCompatibleReservedNextLeaf H K
            (fun t : Nat => F t) f m w := by
  obtain ⟨f, P, hCones⟩ :=
    DH.exists_first_leaf_entire_generic_cones_of_reserved_successors
      DK G F hFLeaf m hm hFirst
  obtain ⟨J, hAll⟩ := hCones 0
  have hAnchor : HasCompatibleReservedNextLeaf H K
      (fun t : Nat => F t) f m (J 0) :=
    (hAll 0).2.2.2
  refine ⟨f, P, J 0, ?_⟩
  exact DK.first_leaf_reserved_anchor_saturates_entire_late_leaf_tail
    hm hFirst P hAnchor

end DiaryLeafPriority
end ThreeUniformDiaries
