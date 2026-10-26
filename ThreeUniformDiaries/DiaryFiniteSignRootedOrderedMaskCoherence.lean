import ThreeUniformDiaries.DiaryFiniteSignRootedRankCutParentTransport

/-!
# The actual sign-rooted off-branch mask is coherent at rank cuts

The causal literal-V3 construction needs only equality of the masks
selecting missing off-branch marker edges for corresponding positive
successors. We now verify this for the ACTUAL sign-rooted raw tree.

At a shared source split s, every earlier node Y in a level-first
enumeration has original source level <= s. If Y is strictly below s,
prefix uniqueness gives the same off-branch classification for every
later branch terminal sharing that cut. The proposed total order puts
Y before either terminal, making this an equality of ordered masks.
If Y has original level s, it has SPLIT role rather than LEAF role;
both off-branch masks are false, regardless of the tie-break order.

Additionally, no vertex at an original split level can occur as the
middle of a selected off-branch marker edge, and no ordered pair on a
single original source branch can be selected.

These statements are about the concrete structural mask on RAW
sign-rooted nodes, not yet about its transport to a finite
Nat-indexed enumeration. They establish the mask hypotheses needed
when the causal V3 construction is instantiated at the rank cut.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority
namespace FiniteSignRootedFlipFamily

variable {A : Ordered3Graph Nat} {n : Nat} {ι : Type*}

/-- At a shared source cut, an earlier raw node Y of strictly
smaller source level has identical ORDERED off-branch masks
against the two later terminals. This includes all off-path Y. -/
theorem orderedOffBranch_sharedCut_of_source_lt
    (F : FiniteSignRootedFlipFamily A n ι)
    (before : FiniteSignRootedNode A n →
      FiniteSignRootedNode A n → Prop)
    (hLevel : F.ExtendsSourceLevels before)
    (i j : ι) (s u v : Nat)
    (hShared : F.node i s = F.node j s)
    (hsu : s ≤ u) (hsv : s ≤ v)
    (hun : u < n) (hvn : v < n)
    (hu : IsLeaf A u) (hv : IsLeaf A v)
    (Y : FiniteSignRootedNode A n) (hYs : Y.1 < s) :
    F.OrderedOffBranchLeafPair before Y (F.node i u) ↔
      F.OrderedOffBranchLeafPair before Y (F.node j v) := by
  have hYU : Y.1 < (F.node i u).1 := by
    simp only [F.node_level]
    omega
  have hYV : Y.1 < (F.node j v).1 := by
    simp only [F.node_level]
    omega
  have hI := F.orderedOffBranch_iff_original_of_source_lt
    before hLevel Y (F.node i u) hYU
  have hJ := F.orderedOffBranch_iff_original_of_source_lt
    before hLevel Y (F.node j v) hYV
  have hPrefix := F.offBranchLeafPair_iff_of_shared_cut
    i j s hShared Y hYs u v hsu hsv hun hvn hu hv
  exact hI.trans (hPrefix.trans hJ.symm)

/-- At a source split level s, EVERY raw node of source level s
is non-leaf and therefore cannot be the middle vertex of
an added ordered off-branch Devlin marker edge. -/
theorem orderedOffBranch_splitLevel_middle_false
    (F : FiniteSignRootedFlipFamily A n ι)
    (before : FiniteSignRootedNode A n →
      FiniteSignRootedNode A n → Prop)
    (s : Nat) (hs : IsOneSplit A s ∨ IsTwoSplit A s)
    (Y Z : FiniteSignRootedNode A n)
    (hYs : Y.1 = s) :
    ¬ F.OrderedOffBranchLeafPair before Y Z := by
  have hNoLeaf : ¬ IsLeaf A Y.1 := by
    rw [hYs]
    exact splitRole_not_leaf A s hs
  intro hOff
  exact hNoLeaf hOff.leafY

/-- The exact missing-marker mask agrees for two later leaves
on branches sharing a 1- or 2-split at EVERY earlier raw node
of the FINAL level-first rank order, even when source levels tie.

Unlike PrefixUniformOrientation, this is unconditional: it is
a theorem of the sign-rooted geometry and the split roles. -/
theorem orderedOffBranch_sharedSplit_rank_predecessor
    (F : FiniteSignRootedFlipFamily A n ι)
    (before : FiniteSignRootedNode A n →
      FiniteSignRootedNode A n → Prop)
    (hLevel : F.ExtendsSourceLevels before)
    (hOrder : F.LevelFirstStrictOrder before)
    (i j : ι) (s u v : Nat)
    (hs : IsOneSplit A s ∨ IsTwoSplit A s)
    (hShared : F.node i s = F.node j s)
    (hsu : s < u) (hsv : s < v)
    (hun : u < n) (hvn : v < n)
    (hu : IsLeaf A u) (hv : IsLeaf A v)
    (Y : FiniteSignRootedNode A n)
    (hYS : before Y (F.node i s)) :
    F.OrderedOffBranchLeafPair before Y (F.node i u) ↔
      F.OrderedOffBranchLeafPair before Y (F.node j v) := by
  have hYsLe : Y.1 ≤ s := by
    have h := hOrder.1 Y (F.node i s) hYS
    simpa only [F.node_level] using h
  rcases lt_or_eq_of_le hYsLe with hYs | hYs
  · exact F.orderedOffBranch_sharedCut_of_source_lt
      before hLevel i j s u v hShared
      hsu.le hsv.le hun hvn hu hv Y hYs
  · have hNoI : ¬ F.OrderedOffBranchLeafPair
        before Y (F.node i u) :=
      F.orderedOffBranch_splitLevel_middle_false
        before s hs Y (F.node i u) hYs
    have hNoJ : ¬ F.OrderedOffBranchLeafPair
        before Y (F.node j v) :=
      F.orderedOffBranch_splitLevel_middle_false
        before s hs Y (F.node j v) hYs
    exact iff_of_false hNoI hNoJ

/-- Cross-marker bits are NEVER inserted on a pair of vertices
from the same original genuine source flip branch, regardless
of the candidate enumeration or orientation. -/
theorem orderedOffBranch_same_source_branch_false
    (F : FiniteSignRootedFlipFamily A n ι)
    (before : FiniteSignRootedNode A n →
      FiniteSignRootedNode A n → Prop)
    (i : ι) (u v : Nat)
    (huv : u < v) (hvn : v < n) :
    ¬ F.OrderedOffBranchLeafPair before
      (F.node i u) (F.node i v) := by
  intro hOff
  have hPair : F.SharedBranchPair
      (F.node i u) (F.node i v) :=
    ⟨i,u,v,huv,hvn,rfl,rfl⟩
  exact hOff.separated hPair

end FiniteSignRootedFlipFamily

/-- The concrete finite canonical sign-rooted carrier, equipped
with its verified level-first rank ordering, satisfies the
FULL earlier-mask comparison at any shared genuine split. -/
theorem finiteCanonicalSignRooted_orderedMask_sharedSplit
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (i j : FiniteCanonicalFlipIndex A n)
    (s u v : Nat)
    (hs : IsOneSplit A s ∨ IsTwoSplit A s)
    (hShared :
      (finiteCanonicalSignRootedFamily DA).node i s =
      (finiteCanonicalSignRootedFamily DA).node j s)
    (hsu : s < u) (hsv : s < v)
    (hun : u < n) (hvn : v < n)
    (hu : IsLeaf A u) (hv : IsLeaf A v)
    (Y : FiniteSignRootedNode A n)
    (hYS : finiteCanonicalNodeBeforeAmbient DA Y
      ((finiteCanonicalSignRootedFamily DA).node i s)) :
    (finiteCanonicalSignRootedFamily DA).OrderedOffBranchLeafPair
      (finiteCanonicalNodeBeforeAmbient DA)
      Y ((finiteCanonicalSignRootedFamily DA).node i u) ↔
    (finiteCanonicalSignRootedFamily DA).OrderedOffBranchLeafPair
      (finiteCanonicalNodeBeforeAmbient DA)
      Y ((finiteCanonicalSignRootedFamily DA).node j v) := by
  exact (finiteCanonicalSignRootedFamily DA).orderedOffBranch_sharedSplit_rank_predecessor
    (finiteCanonicalNodeBeforeAmbient DA)
    (finiteCanonicalNodeBeforeAmbient_extends_levels DA)
    (finiteCanonicalNodeBeforeAmbient_levelFirstStrictOrder DA)
    i j s u v hs hShared hsu hsv hun hvn hu hv Y hYS

end DiaryLeafPriority
end ThreeUniformDiaries
