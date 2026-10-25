import ThreeUniformDiaries.DiaryFiniteSignRootedOrderedMarkerCoverage

/-!
# Ordered tie repair agrees with first marker extension at increasing levels

The corrected cross-branch Devlin marker extension handles two
distinct raw nodes tied at an ORIGINAL source level, after a
candidate ambient order resolves the tie. At strictly increasing
source levels, however, there must be NO change from the first
verified extension.

The only assumption on the ambient candidate order needed for
this comparison is that it ranks nodes with smaller source level
first. Then an ordered off-branch predicate on Y,Z with Y.1<Z.1
is equivalent to the old strict-level off-branch predicate.
Consequently the entire ordered-marker relation agrees with
the old marker extension on ALL increasing-original-level
terminal pairs, including their edges and nonedges.

This is a key bridge: all type tests below a source cut s
involving a terminal strictly beyond s are of that kind,
and full auxiliary pair tests on a single original branch
also have increasing source terminal levels. Thus the
prefix-uniform marker-stability theorem for the first
extension can be transferred to the corrected ordered
extension, provided the candidate order respects source levels.

This does NOT prove that an admissible globally linear order
and an orientation satisfying literal V3 exist together.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority
namespace FiniteSignRootedFlipFamily

variable {A : Ordered3Graph Nat} {n : Nat} {ι : Type*}

/-- Minimal source-level monotonicity required of a candidate
ambient ordering of all sign-rooted raw nodes. -/
def ExtendsSourceLevels
    (F : FiniteSignRootedFlipFamily A n ι)
    (before : FiniteSignRootedNode A n →
      FiniteSignRootedNode A n → Prop) : Prop :=
  ∀ Y Z : FiniteSignRootedNode A n,
    Y.1 < Z.1 → before Y Z

/-- On strictly increasing original source levels, the new
ordered off-branch predicate is exactly the old one. -/
theorem orderedOffBranch_iff_original_of_source_lt
    (F : FiniteSignRootedFlipFamily A n ι)
    (before : FiniteSignRootedNode A n →
      FiniteSignRootedNode A n → Prop)
    (hLevel : F.ExtendsSourceLevels before)
    (Y Z : FiniteSignRootedNode A n)
    (hYZ : Y.1 < Z.1) :
    F.OrderedOffBranchLeafPair before Y Z ↔
      F.OffBranchLeafPair Y Z := by
  constructor
  · intro h
    exact ⟨h.leafY,h.leafZ,hYZ,h.separated⟩
  · intro h
    exact ⟨h.leafY,h.leafZ,hLevel Y Z hYZ,h.separated⟩

/-- The corrected (tie-covering) marker extension and the first
source-level-ordered extension AGREE on all triple tests whose
last two vertices have strictly increasing source levels,
regardless of the first raw vertex. -/
theorem orderedMarkerExtension_iff_original_of_source_lt
    (F : FiniteSignRootedFlipFamily A n ι)
    (base : ι)
    (before orient : FiniteSignRootedNode A n →
      FiniteSignRootedNode A n → Prop)
    (hLevel : F.ExtendsSourceLevels before)
    (X Y Z : FiniteSignRootedNode A n)
    (hYZ : Y.1 < Z.1) :
    (F.withOrderedCrossMarkerEdges base before orient).edge X Y Z ↔
      (F.withCrossMarkerEdges base orient).edge X Y Z := by
  have hOff := F.orderedOffBranch_iff_original_of_source_lt
    before hLevel Y Z hYZ
  change
    ((F.rawAmalgam).edge X Y Z ∨
      (X = F.node base 1 ∧
        F.OrderedOffBranchLeafPair before Y Z ∧ orient Y Z) ∨
      (X = F.node base 2 ∧
        F.OrderedOffBranchLeafPair before Y Z ∧ ¬ orient Y Z)) ↔
    ((F.rawAmalgam).edge X Y Z ∨
      (X = F.node base 1 ∧
        F.OffBranchLeafPair Y Z ∧ orient Y Z) ∨
      (X = F.node base 2 ∧
        F.OffBranchLeafPair Y Z ∧ ¬ orient Y Z))
  simp only [hOff]

/-- The necessary order condition is consistent, even though
this displayed source-level comparison does NOT totally order
distinct nodes tied at the same level. -/
theorem exists_level_extending_relation
    (F : FiniteSignRootedFlipFamily A n ι) :
    ∃ before : FiniteSignRootedNode A n →
        FiniteSignRootedNode A n → Prop,
      F.ExtendsSourceLevels before := by
  exact ⟨fun Y Z => Y.1 < Z.1,
    by intro Y Z hYZ; exact hYZ⟩

end FiniteSignRootedFlipFamily
end DiaryLeafPriority
end ThreeUniformDiaries
