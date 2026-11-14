import ThreeUniformDiaries.DiaryFirstLeafWholeGenericReservedCones
import ThreeUniformDiaries.DiaryAllVerticesColourGenericExtensions

/-!
# Track A: FIRST-LEAF old cut is EXACTLY 3; one anchored colour extends ALL stages

English-first adversarial proof: 3-uniform-diaries PR #363.

For a genuine first source leaf m, the old selected-leaf prefix
is empty and S_m consists EXACTLY of role markers 0,1,2.
Any actual reserved old stage fixes those marker images.
Consequently the full oldStageTailCut H m f is EXACTLY 3
(upper bound: all supported images ≤2; lower bound: marker 2
belongs to S_m and f(2)=2).

In a full target RoleDiary, all TRUE target leaves have the
same COMPLETE singleton colour at this cut 3: ALL triple bits
over the three marker pairs (0,1), (0,2), (1,2) vanish by the
fully verified RoleDiary.no_edge_in_marker_leaf_support.

Thus any arbitrary original UNORDERED induced generic leaf
range F[G] is LITERALLY monochromatic below the exact old
cut, rather than merely containing a monochromatic subcopy.
The newly checked pure generic lemma proves that its vertex
predicate passes HasGenericColourOnePointExtensions at EVERY
finite induced increasing generic stage, not just n=0,1.

An ACTUAL first-leaf reserved anchor exists by the now
verified full generic first-leaf successor cones theorem.
We hence export one old stage f and one anchored complete
colour c with the ENTIRE generic one-point extension schema.

The first source leaf therefore satisfies the strong
sufficient generic-colour criterion in full. Later source
leaves do NOT have global constant full old-cut colours,
and no fixed new-leaf image surviving future source horizons
or full countable diary unavoidability is asserted.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- For any genuine reserved old stage of the FIRST source
leaf, the ACTUAL full old support cut is numerically EXACTLY 3.
This includes both old selected leaf and old nonleaf generator
images (there are none), and retains the source marker-2
lower bound, not just the previously checked cut ≤3. -/
theorem first_leaf_oldStageTailCut_eq_three
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m : Nat}
    (P : ReservedDiaryStage H K F m f)
    (hFirst : countableDiaryLeafPrefix H m = ∅) :
    oldStageTailCut H m f = 3 := by
  classical
  have hUpper : oldStageTailCut H m f ≤ 3 :=
    first_leaf_oldStageTailCut_le_three P hFirst
  have h2Support :
      2 ∈ countableDiaryFiniteSupport H m :=
    mem_finiteLeafMeetSupport_marker H
      (countableDiaryLeafPrefix H m) 2 (by omega)
  have hTwoSup :
      2 ≤ (countableDiaryFiniteSupport H m).sup f := by
    calc
      2 = f 2 := P.1.marker_two.symm
      _ ≤ (countableDiaryFiniteSupport H m).sup f :=
        Finset.le_sup (f := f) h2Support
  have hLower : 3 ≤ oldStageTailCut H m f := by
    change 3 ≤
      max ((countableDiaryFiniteSupport H m).sup f)
        ((countableDiaryLeafPrefix H m).sup f) + 1
    omega
  exact Nat.le_antisymm hUpper hLower

/-- The full old-cut singleton colour of the ORIGINAL target
F[G] range is LITERALLY CONSTANT at the FIRST source leaf,
and hence its chosen complete c-colour passes the strong
finite generic one-point extension property for EVERY n.

The outer F is unordered induced in the target; only its
leaf-valued range is used to show complete old-cut colour
equality. The finite extension step itself is the genuine
generic G extension axiom, not a diary-relative assertion. -/
theorem RoleDiary.first_leaf_original_range_has_all_generic_colour_extensions
    {H K : Ordered3Graph Nat}
    (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    {m : Nat} (f : Nat → Nat)
    (P : ReservedDiaryStage H K (fun t : Nat => F t) m f)
    (hFirst : countableDiaryLeafPrefix H m = ∅) :
    let c := DiaryLowerBoundColors.singletonColour K
      (oldStageTailCut H m f) (F 0)
    (∀ t : Nat,
      DiaryLowerBoundColors.singletonColour K
        (oldStageTailCut H m f) (F t) = c) ∧
      HasGenericColourOnePointExtensions G
        (fun t : Nat =>
          DiaryLowerBoundColors.singletonColour K
            (oldStageTailCut H m f) (F t) = c) := by
  classical
  let B := oldStageTailCut H m f
  let c := DiaryLowerBoundColors.singletonColour K B (F 0)
  have hB : B ≤ 3 :=
    first_leaf_oldStageTailCut_le_three P hFirst
  have hAll : ∀ t : Nat,
      DiaryLowerBoundColors.singletonColour K B (F t) = c := by
    intro t
    exact DK.genuine_leaves_same_singletonColour_below_marker_cut
      B hB (hFLeaf t) (hFLeaf 0)
  exact ⟨hAll,
    G.has_generic_colour_onePointExtensions_of_all
      (fun t : Nat =>
        DiaryLowerBoundColors.singletonColour K B (F t) = c)
      hAll⟩

/-- UNCONDITIONAL first-leaf completion of the strong
anchor + ALL finite generic one-point extensions criterion.

One genuine literal old reserved stage f and one COMPLETE
old-cut colour c are selected together, BEFORE all finite
generic source stages. The colour has an ACTUAL compatible
reserved immediate next-leaf anchor in the original F range,
and EVERY induced increasing finite generic stage whose
images lie in c can be extended inside the SAME colour.

This closes the anchored generically-rich colour problem in
the marker-only FIRST-LEAF case. It does not select a fixed
new-leaf image persistent through later source horizons or
address non-first source leaves with nontrivial old E2/E3/E5. -/
theorem RoleDiary.exists_first_leaf_anchored_colour_with_all_generic_onePointExtensions
    {H K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    (m : Nat) (hm : IsLeaf H m)
    (hFirst : countableDiaryLeafPrefix H m = ∅) :
    ∃ f : Nat → Nat,
      ReservedDiaryStage H K (fun t : Nat => F t) m f ∧
      ∃ c : Fin (oldStageTailCut H m f) →
          Fin (oldStageTailCut H m f) → Bool,
        (∃ v : Nat,
          HasCompatibleReservedNextLeaf H K
            (fun t : Nat => F t) f m v ∧
          DiaryLowerBoundColors.singletonColour K
            (oldStageTailCut H m f) v = c) ∧
        HasGenericColourOnePointExtensions G
          (fun t : Nat =>
            DiaryLowerBoundColors.singletonColour K
              (oldStageTailCut H m f) (F t) = c) := by
  classical
  obtain ⟨f, P, hCones⟩ :=
    DH.exists_first_leaf_entire_generic_cones_of_reserved_successors
      DK G F hFLeaf m hm hFirst
  obtain ⟨J, hAllJ⟩ := hCones 0
  let B := oldStageTailCut H m f
  let c := DiaryLowerBoundColors.singletonColour K B (F 0)
  obtain ⟨hAllC, hExt⟩ :=
    DK.first_leaf_original_range_has_all_generic_colour_extensions
      G F hFLeaf f P hFirst
  have hJ0 : IsLeaf K (J 0) ∧
      (∃ t : Nat, J 0 = F t) ∧
      HasCompatibleReservedNextLeaf H K
        (fun t : Nat => F t) f m (J 0) :=
    (hAllJ 0).2
  obtain ⟨hJLeaf, ⟨t, ht⟩, hJGood⟩ := hJ0
  have hJColour :
      DiaryLowerBoundColors.singletonColour K B (J 0) = c := by
    rw [ht]
    exact hAllC t
  exact ⟨f, P, c, ⟨J 0, hJGood, hJColour⟩, hExt⟩

end DiaryLeafPriority
end ThreeUniformDiaries
