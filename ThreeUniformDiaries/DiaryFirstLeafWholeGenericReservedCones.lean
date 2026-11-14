import ThreeUniformDiaries.DiaryFirstLeafReservedSuccessor
import ThreeUniformDiaries.DiaryFirstLeafUniformAllHorizonColour
import ThreeUniformDiaries.DiaryReservedOldColourTailDichotomy
import ThreeUniformDiaries.DiaryGenericTargetOldE5PatternCopy

/-!
# Track A: UNCONDITIONAL entire generic cones of genuine first-leaf reserved successors

English-first adversarial proof: 3-uniform-diaries PR #361.

At the FIRST genuine source diary leaf m, the canonical old support
contains ONLY the three fixed role markers 0,1,2. Every real old
reserved stage therefore has exact oldStageTailCut ≤ 3.

The checked RoleDiary.no_edge_in_marker_leaf_support proves every
triple consisting of TWO markers and ONE true target leaf is a
NONEDGE, INCLUDING the (1,2,leaf) test not fixed by IsLeaf alone.
Consequently all true target diary leaves share the SAME complete
mixed singleton type below EVERY cut B≤3.

Choose one actual reserved first-leaf successor g0 inside the original
arbitrary UNORDERED induced generic F range; restrict to obtain
one fixed genuine old stage f=g0 and a real immediate anchor
v0=g0(m). The checked generic target E5-pattern theorem provides,
beyond any numerical cutoff, an ENTIRE induced unordered generic
target leaf subcopy J⊆F[G] above v0. Every J vertex has the
same complete old-cut colour as v0, so the checked old-cut
tail-replacement theorem supplies an ACTUAL compatible
reserved immediate next-leaf stage over the SAME old f
for EVERY J vertex.

Thus the first-leaf good-anchored/generically-rich colour gap
is solved UNCONDITIONALLY, and even the original target range
is an immediate successor tail above v0. This does NOT give
one fixed next-leaf image persistent through later SOURCE
horizons, or a countable full-diary unavoidability theorem.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Every two genuine leaves in a full RoleDiary have the
SAME COMPLETE singleton-colour mask at any cut B≤3.

The (0,1,leaf) and (0,2,leaf) bits vanish by IsLeaf.
The (1,2,leaf) bit vanishes by the full RoleDiary
permitted-edge shape, via the checked no-edge theorem.
No target order relation between the two leaves is needed. -/
theorem RoleDiary.genuine_leaves_same_singletonColour_below_marker_cut
    {K : Ordered3Graph Nat}
    (DK : RoleDiary K) (B : Nat) (hB : B ≤ 3)
    {v w : Nat} (hv : IsLeaf K v) (hw : IsLeaf K w) :
    DiaryLowerBoundColors.singletonColour K B v =
      DiaryLowerBoundColors.singletonColour K B w := by
  apply (DiaryLowerBoundColors.singletonColour_eq_iff K B v w).mpr
  intro x y hxy hyB
  have hy3 : y < 3 := lt_of_lt_of_le hyB hB
  have hx3 : x < 3 := lt_trans hxy hy3
  have hyv : y < v := lt_of_lt_of_le hy3 hv.1
  have hyw : y < w := lt_of_lt_of_le hy3 hw.1
  have hNoV : ¬ K.edge x y v :=
    DK.no_edge_in_marker_leaf_support hv
      (Or.inl hx3) (Or.inl hy3) (Or.inr rfl) hxy hyv
  have hNoW : ¬ K.edge x y w :=
    DK.no_edge_in_marker_leaf_support hw
      (Or.inl hx3) (Or.inl hy3) (Or.inr rfl) hxy hyw
  exact ⟨fun h => False.elim (hNoV h),
    fun h => False.elim (hNoW h)⟩

/-- For the first source leaf, the entire old support S_m consists
of fixed role markers and each old image f(u)≤2.
Thus its ACTUAL full oldStageTailCut (including both old
leaf and generator supports) is at most 3.

This is proved for a GENUINE reserved old stage P, not a
bare prediary map or an invented marker-fixing assumption. -/
theorem first_leaf_oldStageTailCut_le_three
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m : Nat}
    (P : ReservedDiaryStage H K F m f)
    (hFirst : countableDiaryLeafPrefix H m = ∅) :
    oldStageTailCut H m f ≤ 3 := by
  classical
  have hFix : ∀ u : Nat,
      u ∈ countableDiaryFiniteSupport H m → f u = u := by
    intro u hu
    have hu3 : u < 3 :=
      first_leaf_old_support_only_markers H m hFirst u hu
    have hCases : u = 0 ∨ u = 1 ∨ u = 2 := by omega
    rcases hCases with h0 | h1 | h2
    · subst u
      exact P.1.marker_zero
    · subst u
      exact P.1.marker_one
    · subst u
      exact P.1.marker_two
  have hOldBound :
      (countableDiaryFiniteSupport H m).sup f ≤ 2 := by
    apply Finset.sup_le
    intro u hu
    rw [hFix u hu]
    have hu3 : u < 3 :=
      first_leaf_old_support_only_markers H m hFirst u hu
    omega
  have hLeafSup : (countableDiaryLeafPrefix H m).sup f = 0 := by
    rw [hFirst]
    simp
  change
    max ((countableDiaryFiniteSupport H m).sup f)
      ((countableDiaryLeafPrefix H m).sup f) + 1 ≤ 3
  rw [hLeafSup]
  omega

/-- FIRST-LEAF POSITIVE THEOREM. One literal genuine reserved
old source stage f works on arbitrarily late WHOLE
induced UNORDERED generic target leaf subcopies J[G] of the
original prescribed F[G] range, and EVERY vertex of each
J has an ACTUAL old-f-compatible reserved IMMEDIATE successor.

No monochromatic Ramsey refinement, prescribed-source E5
fibre construction beyond an empty mask, or finite palette
hypothesis is required. The output maps may depend on J(t),
and no image is asserted to survive later source horizons. -/
theorem RoleDiary.exists_first_leaf_entire_generic_cones_of_reserved_successors
    {H K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    (m : Nat) (hm : IsLeaf H m)
    (hFirst : countableDiaryLeafPrefix H m = ∅) :
    ∃ f : Nat → Nat,
      ReservedDiaryStage H K (fun t : Nat => F t) m f ∧
      ∀ M : Nat,
        ∃ J : Ordered3Graph.UnorderedEmbedding G.graph K,
          ∀ n : Nat,
            M < J n ∧
            IsLeaf K (J n) ∧
            (∃ t : Nat, J n = F t) ∧
            HasCompatibleReservedNextLeaf H K
              (fun t : Nat => F t) f m (J n) := by
  classical
  obtain ⟨t₀, ht₀⟩ :=
    exists_ge_of_injective_nat (fun t : Nat => F t) F.injective m
  obtain ⟨g₀, Q₀, _hOldLeaves⟩ :=
    exists_reserved_successor_of_first_leaf
      (F := fun t : Nat => F t) (f := fun u : Nat => u)
      (m := m) (t := t₀)
      DH DK hm hFirst (hFLeaf t₀) ht₀
  have P : ReservedDiaryStage H K (fun t : Nat => F t) m g₀ :=
    Q₀.restrict (by omega)
  have hOldCompatible : CofinalDiaryStageCompatible H m g₀ g₀ := by
    intro u hu
    rfl
  have hAnchor : HasCompatibleReservedNextLeaf H K
      (fun t : Nat => F t) g₀ m (g₀ m) :=
    ⟨g₀, Q₀, hOldCompatible, rfl⟩
  have hmSelected : m ∈ countableDiaryLeafPrefix H (m + 1) :=
    (mem_countableDiaryLeafPrefix_iff H (m + 1) m).mpr
      ⟨hm.1, by omega, hm⟩
  have hmSupported : m ∈ countableDiaryFiniteSupport H (m + 1) :=
    mem_finiteLeafMeetSupport_leaf H
      (countableDiaryLeafPrefix H (m + 1)) m hmSelected
  have hv₀Leaf : IsLeaf K (g₀ m) :=
    Q₀.1.leaf_role m hmSupported hm
  have hB : oldStageTailCut H m g₀ ≤ 3 :=
    first_leaf_oldStageTailCut_le_three P hFirst
  refine ⟨g₀, P, ?_⟩
  intro M
  obtain ⟨J, hRange, _hMask⟩ :=
    exists_generic_leaf_subcopy_in_prescribed_target_bounded_E5_pattern
      G K F hFLeaf 0 (max M (g₀ m)) (fun _ _ => false)
  refine ⟨J, ?_⟩
  intro n
  have hM : M < J n :=
    lt_of_le_of_lt (le_max_left M (g₀ m)) (hRange n).1
  have hAbove : g₀ m ≤ J n :=
    le_of_lt (lt_of_le_of_lt
      (le_max_right M (g₀ m)) (hRange n).1)
  have hLeaf : IsLeaf K (J n) := (hRange n).2.2.1
  have hInF : ∃ t : Nat, J n = F t := (hRange n).2.2.2
  have hSameColour :
      DiaryLowerBoundColors.singletonColour K
        (oldStageTailCut H m g₀) (g₀ m) =
      DiaryLowerBoundColors.singletonColour K
        (oldStageTailCut H m g₀) (J n) :=
    DK.genuine_leaves_same_singletonColour_below_marker_cut
      (oldStageTailCut H m g₀) hB hv₀Leaf hLeaf
  have hGood : HasCompatibleReservedNextLeaf H K
      (fun t : Nat => F t) g₀ m (J n) :=
    compatible_reserved_nextLeaf_tail_of_oldCut_colour
      hm hAnchor hAbove hLeaf hInF hSameColour
  exact ⟨hM, hLeaf, hInF, hGood⟩

end DiaryLeafPriority
end ThreeUniformDiaries
