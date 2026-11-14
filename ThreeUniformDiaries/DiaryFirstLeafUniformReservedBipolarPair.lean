import ThreeUniformDiaries.DiaryFirstLeafAllHorizonGenericReservedUnification
import ThreeUniformDiaries.DiaryMonochromaticGenericBipolarPair

/-!
# Track C: a selected BIPOLAR E5 pair among first-leaf reserved successors
# over the SAME all-horizon old support and complete mixed colour

English-first proof and adversarial scope audit:
  janhubicka/3-uniform-diaries PR #366.

The verified first-leaf unification theorem fixes ONE finitely
persistent old marker-only support f and ONE complete old-cut
singleton colour c. The same f,c have genuine compatible reserved
q=m+1+n new-leaf witnesses cofinally high at EVERY finite source
horizon n. Every genuine target leaf has colour c, and every
sufficiently late F-range leaf is a genuine compatible reserved
IMMEDIATE successor over this f. An ENTIRE induced unordered
generic target leaf subcopy consists of such immediate successors.

Apply the already kernel-checked unordered monochromatic generic
BIPOLAR PAIR theorem INSIDE that specific generic immediate
successor copy. It selects two distinct actual true F-range
immediate successor images x,y, both of full old-cut colour c,
so that arbitrarily late THIRD true F-range compatible reserved
immediate successor images realize E5 edges AND nonedges over
that SAME selected pair. The source-order of x,y is irrelevant:
the target triple is measured by unorderedEdge.

This is the correct FIRST NECESSARY pair-richness test and
uses the SAME old support f as the all-horizon q-witness theorem.
It DOES NOT assert that x,y occur simultaneously in one
source-stage map, or that the third images survive ANY later
source horizon, or that the entire q-horizon witness fibre
contains an induced generic copy. No countable diary
unavoidability or exact BRD is inferred.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A true target F-range leaf of one prescribed complete
mixed old-cut colour which admits an ACTUAL compatible
reserved IMMEDIATE next source-leaf extension over f. -/
def IsGoodReservedLeafOfOldCutColour
    (H K : Ordered3Graph Nat) (F f : Nat → Nat) (m : Nat)
    (c : Fin (oldStageTailCut H m f) →
      Fin (oldStageTailCut H m f) → Bool)
    (v : Nat) : Prop :=
  IsLeaf K v ∧
  (∃ t : Nat, v = F t) ∧
  HasCompatibleReservedNextLeaf H K F f m v ∧
  DiaryLowerBoundColors.singletonColour K
    (oldStageTailCut H m f) v = c

/-- Unconditional first-leaf selected E5 bipolarity for one
finitely persistent old support f and full colour c chosen
before ALL future finite source horizons.

The same f,c admit cofinally high genuine reserved horizon
stages at EVERY n. There exists one pair x≠y of TRUE target
F-range compatible reserved IMMEDIATE successor images of c.
For every M the pair has SOME third c-coloured genuine
compatible immediate successor z with unordered E5 edge,
and SOME third such z with E5 nonedge, both >M and >x,y.

No claims are made about sharing a simultaneous stage for
x,y or about preserving these images at any later horizon. -/
theorem RoleDiary.exists_first_leaf_all_horizon_old_support_with_bipolar_reserved_pair
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
        ∃ x y : Nat,
          x ≠ y ∧
          IsGoodReservedLeafOfOldCutColour H K
            (fun t : Nat => F t) f m c x ∧
          IsGoodReservedLeafOfOldCutColour H K
            (fun t : Nat => F t) f m c y ∧
          (∀ M : Nat, ∃ z : Nat,
            M < z ∧ max x y < z ∧
            IsGoodReservedLeafOfOldCutColour H K
              (fun t : Nat => F t) f m c z ∧
            K.unorderedEdge x y z) ∧
          (∀ M : Nat, ∃ z : Nat,
            M < z ∧ max x y < z ∧
            IsGoodReservedLeafOfOldCutColour H K
              (fun t : Nat => F t) f m c z ∧
            ¬ K.unorderedEdge x y z) := by
  classical
  obtain ⟨f,Pf,c,_hPalette,_hColourAll,_hFinite,hAll,_hTail,hCones⟩ :=
    DH.exists_first_leaf_all_horizon_good_colour_and_whole_generic_successor_cones
      DK G F hFLeaf m hm hFirst
  obtain ⟨J,hJ⟩ := hCones 0
  have hC (i : Nat) :
      IsGoodReservedLeafOfOldCutColour H K
        (fun t : Nat => F t) f m c (J i) := by
    obtain ⟨_hM,hLeaf,hInF,hGood⟩ := hJ i
    exact ⟨hLeaf,hInF,hGood,_hColourAll (J i) hLeaf⟩
  obtain ⟨x,y,hNe,hCx,hCy,hPos,hNeg⟩ :=
    exists_unordered_bipolar_pair_of_monochromatic_generic_leaf_copy
      G K
      (IsGoodReservedLeafOfOldCutColour H K
        (fun t : Nat => F t) f m c)
      J hC
  exact ⟨f,Pf,c,hAll,x,y,hNe,hCx,hCy,hPos,hNeg⟩


/-- At the FIRST source leaf, one persistent old f and complete c
can be chosen before ALL finite source horizons and target bounds
so that ACTUAL compatible q-horizon reserved witnesses recur
cofinally, and the SAME source-index colour predicate has the
ENTIRE generic one-point extension property at EVERY finite n.

The proof is exact: full target RoleDiary marker-colour rigidity
makes the selected c TRUE on EVERY original generic source
index t. Thus a usual generic extension of an arbitrary
finite increasing induced stage s automatically has colour c.
This includes the first nontrivial E5 table at n=2 and ALL
larger n. The same f supports arbitrarily high ENTIRE generic
copies of genuine compatible reserved IMMEDIATE successors.

Nothing asserts that every generic extension selected in c
admits a RESERVED q-horizon continuation for arbitrary q,
nor that a single new image persists through all horizons. -/
theorem RoleDiary.exists_first_leaf_all_horizon_good_colour_with_all_generic_finite_extensions
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
        HasGenericColourOnePointExtensions G
          (fun t : Nat =>
            DiaryLowerBoundColors.singletonColour K
              (oldStageTailCut H m f) (F t) = c) ∧
        (∀ M : Nat,
          ∃ J : Ordered3Graph.UnorderedEmbedding G.graph K,
            ∀ i : Nat,
              M < J i ∧
              IsLeaf K (J i) ∧
              (∃ t : Nat, J i = F t) ∧
              HasCompatibleReservedNextLeaf H K
                (fun t : Nat => F t) f m (J i)) := by
  classical
  obtain ⟨f,Pf,c,_hPalette,hColourAll,_hFinite,hAll,_hTail,hCones⟩ :=
    DH.exists_first_leaf_all_horizon_good_colour_and_whole_generic_successor_cones
      DK G F hFLeaf m hm hFirst
  refine ⟨f,Pf,c,hAll,?_,hCones⟩
  intro n s _hOldColour
  obtain ⟨hBound,hBits⟩ := s.newVertex_spec
  exact ⟨s.newVertex,hBound,
    hColourAll (F s.newVertex) (hFLeaf s.newVertex),hBits⟩

end DiaryLeafPriority
end ThreeUniformDiaries
